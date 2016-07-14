open Mixed_solver
open Theory_model
open LA_SMT
open LA_SMT.Formula
open Arith_array_language
open Utils

module Solver = Mixed_solver(LA_SMT)
module Variable_manager = LA_SMT.Variable_manager
module Typing = Lisp_typechecking.Lisp_typechecking(Variable_manager)

type additional_defs = 
  | Card of Solver.constructed_variables
  | Def of Lisp.lisp

let fresh_var =
  let i = ref 0 in
  fun ?sort:(sort=Int) () ->
  (incr i; let n = "card!" ^ string_of_int !i
           in
           Variable_manager.use_var sort n; n)

exception Out
exception Not_allowed of string
exception Not_allowed_for_type of string * string
exception Type_not_allowed_for_counting of string
exception Forall_on_range

let range_to_string = function
  | Range(l) -> interval_to_string l
  | _ -> raise Forall_on_range
           
let ensure_int_expr l =
  match Typing.infer l with
  | Int | Range(_) -> ()
  | _ -> assert(false)

let load_lisp_from_string s = 
  Lisp_parser.prog Lisp_lexer.read (Lexing.from_string s)

let rec lisp_to_int_texpr ~z ctx =
  let open Lisp in
  function
  | Lisp_string(z) -> (Variable_manager.ensure_int z; IVar(z, 0))
  | Lisp_int (v) -> IValue v
  | Lisp_rec(Lisp_string "+" :: Lisp_string z :: Lisp_int i :: []) -> (Variable_manager.ensure_int z; IVar(z, i))
  | Lisp_rec(Lisp_string "-" :: Lisp_string z :: Lisp_int i :: []) -> (Variable_manager.ensure_int z; IVar(z, -i))
  | Lisp_rec(Lisp_string "+" :: Lisp_int i :: Lisp_string z :: []) -> (Variable_manager.ensure_int z; IVar(z, i))
  | Lisp_rec(Lisp_string "+" :: a :: b :: []) as e ->
    let subs = fresh_var () in
    ctx := (Def (Lisp_rec (Lisp_string "=" :: Lisp_string subs :: e :: []))) :: !ctx;
    ensure_int_expr a; ensure_int_expr b;
    IVar(subs, 0)
  | Lisp_rec(Lisp_string "-" :: a :: b :: []) as e ->
    let subs = fresh_var () in
    ctx := (Def (Lisp_rec (Lisp_string "=" :: Lisp_string subs :: e :: []))) :: !ctx;
    ensure_int_expr a; ensure_int_expr b;
    IVar(subs, 0)
  | Lisp_rec(Lisp_string "mod" :: q) ->
    failwith "The only supported syntax for mod is (= (mod z a) b) where a and b are constants."
  | a ->
    raise (Not_allowed_for_type (lisp_to_string a, "int"))

(** This function takes an expression and count how many times
 * the quantified variable (the first argument) appears. It also returns
 * an expression which is free of this variable. *)
let rec (extract_quantified_var: string -> Lisp.lisp -> int * Lisp.lisp) = fun z l ->
  let open Lisp in
  match l with
  | Lisp_string(_) | Lisp_false | Lisp_true | Lisp_int _ -> 0, l
  | Lisp_rec(Lisp_string "+" :: Lisp_string v :: b :: [] )
    when v = z->
    let n, b = extract_quantified_var z b in
    n+1, b
  | Lisp_rec(Lisp_string "+" :: b :: Lisp_string v :: [] )
    when v = z ->
    let n, b = extract_quantified_var z b in
    n+1, b
  | Lisp_rec(Lisp_string "-" :: b :: Lisp_string v :: [] )
    when v = z ->
    let n, b = extract_quantified_var z b in
    n-1, b
  | Lisp_rec(Lisp_string "-" :: Lisp_string v :: b :: [] )
    when v = z ->
    let n, b = extract_quantified_var z b in
    1-n, Lisp_rec (Lisp_string "-" :: Lisp_int 0 :: b :: [])
  | Lisp_rec(Lisp_string "-" :: a :: b :: [] ) ->
    let na, a = extract_quantified_var z a in
    let nb, b = extract_quantified_var z b in
    na - nb, Lisp_rec (Lisp_string "-" :: a :: b :: [])
  | Lisp_rec(Lisp_string "+" :: a :: b :: [] ) ->
    let na, a = extract_quantified_var z a in
    let nb, b = extract_quantified_var z b in
    na + nb, Lisp_rec (Lisp_string "+" :: a :: b :: [])
  | a ->
    raise (Not_allowed_for_type (lisp_to_string a, "int"))

(** z is the quantified variable name *)
let rec lisp_to_expr ?z:(z="") ctx l =
  let open Lisp in
  try
    match l with
    | Lisp_rec(Lisp_string "=>" :: a :: b :: []) ->
      Or (lisp_to_expr ~z ctx b, Not(lisp_to_expr ~z ctx a))
    | Lisp_rec(Lisp_string "and" :: a :: b :: []) ->
      And (lisp_to_expr ~z ctx a, lisp_to_expr ~z ctx b)
    | Lisp_rec(Lisp_string "not" :: a :: []) ->
      Not (lisp_to_expr ~z ctx a)
    | Lisp_rec(Lisp_string "and" :: a :: q) ->
      And (lisp_to_expr ~z ctx a, lisp_to_expr ~z ctx (Lisp_rec (Lisp_string "and" :: q)))
    | Lisp_rec(Lisp_string "or" :: a :: b :: []) ->
      Or (lisp_to_expr ~z ctx a, lisp_to_expr ~z ctx b)
    | Lisp_rec(Lisp_string "or" :: a :: q) ->
      Or (lisp_to_expr ~z ctx a, lisp_to_expr ~z ctx (Lisp_rec (Lisp_string "or" :: q)))
    | Lisp_rec(Lisp_string "select" :: a :: b :: []) ->
      Theory_expr (Bool (lisp_to_bool ~z ctx l))
    | Lisp_rec(Lisp_string ">=" :: a :: b :: []) when a = Lisp_string z || b = Lisp_string z ->
      Theory_expr (Greater (lisp_to_int_texpr ~z ctx a, lisp_to_int_texpr ~z ctx b))
    | Lisp_rec(Lisp_string ">=" :: a :: b :: []) ->
      let count_quantified_a, a = extract_quantified_var z a in
      let count_quantified_b, b = extract_quantified_var z b in
      let total_count = count_quantified_a - count_quantified_b in
      if total_count = 1 then
        let transformed_expr =
          Lisp_rec [Lisp_string ">="; Lisp_string z; Lisp_rec [Lisp_string "-"; b; a]] in
        lisp_to_expr ~z ctx transformed_expr
      else if total_count = -1 then
        let transformed_expr =
          Lisp_rec [Lisp_string ">="; Lisp_rec [Lisp_string "-"; a; b]; Lisp_string z] in
        lisp_to_expr ~z ctx transformed_expr
      else failwith "non unit coefficient in front of the quantified"
    | Lisp_rec(Lisp_string ">" :: a :: b :: []) ->
      let transformed_expr =
        Lisp_rec [Lisp_string ">="; Lisp_rec [Lisp_string "-"; a; Lisp_int 1]; b] in
      lisp_to_expr ~z ctx transformed_expr
    | Lisp_rec(Lisp_string "<" :: a :: b :: []) ->
      lisp_to_expr ~z ctx (Lisp_rec [Lisp_string ">"; b; a])
    | Lisp_rec(Lisp_string "<=" :: a :: b :: []) ->
      lisp_to_expr ~z ctx (Lisp_rec [Lisp_string ">="; b; a])
    | Lisp_rec (Lisp_string "=" :: (Lisp_rec (Lisp_string "mod" :: Lisp_string z' :: Lisp_int a :: [])) :: Lisp_int b :: [])
      when z' = z && a > b ->
      assert (a > 0);
      Theory_expr (Mod (IVar(z, 0), modp b a, a))
    | Lisp_rec(Lisp_string "=" :: a :: b :: []) ->
      let s = Typing.infer a in
      begin
        match s with
        | Int | Range(_, _) ->
          Theory_expr (IEquality (lisp_to_int_texpr ~z ctx a, lisp_to_int_texpr ~z ctx b))
        | Bool ->
          Theory_expr (BEquality (lisp_to_bool ~z ctx a, lisp_to_bool ~z ctx b))
        | _ -> assert(false)
      end
    | Lisp_true | Lisp_false | Lisp_string _ ->
      Theory_expr (Bool (lisp_to_bool ~z ctx l))
    | _ ->
      raise (Not_allowed (lisp_to_string l))
  with
  | TypeCheckingError(_) as e ->
    Format.eprintf "error while typechecking %s@." @@ lisp_to_string l;
    raise e
and lisp_to_array =
  let open Lisp in
  function
  | Lisp_string x ->
    Array_term(x, TBool)
  | l -> raise (Not_allowed_for_type (lisp_to_string l, "array"))
and lisp_to_bool ?z:(z="") ctx l =
  let open Lisp in
  match l with
  | Lisp_rec(Lisp_string "select" :: a :: b :: []) ->
     Array_access (lisp_to_array a, lisp_to_int_texpr ~z ctx b, true)
  | Lisp_string(z) -> (Variable_manager.ensure_bool z; BVar(z, true))
  | Lisp_rec(Lisp_string "not" :: a :: []) ->
    let a = lisp_to_bool ~z ctx a in
    apply_not a
  | Lisp_true -> BValue true
  | Lisp_false -> BValue false
  | _ ->
    raise (Not_allowed_for_type (lisp_to_string l, "bool"))

let rec extract_cards ?z:(z="") l =
  let open Lisp in
  match l with
    | Lisp_int _ | Lisp_string _ | Lisp_true | Lisp_false -> l, []
    (* Accept any reasonable number of parenthesis *)
    | Lisp_rec (Lisp_string "#" :: Lisp_string z :: Lisp_string sort :: formula :: [])
    | Lisp_rec (Lisp_string "#" :: Lisp_rec(Lisp_string z :: Lisp_string sort :: []) :: formula :: [])
    | Lisp_rec (Lisp_string "#" :: Lisp_rec(Lisp_rec (Lisp_string z :: Lisp_string sort :: []) :: []) :: formula :: []) ->
      let y = fresh_var () in
      let sort = match sort with
          | "Int" -> Int
          | "Bool" -> Bool
          | a ->
            try
              Variable_manager.get_range a
            with
            | Not_found -> raise (Type_not_allowed_for_counting a)
      in
      let ctx = ref [] in
      let formula = Variable_manager.use_quantified_var z sort (fun a ->
          let formula_extracted, defs_formula = extract_cards ~z:z formula in
          ctx := defs_formula;
          And(a, lisp_to_expr ~z ctx formula_extracted)) in
      Lisp_string (y), Card {var_name = y; construct = { expr = formula; quantified_var = z; quantified_sort = sort;} } :: !ctx
    | Lisp_rec (Lisp_string "select" :: a :: b :: [] ) when b <> Lisp_string z ->
      let a_extracted, defs_a = extract_cards a in
      let b_extracted, defs_b = extract_cards b in
      let array_sort = Typing.infer a_extracted in
      let element_sort = match array_sort with
        | Array(_, Bool) -> Bool
        | _ -> failwith "too complex array"
      in
      let y = fresh_var ~sort:element_sort () in
      let card_var = fresh_var () in
      let ctx = ref @@ defs_a @ defs_b in
      let formula = Variable_manager.use_quantified_var "z" Int (fun a ->
          let f =
            Format.sprintf "(and (= z %s) (= %s (select %s z)))"
              (lisp_to_string b_extracted)
              y
              (lisp_to_string a_extracted)
            |> load_lisp_from_string
            |> lisp_to_expr ctx
          in
          And(a, f) 
        )
      in
      Lisp_string y,
      Def (Lisp_rec [Lisp_string "="; Lisp_string card_var; Lisp_string "1"]) ::
      Card { var_name = card_var; construct = { expr = formula; quantified_var = "z"; quantified_sort = Int; } } ::
      !ctx
    | Lisp_rec (Lisp_string "store" :: a :: b :: c :: []) when b <> Lisp_string z ->
      let a_extracted, defs_a = extract_cards a in
      let b_extracted, defs_b = extract_cards b in
      let c_extracted, defs_c = extract_cards c in
      let array_sort = Typing.infer a_extracted in
      let array_size, index_sort = match array_sort with
        | Array((Range(Expr a, Expr b)) as index_sort, Bool) ->
          Lisp_rec [Lisp_string "-"; Lisp_string (term_to_string b); Lisp_string (term_to_string a)], index_sort
        | _ -> failwith "too complex array"
      in
      let result_of_store = fresh_var ~sort:array_sort () in
      let card_var = fresh_var () in
      let ctx = ref @@ defs_a @ defs_b @ defs_c in
      let formula = Variable_manager.use_quantified_var "z" index_sort (fun a ->
          let index = lisp_to_string b_extracted in
          let f =
            Format.sprintf "(or (and (= z %s) (= (select %s z) %s)) (and (not (= z %s)) (= (select %s z) (select %s z))))"
              index
              result_of_store
              (lisp_to_string c_extracted)
              index
              result_of_store
              (lisp_to_string a_extracted)
            |> load_lisp_from_string
            |> lisp_to_expr ctx
          in
          And(a, f)
        )
      in
      Lisp_string result_of_store,
      Def (Lisp_rec [Lisp_string "="; array_size; Lisp_string card_var]) ::
      Card { var_name = card_var;  construct = { expr=formula; quantified_var = "z"; quantified_sort = index_sort; } } ::
      !ctx
    | Lisp_rec (Lisp_string "forall" :: ((Lisp_rec (Lisp_rec (Lisp_string a :: Lisp_string b :: []) :: []) :: _) as q) ) ->
      extract_cards (Lisp_rec (Lisp_string "=" :: Lisp_string (range_to_string (Variable_manager.get_range b)) :: Lisp_rec (Lisp_string "#" :: q) :: []))
    | Lisp_rec(Lisp_string "=" :: a :: b :: []) ->
      let sort_a, sort_b = Typing.infer a, Typing.infer b in
      begin
        match sort_a, sort_b with
        | Array((Range(Expr l, Expr u)) as index_sort, _), Array(_) -> 
          let a_extracted, defs_a = extract_cards a in
          let b_extracted, defs_b = extract_cards b in
          let ctx = ref @@ defs_a @ defs_b in
          let array_size = Format.sprintf "(- %s %s)" (term_to_string u) (term_to_string l) in
          let formula = Variable_manager.use_quantified_var "z" index_sort (fun constraint_on_sort ->
              let f =
                Format.sprintf "(= (select %s z) (select %s z))"
                  (lisp_to_string a_extracted)
                  (lisp_to_string b_extracted)
                |> load_lisp_from_string
                |> lisp_to_expr ctx
              in
              And(constraint_on_sort, f)
            )
          in
          let card_var = fresh_var () in
          Lisp_rec [Lisp_string "=";Lisp_string card_var; Lisp_string array_size],
          Card { var_name = card_var; construct = { expr=formula; quantified_var = "z"; quantified_sort = index_sort; } }
          :: !ctx
        | e -> 
          let a_extracted, defs_a = extract_cards ~z a in
          let b_extracted, defs_b = extract_cards ~z b in
          Lisp_rec[Lisp_string "="; a_extracted; b_extracted], defs_a @ defs_b
      end
    | Lisp_rec (l) ->
      let l, cards = List.map (extract_cards ~z) l |> List.split in
      Lisp_rec (l), List.concat cards

let lexing = Lexing.from_channel

let rec runner stdout lexing_stdin cards' =
  let cards = ref cards' in
  try
    while true do
      let open Lisp in
      lexing_stdin
      |> Lisp_parser.prog Lisp_lexer.read
      |> (fun lisp ->
          match lisp with
            | Lisp_rec (Lisp_string "set-logic" :: _) | Lisp_rec (Lisp_string "set-info" :: _) ->
              lisp_to_string lisp
              |> LA_SMT.send_to_solver
            | Lisp_rec (Lisp_string "get-model" :: []) ->
              begin
                try
                  Solver.solve_context_get_model !cards |> LA_SMT.print_model
                with
                  | LA_SMT.Unsat -> Printf.fprintf stdout "unsat\n"
              end
            | Lisp_rec (Lisp_string "declare-fun" :: Lisp_string x :: Lisp_rec ([]) :: sort :: []) ->
              Variable_manager.use_var (Typing.to_sort sort) x
            | Lisp_rec (Lisp_string "declare-range" :: Lisp_string x :: Lisp_rec (a :: b :: []) :: []) ->
              let a = lisp_to_int_texpr ~z:"" (ref []) a in
              let b = lisp_to_int_texpr ~z:"" (ref []) b in
              Variable_manager.new_range x (Expr(a)) (Expr(b));
            | Lisp_rec (Lisp_string "push" :: Lisp_int 1 :: []) ->
              LA_SMT.push (fun () -> runner stdout lexing_stdin !cards)
            | Lisp_rec (Lisp_string "pop" :: Lisp_int 1 :: []) | Lisp_rec (Lisp_string "exit" :: []) ->
              raise Out
            | Lisp_rec (Lisp_string "assert" :: a :: []) ->
              begin
                let assertion_cardless, new_card_vars = extract_cards a in
                let new_vars, new_cards = List.partition (function
                    | Card _ -> false
                    | Def _ -> true) new_card_vars
                in
                let new_vars = List.map (function
                    | Card _ -> raise Not_found
                    | Def a -> a) new_vars
                in
                let new_cards = List.map (function
                    | Card a -> a
                    | Def _ -> raise Not_found) new_cards
                in
                Lisp_rec (Lisp_string "assert" :: Lisp_rec (Lisp_string "and" :: assertion_cardless :: new_vars) :: [])
                |> lisp_to_string
                |> send_to_solver;
                cards := new_cards @ !cards
              end
            | Lisp_rec (Lisp_string "check-sat" :: []) ->
              begin
                try
                  let _ = Solver.solve_context !cards in
                  Format.printf "sat@."
                with
                  | LA_SMT.Unsat -> Format.printf "unsat@."
              end
            | a -> raise (Not_allowed (lisp_to_string a))
         )
    done
  with
    | Out -> ()


