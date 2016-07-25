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

let iff a b =
  let open Lisp in
  Lisp_rec [Lisp_string "or"; Lisp_rec [Lisp_string "and"; a; b]; Lisp_rec [Lisp_string "and"; Lisp_rec [Lisp_string "not"; a;]; Lisp_rec [Lisp_string "not"; b]]]

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
      Theory_expr (lisp_to_bool ~z ctx l)
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
          Theory_expr (int_equality (lisp_to_int_texpr ~z ctx a) (lisp_to_int_texpr ~z ctx b))
        | Bool ->
          Theory_expr (bool_equality (lisp_to_bool ~z ctx a) (lisp_to_bool ~z ctx b))
        | _ -> assert(false)
      end
    | Lisp_true | Lisp_false | Lisp_string _ ->
      Theory_expr (lisp_to_bool ~z ctx l)
    | _ ->
      raise (Not_allowed (lisp_to_string l))
  with
  | TypeCheckingError(_) as e ->
    Format.eprintf "error while typechecking %s@." @@ lisp_to_string l;
    raise e
and lisp_to_array ctx =
  let open Lisp in
  function
  | Lisp_string x ->
    Array_term(x, TBool)
  | Lisp_rec (Lisp_string "store" :: a :: b :: c :: []) ->
    let a = lisp_to_array ctx a in
    let b = lisp_to_int_texpr ctx b ~z:"" in
    let c = lisp_to_bool ctx c in
    Array_store(a, b, c)
  | Lisp_rec (Lisp_rec (Lisp_string "as" :: _) :: _) -> Array_term("", TBool)
  | l -> raise (Not_allowed_for_type (lisp_to_string l, "array"))
and lisp_to_bool ?z:(z="") ctx l =
  let open Lisp in
  match l with
  | Lisp_rec(Lisp_string "select" :: a :: b :: []) ->
     Array_access (lisp_to_array ctx a, lisp_to_int_texpr ~z ctx b, true)
  | Lisp_string(z) -> (Variable_manager.ensure_bool z; BVar(z, true))
  | Lisp_rec(Lisp_string "not" :: a :: []) ->
    let a = lisp_to_bool ~z ctx a in
    not_term a
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
      let open Solver in
      Lisp_string (y), Card {var_name = y; construct = { expr = formula; quantified_var = z; quantified_sort = sort;} } :: !ctx
    | Lisp_rec (Lisp_string "forall" :: ((Lisp_rec (Lisp_rec (Lisp_string a :: Lisp_string b :: []) :: []) :: _) as q) ) ->
      extract_cards (Lisp_rec (Lisp_string "=" :: Lisp_string (range_to_string (Variable_manager.get_range b)) :: Lisp_rec (Lisp_string "#" :: q) :: []))
    | Lisp_rec(Lisp_string "=" :: a :: b :: []) ->
      let sort_a, sort_b = Typing.infer a, Typing.infer b in
      begin
        match sort_a, sort_b with
        | Array((Range(Expr l, Expr u)), _), Array(_) -> 
          let a_extracted, defs_a = extract_cards a in
          let b_extracted, defs_b = extract_cards b in
          let ctx = ref @@ defs_a @ defs_b in
          begin
            let a, b = lisp_to_array ctx a_extracted, lisp_to_array ctx b_extracted in
            let rel = Array_bool_equality(ExtEquality(a, b)) in
            let v = Variable_manager.use_var_for_rel rel in
            ctx := Def( iff (Lisp_rec[Lisp_string "="; a_extracted; b_extracted]) (Lisp_string v.name)) :: !ctx;
            Lisp_rec[Lisp_string "="; a_extracted; b_extracted], !ctx
          end
        | e -> 
          let a_extracted, defs_a = extract_cards ~z a in
          let b_extracted, defs_b = extract_cards ~z b in
          Lisp_rec[Lisp_string "="; a_extracted; b_extracted], defs_a @ defs_b
      end
    | Lisp_rec (l) ->
      let l, cards = List.map (extract_cards ~z) l |> List.split in
      Lisp_rec (l), List.concat cards

let rec extract_array_terms l =
  let open Lisp in
  match l with
  | Lisp_string _ | Lisp_int _ | Lisp_true | Lisp_false -> []
  | Lisp_rec (Lisp_string "select" :: a :: b :: []) ->
    let l = (List.map extract_array_terms [a; b]) |> List.concat in
    b :: l
  | Lisp_rec (Lisp_string "store" :: a :: b :: c :: []) ->
    let l = (List.map extract_array_terms [a; b;c]) |> List.concat in
    b :: l
  | Lisp_rec ((Lisp_string "#" | Lisp_string "forall") ::
              (
                (Lisp_string z :: Lisp_string sort :: formula :: []) |
                (Lisp_rec(Lisp_string z :: Lisp_string sort :: []) :: formula :: []) |
                (Lisp_rec(Lisp_rec(Lisp_string z :: Lisp_string sort :: [])::[]) :: formula :: [])
              )) ->
    extract_array_terms formula  |> List.filter ((<>) (Lisp_string z))
  | Lisp_rec (l) ->
    List.map extract_array_terms l |> List.concat

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
                extract_array_terms a
                |> List.map (lisp_to_int_texpr (ref []) ~z:"")
                |> List.iter LA_SMT.Array_solver.save_array_index;
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
                LA_SMT.flush_formulae ();
                List.iter (fun lisp ->
                    Lisp_rec [Lisp_string "assert"; lisp]
                    |> lisp_to_string
                    |> send_to_solver;
                  ) (assertion_cardless :: new_vars);

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


