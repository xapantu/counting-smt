open Mixed_solver
open Theory_model
open LA_SMT
open LA_SMT.Formula

module Solver = Mixed_solver(LA_SMT)

let fresh_var =
  let i = ref 0 in
  fun () ->
    (incr i; let n = "card!" ^ string_of_int !i
     in
     LA_SMT.use_var n Int; n)

exception Out
exception Not_allowed of string

let rec lisp_to_bool_texpr =
  let open Lisp in
  function
  | Lisp_true -> BValue true
  | Lisp_false -> BValue false
  | Lisp_string(z) -> (ensure_bool z; BVar(z, true))

let rec lisp_to_int_texpr =
  let open Lisp in
  function
  | Lisp_string(z) -> (ensure_int z; IVar(z, 0))
  | Lisp_int (v) -> IValue v
  | Lisp_rec(Lisp_string "+" :: Lisp_string z :: Lisp_int i :: []) -> (ensure_int z; IVar(z, i))
  | Lisp_rec(Lisp_string "-" :: Lisp_string z :: Lisp_int i :: []) -> (ensure_int z; IVar(z, -i))
  | Lisp_rec(Lisp_string "+" :: Lisp_int i :: Lisp_string z :: []) -> (ensure_int z; IVar(z, i))
  | a -> raise (Not_allowed (lisp_to_string a))

let rec lisp_to_expr l =
  let open Lisp in
  match l with
  | Lisp_rec(Lisp_string "and" :: a :: b :: []) -> And (lisp_to_expr a, lisp_to_expr b)
  | Lisp_rec(Lisp_string "and" :: a :: q) -> And (lisp_to_expr a, lisp_to_expr (Lisp_rec (Lisp_string "and" :: q)))
  | Lisp_rec(Lisp_string "or" :: a :: b :: []) -> Or (lisp_to_expr a, lisp_to_expr b)
  | Lisp_rec(Lisp_string "or" :: a :: q) -> Or (lisp_to_expr a, lisp_to_expr (Lisp_rec (Lisp_string "or" :: q)))
  | Lisp_rec(Lisp_string ">=" :: a :: b :: []) -> Theory_expr (Greater (lisp_to_int_texpr a, lisp_to_int_texpr b))
  | Lisp_rec(Lisp_string "=" :: a :: b :: []) -> Theory_expr (Greater (lisp_to_int_texpr a, lisp_to_int_texpr b))
  | Lisp_true -> Theory_expr (Bool (BValue true))
  | Lisp_false -> Theory_expr (Bool (BValue false))
  | Lisp_string b -> Theory_expr (Bool (BVar(b, true)))
  | _ -> raise (Not_allowed (lisp_to_string l))

let rec extract_cards l =
  let open Lisp in
  match l with
  | Lisp_int _ | Lisp_string _ | Lisp_true | Lisp_false -> l, []
  | Lisp_rec (Lisp_string "#" :: Lisp_string z :: formula :: []) ->
    let y = fresh_var () in
    let formula = use_quantified_var z (fun () -> lisp_to_expr formula) Int in
    Lisp_string (y), [{var_name = y; expr = formula; quantified_var = z}]
  | Lisp_rec (l) ->
    let l, cards = List.map extract_cards l |> List.split in
    Lisp_rec (l), List.concat cards

let rec runner cards' =
  let cards = ref cards' in
  try
    while true do
      let lisp = stdin
                 |> Lexing.from_channel
                 |> Lisp_parser.prog Lisp_lexer.read in
      let open Lisp in
      match lisp with
      | Lisp_rec (Lisp_string "set-logic" :: _) ->
        lisp_to_string lisp
        |> LA_SMT.send_to_solver
      | Lisp_rec (Lisp_string "get-model" :: []) ->
        begin
          try
            Solver.solve_context !cards  |> LA_SMT.print_model
          with
          | LA_SMT.Unsat -> print_endline "unsat"
        end
      | Lisp_rec (Lisp_string "declare-fun" :: Lisp_string x :: Lisp_rec ([]) :: Lisp_string "Int" :: []) ->
        LA_SMT.use_var x Int
      | Lisp_rec (Lisp_string "declare-fun" :: Lisp_string x :: Lisp_rec ([]) :: Lisp_string "Bool" :: []) ->
        LA_SMT.use_var x Bool
      | Lisp_rec (Lisp_string "push" :: Lisp_int 1 :: []) ->
        LA_SMT.push (fun () -> runner !cards)
      | Lisp_rec (Lisp_string "pop" :: Lisp_int 1 :: []) ->
        raise Out
      | Lisp_rec (Lisp_string "assert" :: a :: []) ->
        begin
          let assertion_cardless, new_cards = extract_cards a in
          Lisp_rec (Lisp_string "assert" :: assertion_cardless :: [])
          |> lisp_to_string
          |> send_to_solver;
          cards := new_cards @ !cards
        end
      | Lisp_rec (Lisp_string "check-sat" :: []) ->
        begin
          try
            let _ = Solver.solve_context !cards in
            print_endline "sat"
          with
          | LA_SMT.Unsat -> print_endline "unsat"
        end
      | a -> raise (Not_allowed (lisp_to_string a))
    done
  with
  | Out -> ()


let _ =
  let verbose = ref false in
  (let open Arg in
   Arg.parse [
     "--verbose", Set verbose, "be verbose";
   ] (fun f ->
       ()) "basic smt solver, takes input from stdin");
  LA_SMT.set_verbose !verbose;
  runner []
