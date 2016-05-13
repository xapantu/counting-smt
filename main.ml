open Dpll_solver
open Theory.LA_SMT
open Theory.LA_SMT.Formula

module Solver = Dpll_solver(Theory.LA_SMT)

let () = Theory.LA_SMT.use_var "a" Bool
let () = Theory.LA_SMT.use_var "b" Bool
let () = Theory.LA_SMT.use_var "x" Int
let () = Theory.LA_SMT.use_var "y" Int

let _ =
  let open Solver in
  match solve [[Lit "a"];[NotLit "b"]] with
  | Sat -> print_endline "sat"
  | Unsat -> print_endline "unsat"


let _ =
  let open Solver in
  match Solver.solve [[Lit "(< x y)"];[NotLit "(> x y)"]] with
  | Sat -> print_endline "sat"
  | Unsat -> print_endline "unsat"


  let _ =
    let open Solver in
    match Solver.solve [[Lit "(< x y)"];[NotLit "(> y x)"]] with
    | Sat -> print_endline "sat"
    | Unsat -> print_endline "unsat"
