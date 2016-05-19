open Mixed_solver
open Theory_model
open LA_SMT
open LA_SMT.Formula

module Solver = Mixed_solver(LA_SMT)

let () = use_var "x" Int
let () = use_var "y" Int

let _ =
  let open Solver in
  try
    let m = solve (
        And(
          Theory_expr(Greater(Var("x",0), Var("y",0))),
          Theory_expr(Greater(Var("x",0), Value 0))
        )
      )
        [{var_name = "y"; expr = And(
             Theory_expr(
               Greater(Var ("x",0), Var("z",0))
             ),
             Theory_expr(Greater(Var ("z",0), Var("y",0))
                        )
           )
          }]
    in
    print_endline "sat";
    LA_SMT.print_model m;
  with
  | Unsat -> print_endline "unsat"


  let _ =
    let open Solver in
    try
      let m = solve (
          And(
            Theory_expr(Greater(Var("y",0), Var("x",1))),
            Theory_expr(Greater(Var("x",0), Value 0))
          )
        )
          [{var_name = "y"; expr = And(
               Theory_expr(
                 Greater(Var ("x",0), Var("z",0))
               ),
               Theory_expr(Greater(Var ("z",0), Var("y",0))
                          )
             )
            }]
      in
      print_endline "sat";
      LA_SMT.print_model m;
    with
    | Unsat -> print_endline "unsat"
(*
let _ =
  let open Solver in
  match Solver.solve [[Lit "(< x y)"];[NotLit "(> x y)"]] with
  | Sat -> print_endline "sat"
  | Unsat -> print_endline "unsat"


  let _ =
    let open Solver in
    match Solver.solve [[Lit "(< x y)"];[NotLit "(> y x)"]] with
    | Sat -> print_endline "sat"
    | Unsat -> print_endline "unsat"*)
