open Smtlib
open Mixed_solver
open Theory_model


let _ =
  let verbose = ref false in
  (let open Arg in
   Arg.parse [
     "--verbose", Set verbose, "be verbose";
   ] (fun f ->
       ()) "basic smt solver, takes input from stdin");
  LA_SMT.set_verbose !verbose;
  runner stdout (lexing stdin) []
