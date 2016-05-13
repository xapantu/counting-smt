open Formula

module type T = sig
  module Formula : F
  val check_consistent : Formula.litteral list -> bool
end

module LA_SMT  = struct

  type sort =
    | Int
    | Bool

  type expr =
    | And of expr * expr
    | Or of expr * expr
    | Greater of expr * expr
    | Equality of expr * expr
    | Value of int
    | Var of string

  type domain = int

  type texpr = expr
  type tdomain = domain

  module Formula = IFormula(struct
      type expr = texpr
      type domain = tdomain
    end)

  open Formula

  let solver_command = "yices-smt2 --incremental"

  let solver_in, solver_out = Unix.open_process solver_command

  let send_to_solver s =
    output_string solver_out s;
    (*print_endline s;*)
    output_string solver_out "\n";
    flush solver_out

  let () = send_to_solver "(set-logic QF_LIA)"

  let use_var name = function
    | Int -> send_to_solver @@ "(declare-fun " ^ name ^ " () Int)"
    | Bool -> send_to_solver @@ "(declare-fun " ^ name ^ " () Bool)"

  exception Unknown_answer of string

  let is_sat () =
    match input_line solver_in with
    | "sat" -> true
    | "unsat" -> false
    | a -> raise (Unknown_answer a)

  let check_consistent l =
    send_to_solver "(push 1)";
    List.iter (function
        | Lit a -> send_to_solver @@ "(assert " ^ a ^ ")"
        | NotLit a -> send_to_solver @@ "(assert (not " ^ a ^ "))"
        | Card(var, _, Some dom) -> send_to_solver @@ "(assert " ^ (domain_to_string dom var) ^ ")"
      ) l;
    send_to_solver "(check-sat)";
    send_to_solver "(pop 1)";
    is_sat ()

end
