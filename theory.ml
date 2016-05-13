open Formula

module type T = sig
  val check_consistent : litteral list -> bool
end

module LA_SMT  = struct

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
      ) l;
    send_to_solver "(check-sat)";
    send_to_solver "(pop 1)";
    is_sat ()

end
