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
    | Value of int
    | Var of string

  type rel =
    | Greater of expr * expr
    | Equality of expr * expr

  type bound =
    | Ninf
    | Pinf
    | Expr of expr

  type interval = bound * bound
  type domain = interval list

  exception Unknown_answer of string
  exception Cardinality_uncomputed
  exception Unbounded_interval

  let expr_to_string = function
    | Var s -> s
    | Value i -> string_of_int i

  let bound_to_string = function
    | Ninf | Pinf -> raise Unbounded_interval
    | Expr e -> expr_to_string e

  let interval_to_string (l, u) =
    bound_to_string u ^ " - " ^ bound_to_string l

  let domain_to_string dom =
    dom
    |> List.map interval_to_string
    |> String.concat "+"

  type tdomain = domain

  module Formula = IFormula(struct
      type texpr = rel
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
        | Card(var, _, Some dom) -> send_to_solver @@ "(assert (= " ^ var ^ " " ^ domain_to_string dom ^ ")"
        | Card(_) -> raise Cardinality_uncomputed
      ) l;
    send_to_solver "(check-sat)";
    send_to_solver "(pop 1)";
    is_sat ()

end
