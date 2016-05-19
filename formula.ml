module type F = sig

  type texpr

  type expr =
    | And of expr * expr
    | Or of expr * expr
    | Theory_expr of texpr
    | Not of expr

  type assumptions = texpr list

  type card = { var_name: string; expr: expr; quantified_var: string; }

end

module IFormula (T : sig
    type texpr
    val texpr_to_smt: texpr -> string
  end) = struct

  type texpr = T.texpr

  type expr =
    | And of expr * expr
    | Or of expr * expr
    | Theory_expr of texpr
    | Not of expr


    type assumptions = texpr list

    type card = { var_name: string; expr: expr; quantified_var: string; }

    let rec expr_to_smt = function
      | And(e1, e2) -> "(and " ^ expr_to_smt e1 ^ " " ^ expr_to_smt e2 ^ ")"
      | Or(e1, e2) -> "(or " ^ expr_to_smt e1 ^ " " ^ expr_to_smt e2 ^ ")"
      | Not(e) -> Format.sprintf "(not %s)" @@ expr_to_smt e
      | Theory_expr(t) -> T.texpr_to_smt t

    let assumptions_to_smt l =
      if l = [] then "true"
      else
      "(and " ^
      (
        l |> List.map T.texpr_to_smt
        |> String.concat " ")
      ^ ")"

end
