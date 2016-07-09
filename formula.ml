module type F = sig

  type texpr

  type sort

  type expr =
    | And of expr * expr
    | Or of expr * expr
    | Theory_expr of texpr
    | Not of expr

  type assumptions = texpr list

end

module IFormula (T : sig
    type texpr
    type tsort
    val texpr_to_smt: texpr -> string
  end) = struct

  type texpr = T.texpr
  type sort = T.tsort

  type expr =
    | And of expr * expr
    | Or of expr * expr
    | Theory_expr of texpr
    | Not of expr


    type assumptions = texpr list

    type card = { var_name: string; expr: expr; quantified_var: string; quantified_sort: sort; }

    let rec expr_to_smt = function
      | And(e1, e2) ->
        let e1' = and_to_smt e1 in
        let e2' = and_to_smt e2 in
        if e1' = "true" then expr_to_smt e2
        else if e2' = "true" then expr_to_smt e1
        else Format.sprintf "(and %s %s)" e1' e2'
      | Or(e1, e2) ->
        let e1 = or_to_smt e1 in
        let e2 = or_to_smt e2 in
        if e1 = "false" then e2
        else if e2 = "false" then e1
        else Format.sprintf "(or %s %s)" e1 e2
      | Not(e) -> Format.sprintf "(not %s)" @@ expr_to_smt e
      | Theory_expr(t) -> T.texpr_to_smt t
    and and_to_smt = function
      | And(e1, e2) ->
        let e1 = and_to_smt e1
        and e2 = and_to_smt e2 in
        if e1 = "true" then e2
        else if e2 = "true" then e1
        else Format.sprintf "%s %s" e1 e2
      | a -> expr_to_smt a
    and or_to_smt = function
      | Or(e1, e2) ->
        let e1 = or_to_smt e1
        and e2 = or_to_smt e2 in
        if e1 = "false" then e2
        else if e2 = "false" then e1
        else Format.sprintf "%s %s" e1 e2
      | a -> expr_to_smt a

end
