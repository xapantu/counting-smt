module Dpll_solver (T: Theory.T) = struct

  open T.Formula

  type result = Sat | Unsat

  let remove_litteral lit cnf =
    let open List in
    fold_left (fun acc clause ->
        if mem lit clause then
          acc
        else
          filter (fun l -> not @@ litteral_eq_neg l lit) clause :: acc) [] cnf

  (* cnf is assumed to contain no assumptions litteral *)
  let rec solve_with_assumptions assumptions cnf =
    let rec assume_and_solve cnf assumptions l =
      match l with
      | Card(s, e, None) ->
        compute_domain assumptions e (fun assumptions d ->
            assume_and_solve cnf assumptions (Card(s, e, Some d))
          )
      | _ ->
        let assumptions = (l :: assumptions) in
        if T.check_consistent assumptions then
          remove_litteral l cnf
          |> solve_with_assumptions assumptions
        else
          Unsat
    and
      (*assume l f g =
      let assumptions = (l :: assumptions) in
      if T.check_consistent assumptions && f () = Sat then
        Sat
      else
        let assumptions = (litteral_neg l :: assumptions) in
        if T.check_consistent assumptions && g () = Sat then
          Sat
        else Unsat
        and*)
      compute_domain a expr (cont: assumptions -> domain -> result) =
      match expr with
      | And(e1, e2) ->
        compute_domain a e1 (fun a d1 ->
            compute_domain a e2 (fun a d2 ->
                T.make_domain_intersection a d1 d2 cont
              )
          )
      | Or(e1, e2) ->
        compute_domain a e1 (fun a d1 ->
            compute_domain a e2 (fun a d2 ->
                T.make_domain_union a d1 d2 cont
              )
          )
      | Theory_expr(e) -> T.make_domain_from_expr a e cont
    in
    match cnf with
    | []::q -> Unsat
    | [l]::q ->
      assume_and_solve q assumptions l
    | (l::clause)::q ->
      let sat = assume_and_solve q assumptions l in
      if sat = Sat then
        Sat
      else
        assume_and_solve (clause::q) assumptions (litteral_neg l)
    | [] -> Sat

  let solve = solve_with_assumptions []

end
