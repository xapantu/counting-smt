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
    let assume_and_solve l cnf =
      let assumptions = (l :: assumptions) in
      if T.check_consistent assumptions then
        remove_litteral l cnf
        |> solve_with_assumptions assumptions
      else
        Unsat
    in
    match cnf with
    | []::q -> Unsat
    | [l]::q ->
      assume_and_solve l q
    | (l::clause)::q ->
      let sat = assume_and_solve l q in
      if sat = Sat then
        Sat
      else
        assume_and_solve (litteral_neg l) (clause::q)
    | [] -> Sat

  let solve = solve_with_assumptions []

end
