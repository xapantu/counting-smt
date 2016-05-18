module Mixed_solver (T: Theory_model.T) = struct
  open T.Formula

  let solve (formula:expr) (cards: card list) =
    let rec solve_aux m =
      let open List in
      let all_assumptions =
        cards
        |> map (fun c ->
            let (d, assumptions) = T.expr_to_domain m c.expr in
            T.implies_card assumptions c.var_name d;
            assumptions
          )
        |> concat
      in
      try
        T.solve_assuming all_assumptions (fun m -> m)
      with
      | T.Unsat -> T.solve solve_aux
    in
    T.solve_formula formula solve_aux


  let solve_context (cards: card list) =
    let rec solve_aux m =
      let open List in
      let all_assumptions =
        cards
        |> map (fun c ->
            let (d, assumptions) = T.expr_to_domain m c.expr in
            T.implies_card assumptions c.var_name d;
            assumptions
          )
        |> concat
      in
      try
        T.solve_assuming all_assumptions (fun m -> m)
      with
      | T.Unsat -> T.solve solve_aux
    in
    T.solve solve_aux

end
