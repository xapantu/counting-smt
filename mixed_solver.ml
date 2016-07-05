module Mixed_solver (T: Theory_model.T) = 
  struct
    open T.Formula
           
    let rec solve_starting_from_model cards m =
      let open List in
      let im = T.new_interval_manager () in
      let constraints_cards =
        map (fun c ->
                c, T.expr_to_domain im m c.quantified_var c.expr) cards in
      T.implies_constraints im;
      iter (fun (c, d) ->
                T.implies_card im c.var_name d;
        ) constraints_cards;
      try
        T.solve_assuming im (fun m -> m)
      with
        | T.Unsat -> T.solve (solve_starting_from_model cards)

    let solve (formula:expr) (cards: card list) =
      T.solve_formula formula (solve_starting_from_model cards)


    let solve_context (cards: card list) =
      T.solve (solve_starting_from_model cards)

  end
