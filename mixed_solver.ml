module Mixed_solver (T: Theories.T) = 
  struct
    type constructed_variables = { var_name: string; construct: T.construct; }

    (**
     * This function gets a model from the solver, then construct the values that are not
     * handled by the solver (counting counstraints, arrays, etc) under some assumptions
     * deduced with the model. Then it adds an implication (assumptions => counting = foo),
     * and asserts assumptions. Then, if it is sat, it returns sat, if it is unsat, it pops the
     * last assumptions assert, and ask for another model (which will NOT follow the last assumptions,
     * as it was unsat).
     **)
    let rec solve_starting_from_model cards (m:T.premodel) =
      let open List in
      let constraints_cards =
        map (fun c ->
                c, T.build_domain_for_construct m c.construct) cards in
      T.ensure_domains_consistency m (List.map snd constraints_cards);
      iter (fun (c, d) ->
                T.ensure_domain m c.var_name d;
        ) constraints_cards;
      try
        T.build_abstract_model m
      with
        | T.Unsat ->
          solve_starting_from_model cards (T.build_premodel ())
    
    let solve_context (cards: constructed_variables list) =
      solve_starting_from_model cards (T.build_premodel ())

    let solve_context_get_model a =
      solve_context a |> T.build_full_model

  end
