open Array_solver

include Arith_array_language

exception Bad_interval

type constraints = Array_solver.array_subdivision

class interval_manager = object
  val array_ctx : Array_solver.array_ctx option = None


  method unwrap_ctx =
    match array_ctx with
    | None -> failwith "uninitialized"
    | Some s -> s

  method domain_neg dom (negate_constraints:constraints -> constraints) empty_constraints is_sat_constraints =
    let rec domain_neg_aux old_bound dom =
      match dom with
      | (_, interv) :: q ->
        begin
          match interv with
          | (Ninf, Expr a) -> domain_neg_aux (Expr  a) q
          | (Expr a, Pinf) ->
            if Expr a = old_bound then
              []
            else
              let interv = (old_bound, Expr a) in
              [empty_constraints interv, interv]
          | (Expr a, Expr b) ->
            if Expr a = old_bound then
              domain_neg_aux (Expr b) q
            else
              let interv = (old_bound, Expr a) in
              (empty_constraints interv, interv) :: domain_neg_aux (Expr b) q
          | (Pinf, _) | (_, Ninf) -> raise Bad_interval
          | (Ninf, Pinf) -> []
        end

      | [] ->
        let interv = (old_bound, Pinf) in
        [empty_constraints interv, interv]
    in
    let dneg = domain_neg_aux Ninf dom
    in
    if dom = [] then dneg
    else
      let rec one_on_one l1 = function
        | t :: q ->t :: (one_on_one q l1)
        | [] -> l1 in
      let fin =
        let dom = List.map (fun (l, i) -> negate_constraints l, i) dom in
        match List.hd dom with
        | (_, (Ninf, _)) -> one_on_one dneg dom
        | _ -> one_on_one dom dneg
      in 
      fin
      |> List.filter (fun (l, i) -> is_sat_constraints l)

end

let i = new interval_manager
