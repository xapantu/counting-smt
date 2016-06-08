open Array_solver

include Arith_array_language

exception Bad_interval

type constraints = Array_solver.array_subdivision
type constrained_interval = Array_solver.array_subdivision * interval
type constrained_domain = constrained_interval list


class interval_manager = object(this)

  val mutable assumptions : rel list  = []

  method assume a =
    assumptions <- a :: assumptions

  method assumptions = assumptions

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

  method interval_domain_inter
      (oracle_compare: int term -> int term -> int)
      (oracle_bool:bool term -> bool term -> bool)
      (intersect_constraints: constraints -> constraints -> constraints)
      ((arr, (l1, u1)): constrained_interval)
      (d2:constrained_domain) =
    (* >= *)
    let greater a b =
      match a, b with
      | _, Ninf -> true
      | Ninf, _ -> false
      | Pinf, _  -> true
      | _, Pinf  -> false
      | Expr a, Expr b ->
        let comp = oracle_compare a b in
        if comp >= 0 then
          (this#assume (Greater(a, b)); true)
        else
          (this#assume (Greater(b, plus_one a)); false)
    in
    let equal a b =
      match a, b with
      | Ninf, Ninf -> true
      | Pinf, Pinf -> true
      | Expr a, Expr b ->
        let comp = oracle_compare a b in
        if comp = 0 then
          (this#assume (IEquality(a, b)); true)
        else if comp  > 0 then
          (this#assume (Greater(a, plus_one b)); false)
        else
          (this#assume (Greater(b, plus_one a)); false)
      | _ -> false
    in
    let rec extract_inter = function
      | [] -> []
      | (arrays, (l, u))::q ->
        let intersect_arrays = intersect_constraints arr arrays in
        if greater l u1 then
          if equal l u1 then
            [intersect_arrays, (l, u1)]
          else
            []
        else if greater l l1 then
          if greater u u1 then
            (intersect_arrays, (l, u1))::extract_inter q
          else
            (intersect_arrays, (l, u))::extract_inter q
        else if greater u l1 then
          if greater u u1 then
            (intersect_arrays, (l1, u1))::extract_inter q
          else
            (intersect_arrays, (l1, u))::extract_inter q
        else
          extract_inter q
    in
    extract_inter d2
    
  method make_domain_intersection oracle_int oracle_bool intersect_constraints d1 d2 =
    let do_inter = this#interval_domain_inter oracle_int oracle_bool intersect_constraints in
    let self = this#make_domain_intersection oracle_int oracle_bool intersect_constraints in
    match d1 with
    | [] -> []
    | t1::q1 ->
      do_inter t1 d2 @ self q1 d2



end

let i = new interval_manager
