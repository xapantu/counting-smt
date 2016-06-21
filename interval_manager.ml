open Array_solver
open Utils

include Arith_array_language

exception Bad_interval

type constraints = Array_solver.array_subdivision
type constrained_interval = Array_solver.array_subdivision * interval
type constrained_domain = constrained_interval list

class interval_manager = object(this)

  val array_ctx : Array_solver.array_ctx option = None
                                                    
  val mutable assumptions : rel list  = []
                                          
  method assume a =
    assumptions <- a :: assumptions

  method assumptions = assumptions

  method complementary_domain dom (negate_constraints:constraints -> constraints) empty_constraints is_full_constraints =
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
        | t :: q -> t :: (one_on_one q l1)
        | [] -> l1 in
      let fin =
        let dom = List.map (fun (l, i) ->
            if is_full_constraints l then
              None
            else
              Some (negate_constraints l, i)) dom in
        let dneg = List.map (fun l -> Some l) dneg in
        (match List.hd dom with
        | Some (_, (Ninf, _)) -> one_on_one dneg dom
        | _ -> one_on_one dom dneg)
        |> List.filter (fun l -> l <> None)
        |> List.map unwrap
      in
      fin

  method intersection_interval_domain
      (oracle:'a term -> 'a term -> int)
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
          let comp = oracle a b in
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
          let comp = oracle a b in
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
                  
  method intersection_domains oracle intersect_constraints d1 d2 =
    let do_inter = this#intersection_interval_domain oracle intersect_constraints in
    List.fold_right (fun constrained_interval l -> do_inter constrained_interval d2 @ l) d1 []

end
