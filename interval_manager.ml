open Array_solver
open Utils

include Arith_array_language

exception Bad_interval

type constraints = Array_solver.array_subdivision
type constrained_interval = Array_solver.array_subdivision * interval
type constrained_domain = constrained_interval list

class interval_manager = object(this)

  val mutable assumptions : rel list  = []
  val mutable ordering : int term list = []
                                          
  method assume a =
    (* first some dumb simplification *)
    let must_be_added =
      not(List.mem a assumptions) &&
      match a with
      | IEquality(a, b) -> a <> b
      | Greater(IVar(a,i), IVar(b, ib)) when a = b && i >= ib -> false
      | Greater(a, b) ->
        if List.mem(IEquality(a, b)) assumptions then
          false
            else if List.mem(IEquality(b, a)) assumptions then
          false
        else if List.mem (Greater(b, a)) assumptions then
          begin
            assumptions <- List.filter ((<>) (Greater(b, a))) assumptions;
            assumptions <- IEquality(a, b) :: assumptions;
            false
          end
        else
          true
      | _ -> true
    in
    if must_be_added then
      assumptions <- a :: assumptions
                    
  method print_ordering =
    List.iter (fun r ->
        Format.eprintf "%s@." (term_to_string r)) ordering

  method assumptions = assumptions

  method order oracle a =
    if not (List.mem a ordering) then
      let rec insert_into = function
        | [] -> [a]
        | t::q ->
          if oracle t a >= 0 then
            a :: t :: q
          else
            t :: insert_into q
      in
      ordering <- insert_into ordering

  method fix_ordering =
    let n = List.length ordering in
    List.iter (function
        | Greater(a, b) ->
          let rec real_order a b found = function
            | [] -> []
            | t::q ->
              if t = a then
                b::(real_order a b found q)
              else if t = b && found then
                a::q
              else if t = b then
                t::q
              else
                real_order a b found q
          in
          ordering <- real_order b a false ordering
        | _ -> ()) assumptions;
    assert(n = List.length ordering)

  method ordering =
    this#fix_ordering;
    ordering

  method get_slices_of_ordering (a, b) =
    this#fix_ordering;
    let rec find_aux a ind b = match b with
      | [] -> failwith (term_to_string a)
      | t::q ->
        if t = a then ind
        else find_aux a (ind + 1) q
    in
    let a, b =
    ( match a with
      | Ninf -> 0
      | Expr a -> find_aux a 1 ordering
      | Pinf -> failwith "pinf" )
  , ( match b with
      | Pinf -> List.length ordering + 1
      | Expr b -> find_aux b 1 ordering
      | Ninf -> raise Not_found )
    in
    (* sometimes terms are equal *)
    let a, b = min a b, max a b in
    let res = ref [] in
    for i = a to (b-1) do
      if i = 0 && List.length ordering = 0 then
        res := "inf!inf" :: !res
      else if i = 0 then
        res := ("inf!" ^ term_to_uid (List.nth ordering i)) :: !res
      else if i = List.length ordering then
        res := (term_to_uid (List.nth ordering (i-1)) ^ "!inf") :: !res
      else
        res := (term_to_uid (List.nth ordering (i-1)) ^ "!" ^ term_to_uid (List.nth ordering i)) :: !res
    done;
    !res

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
      (d2:constrained_domain)
    =
    let save_order = function
      | Expr a -> this#order oracle a
      | _ -> ()
    in
    (* >= *)
    let greater a b =
      save_order a; save_order b;
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
            (this#assume (Greater(b, plus_one a)); this#order oracle (plus_one a); false)
    in
    let equal a b =
      save_order a; save_order b;
      match a, b with
        | Ninf, Ninf -> true
        | Pinf, Pinf -> true
        | Expr a, Expr b ->
          let comp = oracle a b in
          if comp = 0 then
            (this#assume (IEquality(a, b)); true)
          else if comp  > 0 then
            (this#assume (Greater(a, plus_one b)); this#order oracle (plus_one b); false)
          else
            (this#assume (Greater(b, plus_one a)); this#order oracle (plus_one a); false)
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
