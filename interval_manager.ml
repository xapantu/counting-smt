open Array_solver
open Utils

include Arith_array_language

exception Bad_interval

module Interval_manager(Constraints: sig
    type constraints
  end) = struct
type congruence = int * (int list)
type constraints = Constraints.constraints
type constrained_interval = constraints * interval
type constrained_domain = constrained_interval list

class interval_manager = object(this)

  val mutable assumptions : bool term list  = []
  val mutable ordering : int term list list = []
                                          
  method assume a =
    (* first some dumb simplification *)
    let must_be_added =
      not(List.mem a assumptions) &&
      match a with
      | Int_equality(Equality(a, b)) -> (not (List.mem (int_equality b a) assumptions)) &&  a <> b
      | Greater(a, b) ->
        if List.mem(int_equality a b) assumptions then
          false
        else if List.mem(int_equality b a) assumptions then
          false
        else if List.mem (Greater(b, a)) assumptions then
          begin
            assumptions <- List.filter ((<>) (Greater(b, a))) assumptions;
            assumptions <- int_equality a b :: assumptions;
            false
          end
        else
          true
      | _ -> true
    in
    if must_be_added then
      assumptions <- a :: assumptions
                    
  method print_assumptions =
    List.iter (fun l ->
        Format.eprintf "%s@." (term_to_string l)) assumptions

  method print_ordering =
    List.iter (fun l ->
        List.map term_to_string l |> String.concat " " |> Format.eprintf "(%s)@.";
      ) ordering

  method assumptions = assumptions

  method order oracle a =
    assert (List.fold_left (fun l a -> l && List.length a = 1) true ordering);
    let my_ordering = List.map List.hd ordering in
    if not (List.mem a my_ordering) then
      let rec insert_into = function
        | [] -> [a]
        | t::q ->
          if oracle t a >= 0 then
            a :: t :: q
          else
            t :: insert_into q
      in
      ordering <- List.map (fun a -> [a]) (insert_into my_ordering)

  method add_to_ordering (is_top:constraints -> bool) oracle domain =
    let save_order = function
      | Expr a -> this#order oracle a
      | _ -> ()
    in
    List.iter (fun (a, (l, u)) ->
        if not (is_top a) then
          (save_order l; save_order u;)) domain

  method merge_ordering =
    (* now merge every equal terms into a single class *)
    List.iter (function
        | Int_equality(Equality(a, b)) ->
          (* needs a good union_find structure *)
          let class_a = List.find (List.mem a) ordering in
          let class_b = List.find (List.mem b) ordering in

          if class_a <> class_b then
            begin
              ordering <- List.filter ((<>) class_a) ordering;
              ordering <- List.map (fun c ->
                  if c = class_b then
                    class_a @ class_b
                  else
                    c) ordering
            end
        | _ -> ()) assumptions

  method fix_ordering oracle =
    assert (List.fold_left (fun l a -> l && List.length a = 1) true ordering);
    List.iter (function
        | Greater(a, b) | Int_equality(Equality(a, b)) -> this#order oracle a; this#order oracle b
        | _ -> ()) assumptions;
    assert (List.fold_left (fun l a -> l && List.length a = 1) true ordering);
    List.iter (function
        | Greater(a, b) ->
          let a = [a] and b = [b] in
          let index_of l a =
            let rec index_of_aux i = function
              | [] -> raise Not_found
              | t::q -> if a = t then i else index_of_aux (i+1) q
            in
            index_of_aux 0 l
          in
          let ai = index_of ordering a in
          let bi = index_of ordering b in
          if ai < bi then
            ordering <- List.map (fun r -> if r = a then b else if r = b then a else r) ordering;
        | _ -> ()) assumptions;
    assert (List.fold_left (fun l a -> l && List.length a = 1) true ordering);
    this#merge_ordering;
    (* Now check that the assumptions actually enforce the ordering *)
    let rec check_enough_assumptions = function
      | [] | _::[] -> ()
      | t::q'::q ->
        check_enough_assumptions (q'::q);
        let assumed =
          List.fold_left 
            (fun f t ->
               f || List.fold_left (fun found elt ->
            found || List.mem (Greater(elt, t)) this#assumptions) false q') false t in
        if not assumed then
          let a = List.hd q' and b = List.hd t in
          let c = oracle a b in
          if c > 0 then
            this#assume (Greater(a, b))
          else if c = 0 then
            this#assume (int_equality a b)
          else
            assert false
    in
    check_enough_assumptions ordering;
    this#merge_ordering;
    assert (List.fold_left (fun l a -> l && List.length a >= 1) true ordering)
          
  method ordering =
    ordering

  method get_slices_of_ordering (a, b) =
    assert (List.fold_left (fun l a -> l && List.length a >= 1) true ordering);
    let open List in
    let rec find_aux a ind b = match b with
      | [] -> failwith (term_to_string a)
      | t::q ->
        if mem a t then ind
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
        res := ("inf!" ^ term_to_uid (hd @@ List.nth ordering i)) :: !res
      else if i = List.length ordering then
        res := (term_to_uid (hd @@ List.nth ordering (i-1)) ^ "!inf") :: !res
      else
        res := (term_to_uid (hd @@ List.nth ordering (i-1)) ^ "!" ^ term_to_uid (hd @@ List.nth ordering i)) :: !res
    done;
    !res
  
  method assume_oracle oracle a =
    (match a with
    | Greater (a, b)
    | Int_equality(Equality(a, b)) -> this#order oracle a; this#order oracle b;
    | _ -> (););
    this#assume a

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
    let greater a b =
      match a, b with
        | _, Ninf -> 1
        | Ninf, _ -> -1
        | Pinf, _  -> 1
        | _, Pinf  -> -1
        | Expr a, Expr b ->
          let c = oracle a b in
          c
    in
    let assume_greater a b =
      match a, b with
        | _, Ninf | Ninf, _ | Pinf, _  | _, Pinf  -> ()
        | Expr a, Expr b ->
          let c = oracle a b in
          if c > 0 then
            this#assume (Greater (a, b))
          else if c = 0 then
            this#assume (int_equality a b)
          else
            assert false

    in
    let rec extract_inter = function
      | [] -> []
      | (arrays, (l, u))::q ->
        let intersect_arrays = intersect_constraints arr arrays in
        (* the first two case mean that there is no intersection *)
        if greater l u1 > 0 then
            (assume_greater l u1; [])
        else if greater  l1 u > 0 then
            (assume_greater l1 u; extract_inter q)
        else (* so, there is an intersection here *)
          begin
            assume_greater u1 l; assume_greater u l1;
            let bound_inf =
              if greater l l1 >= 0 then 
                (assume_greater l l1; l)
              else
                (assume_greater l1 l; l1)
            in
            let bound_sup =
              if greater u u1 >= 0 then
                (assume_greater u u1; u1)
              else
                (assume_greater u1 u; u)
            in
            assume_greater bound_sup bound_inf;
            (intersect_arrays, (bound_inf, bound_sup)) :: extract_inter q
          end
    in
    extract_inter d2
                  
  method intersection_domains oracle intersect_constraints d1 d2 =
    let do_inter = this#intersection_interval_domain oracle intersect_constraints in
    List.fold_right (fun constrained_interval l -> do_inter constrained_interval d2 @ l) d1 []

end
end
