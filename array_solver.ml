open Utils
open Arith_array_language
open Lisp

module Array_solver(S: sig
    module V:Variable_manager.VM
    module F: Formula.F with type texpr = bool Arith_array_language.term
    type a
    val equality_to_rel: a array equality -> bool term
  end) = struct
  
  type a = S.a
  open S.F

  module StrSet = Set.Make (struct type t = a array term
      let compare = compare end)

  module IntSet = Set.Make (struct
      type t = int term
      let compare = compare
    end)

  exception Unsat

  let declare_variable var =
    match var.sort with
        | Array(_, _) -> ()
        | _ -> ()

  type context = (a array term, a array term * StrSet.t) Hashtbl.t

  let implies = ref IntSet.empty

  let ensure_class (ctx:context) a =
    if not (Hashtbl.mem ctx a) then
      Hashtbl.add ctx a (a, StrSet.singleton a)

  let get_class (ctx:context) a =
    try
      Hashtbl.find ctx a
    with
    | Not_found -> failwith "couldn't find array class - should not happen"

  let merge_class (ctx:context) a b =
    ensure_class ctx a;
    ensure_class ctx b;
    let repr_a, class_a = Hashtbl.find ctx a in
    let repr_b, class_b = Hashtbl.find ctx b in
    let class_total = StrSet.union class_a class_b in
    let store, others = StrSet.partition (function
        | Array_store(_) -> true
        | _ -> false) class_total in
    let c = StrSet.cardinal store in
    if c = 0 then
      let fusion = (match repr_a with | Array_term("", _) -> repr_b | _ -> repr_a), class_total in
      let () = StrSet.iter (fun a ->
          Hashtbl.add ctx a fusion) class_total in
      true
    else if c = 1 then
      match StrSet.choose store with
      | (Array_store(a, _, _)) as e ->
        if StrSet.mem a others then false
        else
          let fusion = e, class_total in
          let () = StrSet.iter (fun a ->
              Hashtbl.add ctx a fusion) class_total in
          true
      | _ -> assert false
    else false

  let ensure_distinct_class ctx a b =
    ensure_class ctx a;
    ensure_class ctx b;
    Hashtbl.find ctx a <> Hashtbl.find ctx b

  let rec get_array_at: context -> a array term -> int term -> bool -> a term = fun context myarray index neg ->
    ensure_class context myarray;
    let (repr, _) = get_class context myarray in
    match repr with
    | Array_store(a, b, c) ->
      let a = get_array_at context a index neg in
      Ite(Int_equality(Equality(b, index)), c, a)
    | Array_term(_) ->
      Array_access(repr, index, neg)
    | Ite(_) | Array_access(_) -> failwith "nested arrays not supported"

  (* Record the equalities between the arrays, might raise Unsat at some point *)
  let context_from_equality: a array equality list -> (bool term -> bool) -> (context * (a array term * a array term * bool) list) = fun equalities_array oracle ->
    let context = Hashtbl.create 10 in
    context, List.fold_left (fun disequalities eq ->
        match eq with
        | AEquality(Array_term(a, sa), Array_term(b, sb)) ->
          if oracle (S.equality_to_rel eq) then
            ignore (merge_class context (Array_term(a, sa)) (Array_term(b, sb)));
          disequalities
        | ExtEquality(a, b) ->
          if oracle (S.equality_to_rel eq) then
            if merge_class context a b then
              disequalities
            else
              (a, b, true) :: disequalities
          else
            begin
              if ensure_distinct_class context a b  then
                (a, b, false) :: disequalities
              else
                raise Unsat
            end
        | AEquality(a, b) |  NoEquality(a, b) | Equality(a, b) -> (a, b, oracle (S.equality_to_rel eq)) :: disequalities
      ) [] equalities_array

  (* Place every array terms between the bounds. It returns a which is formed by bounds
   * and term that are immediately (that is, before any other bound) greater than a
   * particular bound. *)
  let place_array_terms: (bool term -> bool) -> (bool term -> unit) -> bound list -> (bound * int term list list) list = fun oracle assume bounds ->
    (* merge classes *)
    let elts =
      IntSet.elements !implies
      |> List.sort (fun a b ->
          if oracle (Int_equality(Equality(a, b))) then 0
          else if oracle (Greater(a, b)) then 1
          else -1)
      |> List.fold_left (fun l a ->
          match l with
          | [] -> [[a]]
          | t::q ->
            let repr = List.hd t in
            if oracle (Int_equality(Equality(a, repr))) then
              (a::t)::q
            else
              [a]::l
        ) []
    in
    assert (List.map List.length elts |> List.fold_left (+) 0 = List.length (IntSet.elements !implies));
    let elts_number = List.length (IntSet.elements !implies) in
    match bounds with
    | Ninf::q ->
      let _, _, l = List.fold_left (fun (elts, last_bound, l) n ->
          assert ((List.map snd l |> List.map (fun l -> List.map List.length l |> List.fold_left (+) 0) |> List.fold_left (+) 0) + (List.map List.length elts  |> List.fold_left (+) 0) = elts_number);
          match n with
          | Pinf ->
            [], Pinf, (last_bound, elts) :: l
          | Expr b ->
            let current_elts, old_elts = List.partition (fun a ->
              oracle (Greater(List.hd a, b))) elts in
            current_elts, Expr b, (last_bound, old_elts)::l
          | Ninf -> assert false
        ) (elts, Ninf, []) q
      in
      List.rev l
    | _ -> assert false



  let save_array_index: int term -> unit = fun t ->
    implies := IntSet.add t !implies

end
