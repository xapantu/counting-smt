open Utils
open Arith_array_language
open Lisp

module Array_solver(S: sig
    module V:Variable_manager.VM
    type a
    val equality_to_rel: a array equality -> rel
  end) = struct
  
  module V = S.V
  type a = S.a

  module StrSet = Set.Make (struct type t = a array term
      let compare = compare end)

  exception Unsat

  let declare_variable var =
    match var.sort with
        | Array(_, _) -> ()
        | _ -> ()

  type context = (a array term, a array term * StrSet.t) Hashtbl.t

  let _ = React.iter V.new_variables declare_variable

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
    let c = StrSet.filter (function
        | Array_store(_) -> true
        | _ -> false) class_total |> StrSet.cardinal
    in
    if c > 1 then
      false
    else
      let fusion = repr_a, class_total in
      let () = StrSet.iter (fun a ->
          Hashtbl.add ctx a fusion) class_total in
      true

  let ensure_distinct_class ctx a b =
    ensure_class ctx a;
    ensure_class ctx b;
    Hashtbl.find ctx a <> Hashtbl.find ctx b

  (* Record the equalities between the arrays, might raise Unsat at some point *)
  let context_from_equality: a array equality list -> (rel -> bool) -> (context * (a array term * a array term * bool) list) = fun equalities oracle ->
    let context = Hashtbl.create 10 in
    context, List.fold_left (fun disequalities eq ->
        match eq with
        | AEquality(Array_term(a, sa), Array_term(b, sb)) ->
          if oracle (S.equality_to_rel eq) then
            ignore (merge_class context (Array_term(a, sa)) (Array_term(b, sb)));
          disequalities
        | ExtEquality(Array_term(a, sa), Array_term(b, sb)) ->
          if oracle (S.equality_to_rel eq) then
            if merge_class context (Array_term(a, sa)) (Array_term(b, sb)) then
              disequalities
            else
              (Array_term(a, sa), Array_term(b, sb), true) :: disequalities
          else
            begin
              if ensure_distinct_class context (Array_term(a, sa)) (Array_term(b, sb)) then
                (Array_term(a, sa), Array_term(b, sb), false) :: disequalities
              else
                raise Unsat
            end
        | AEquality(a, b) | ExtEquality(a, b) -> (a, b, oracle (S.equality_to_rel eq)) :: disequalities
      ) [] equalities
  
  let get_array_at: context -> a array term -> int term -> a term = fun context myarray index ->
    ensure_class context myarray;
    let (repr, _) = get_class context myarray in

    Array_access(repr, index, false)


end
