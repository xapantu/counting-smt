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

  module ImpliSet = Set.Make (struct
      type t = bool array term * bool array term * int term * int term
      let compare = compare
    end)

  exception Unsat

  let declare_variable var =
    match var.sort with
        | Array(_, _) -> ()
        | _ -> ()

  type context = (a array term, a array term * StrSet.t) Hashtbl.t

  let implies = ref ImpliSet.empty

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
      let fusion = repr_a, class_total in
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

  (* Record the equalities between the arrays, might raise Unsat at some point *)
  let context_from_equality: a array equality list (*-> a equality list*) -> (bool term -> bool) -> (context * (a array term * a array term * bool) list (**  a equality list *)) = fun equalities_array (*equalities_elements*) oracle ->
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
        | AEquality(a, b) | ExtEquality(a, b) -> (a, b, oracle (S.equality_to_rel eq)) :: disequalities
      ) [] equalities_array
    (*,
    List.fold_left (fun disequalities eq ->
        match eq with
        | Bool_equality(Array_access(a, i, neg), c) ->
          let a = get_array_at 
        | a -> (Format.eprintf "equality not handled@."; a :: disequalities)*)


  (* Just a little help for the solver *)
  let save_implications () =
    let eqs, access = S.V.fold_rels (fun rel var (eqs, access) ->
        match rel with
        | Array_bool_equality(AEquality(_)) | Array_bool_equality(ExtEquality(_)) -> (rel, var)::eqs, access
        | Array_access(_) -> eqs, (rel, var)::access
        | _ -> eqs, access) ([], [])
    in
    List.map (function
        | Array_bool_equality(AEquality(a, b)), eq_var | Array_bool_equality(ExtEquality(a, b)), eq_var ->
          List.map (function
              | Array_access(t, i1, true), term1 when a = t ->
                List.fold_left (fun l access2 -> match access2 with
                    | Array_access(t, i2, true), term2 when b = t ->
                      if not (ImpliSet.mem (a, b, i1, i2) !implies) then
                        (
                          implies := ImpliSet.add (a, b, i1, i2) !implies;
                          Or(Not(And(Theory_expr(BVar(eq_var.name, true)), Theory_expr(Int_equality(Equality(i1, i2))))), 
                              Theory_expr(Bool_equality(Equality(BVar(term1.name, true), BVar(term2.name, true))))) :: l)
                      else
                        l
                    | _ -> l) [] access
              | _ -> []) access
          |> List.concat
        | _ -> assert false
      ) eqs
    |> List.concat



  

end
