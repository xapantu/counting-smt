open Utils

(* Ideally, that module should be parametrized by the data type (Bool, Int, Range, Reals) 
 * only bools for now *)
module Array_solver = struct

  exception Not_implemented

  open Arith_array_language

  type my_array = {
    name: string;
    indexes: interval;
  }

  type selection =
    | Selected
    | Unselected
    | Dont_care

  let selection_to_str = function
    | Selected -> "sel"
    | Unselected -> "uns"
    | Dont_care ->  "don"

  (* false is left, true is right *)
  type hyp_tree = { name: string;
                    var_left: string;
                    var_right: string; 
                    mutable left_tree: hyp_tree option;
                    mutable right_tree: hyp_tree option;
                    mutable left_selection: selection;
                    mutable right_selection: selection; }

  let print_tree h =
    let rec aux s = function
      | None -> Format.eprintf "%s -@." s
      | Some a -> Format.eprintf "%s%s %s %s@." s a.name (selection_to_str a.left_selection) (selection_to_str a.right_selection); aux (s ^ a.var_left ^ "\t") a.left_tree; aux (s ^ a.var_right ^ "\t") a.right_tree
    in
    aux "" h
  
  type domain = interval list

  type array_subdivision = hyp_tree option

  type array_ctx = { arrays: (string, my_array) Hashtbl.t;
                     mutable hyps: hyp_tree option;
                     fresh_var: unit -> string;
                     ensure_var_exists: string -> unit;
                   }

  let new_array ctx name indexes =
    Hashtbl.add ctx.arrays name { name; indexes; }

  let new_ctx fresh_var ensure_var_exists =
    { arrays = Hashtbl.create 10; hyps = None; fresh_var; ensure_var_exists; }

  let assume ctx name value tree =
    let rec unselect_all = function
      | Some s -> (s.left_selection <- Unselected; s.right_selection <- Unselected; unselect_all s.left_tree; unselect_all s.right_tree;)
      | None -> ()
    in
    let rec select_dont_care = function
      | Some s ->
        begin
          if s.left_selection = Dont_care then 
           begin
             s.left_selection <- Selected;
             select_dont_care s.left_tree;
           end;
          if s.right_selection = Dont_care then 
           begin
             s.right_selection <- Selected;
             select_dont_care s.right_tree;
           end
        end
      | None -> ()
    in
    let rec find_node_aux = function
      | Some s -> 
        begin
        if s.name = name then
          if value then
            (
              if s.left_selection = Dont_care then
              s.left_selection <- Unselected;
              if s.right_selection = Dont_care then
              s.right_selection <- Selected;

              unselect_all s.left_tree;
              select_dont_care s.right_tree;
            )
          else
            (
              if s.right_selection = Dont_care then
              s.right_selection <- Unselected;
              if s.left_selection = Dont_care then
              s.left_selection <- Selected;

              unselect_all s.right_tree;
              select_dont_care s.left_tree;
            )
        else
          begin
            if not (s.left_tree = None && s.left_selection = Unselected) then
              s.left_tree <- find_node_aux s.left_tree;
            if not (s.right_tree = None && s.right_selection = Unselected) then
              s.right_tree <- find_node_aux s.right_tree;
          end
        end;
        Some s
      | None ->
        let var_left = ctx.fresh_var ()
        and var_right = ctx.fresh_var () in
        Some { name;
               var_left;
               var_right;
               left_tree = None;
               right_tree = None;
               left_selection = (if value then Unselected else Selected);
               right_selection = (if value then Selected else Unselected);
             }
    in
    let new_tree = find_node_aux tree in
    ctx.hyps <- new_tree;
    new_tree
  
  let equality_array: array_ctx -> bool array term -> bool -> array_subdivision -> array_subdivision = fun ctx t value sub ->
    let Array_term(name) = t in
    assume ctx name value sub

  (* The first string argument is the prefix of the variable, for instance if one wants a constraints for every interval
   * the second one is the number of indices. *)
  let rec constraints_subdiv: array_ctx -> string -> string -> array_subdivision -> rel list = fun ctx prefix total a ->
    let prefix = "a!" ^ prefix in
    let rec all_subdiv = function
      | Some s ->
        let left_constraint, var_left = all_subdiv s.left_tree in
        let right_constraint, var_right = all_subdiv s.right_tree in
        ctx.ensure_var_exists (prefix ^ s.var_left);
        ctx.ensure_var_exists (prefix ^ s.var_right);
        let left_cond = if s.left_tree = None then
            ([Bool(BValue (true))] : rel list)
         else
           IEquality (IVar(prefix ^ s.var_left, 0), IVar(unwrap var_left, 0)) :: left_constraint
        in
        let right_cond = if s.right_tree = None then
            ([Bool(BValue (true))] : rel list)
         else
           IEquality (IVar(prefix ^ s.var_right,0), IVar(unwrap var_right, 0)) :: right_constraint
        in
        left_cond @ right_cond,
        Some (Format.sprintf "(+ %s%s %s%s)" prefix s.var_left prefix s.var_right)
      | None -> [Bool(BValue(true))], None
    in
    let constraints_total_sum, additional = all_subdiv a in
    let constraints_total_sum = if additional = None then constraints_total_sum else
        IEquality(IVar(total, 0), IVar(unwrap additional, 0)) :: constraints_total_sum
    in
    let rec extract_from_tree = function
      | None -> []
      | Some s ->
        let left =
          if s.left_tree = None then

            (prefix ^ s.var_left) ::
            extract_from_tree s.left_tree
          else
            extract_from_tree s.left_tree
        in
        let right =
          if s.right_tree = None then
            (prefix ^ s.var_right)::
            extract_from_tree s.right_tree
          else
            extract_from_tree s.right_tree
        in
        left @ right
    in
    extract_from_tree a
    |> List.map (fun s -> Greater(IVar(s, 0), IValue 0))
    |> fun s ->
        s @ constraints_total_sum

  (* the first subdivision must be smaller than the second one *)
  let array_sub_intersect: array_ctx -> array_subdivision -> array_subdivision -> array_subdivision = fun ctx a b ->
    let rec intersect_aux a b =
      match a, b with
      | None, None -> None
      | None, Some s -> Some s
      | Some a, Some b ->
        assert (a.name = b.name && a.var_right = b.var_right && a.var_left = b.var_left);
        let left_selection, left_tree =
          if b.left_tree <> None then
            Dont_care, intersect_aux a.left_tree b.left_tree
          else if a.left_selection <> Unselected && b.left_selection = Selected then
            b.left_selection, intersect_aux a.left_tree b.left_tree
          else if b.left_selection = Unselected || a.left_selection = Unselected then
            Unselected, b.left_tree
          else if b.left_selection = Dont_care && a.left_selection = Selected then
            a.left_selection, intersect_aux a.left_tree b.left_tree
          else (* two Dont_care *)
            Dont_care, intersect_aux a.left_tree b.left_tree
        in
        let right_selection, right_tree =
          if b.right_tree <> None then
            Dont_care, intersect_aux a.right_tree b.right_tree
          else if a.right_selection <> Unselected && b.right_selection = Selected then
            b.right_selection, intersect_aux a.right_tree b.right_tree
          else if b.right_selection = Unselected || a.right_selection = Unselected then
            Unselected, b.right_tree
          else if b.right_selection = Dont_care && a.right_selection = Selected then
            a.right_selection, intersect_aux a.right_tree b.right_tree
          else (* two Dont_care *)
            Dont_care, intersect_aux a.right_tree b.right_tree
        in

        Some { var_right = a.var_right;
               var_left = a.var_left;
               left_selection;
               right_selection;
               left_tree;
               right_tree;
               name = a.name;
             }
      | _ -> failwith "subdivision a is NOT smaller than b, aborting"
    in
    intersect_aux a b

  let array_sub_dup: array_subdivision -> array_subdivision = fun a ->
    let rec dup_aux = function
      | Some a ->
      Some { a with left_tree = dup_aux a.left_tree; right_tree = dup_aux a.right_tree; }
      | None -> None
    in
    dup_aux a



  let dont_care a =
    let rec aux = function
      | None -> None
      | Some s -> Some { s with left_selection = Dont_care; right_selection = Dont_care; left_tree = aux s.left_tree; right_tree = aux s.right_tree; }
    in
    aux a


  let array_sub_neg: array_ctx -> array_subdivision -> array_subdivision = fun c a ->
    let duplicated = array_sub_dup a in
    let neg = function
      | Selected -> Unselected
      | Unselected -> Selected
      | Dont_care -> Dont_care
    in
    let rec neg_aux = function
      | None -> None
      | Some a ->
      if a.left_tree = None && a.right_tree = None then
        Some { a with left_selection = neg a.left_selection; right_selection = neg a.right_selection; }
      else if a.left_tree = None then
        Some { a with left_selection = neg a.left_selection; right_tree = neg_aux a.right_tree; }
      else if a.right_tree = None then
        Some { a with left_tree = neg_aux a.left_tree; right_selection = neg a.right_selection; }
      else
        Some { a with left_tree = neg_aux a.left_tree; right_tree = neg_aux a.right_tree; }
    in
    neg_aux duplicated
  
  let equality_arrays: array_ctx -> bool array term -> bool array term -> bool -> array_subdivision -> array_subdivision = fun ctx t1 t2 value sub ->
    let Array_term(name1) = t1
    and Array_term(name2) = t2 in
    let mysub =
      array_sub_dup sub
      |> assume ctx name1 true
      |> assume ctx name2 value
    in
    let mysub2 =
      dont_care mysub
      |> array_sub_intersect ctx sub
      |> assume ctx name1 false
      |> assume ctx name2 (not value)
    in
    let d = array_sub_neg ctx (array_sub_intersect ctx (array_sub_neg ctx mysub) (array_sub_neg ctx mysub2))
    in d


  let mk_full_subdiv: array_ctx -> interval -> array_subdivision = fun a b ->
    array_sub_dup a.hyps |> dont_care

  let rec is_top: array_subdivision -> bool = function
    | None -> true
    | Some a -> ((a.left_tree <> None || a.left_selection = Dont_care) && (a.right_tree <> None || a.right_selection = Dont_care) && is_top a.right_tree && is_top a.left_tree)


  let array_sub_to_string ctx prefix sub interval =
    let rec all_true = function
      | None -> false
      | Some s ->
         ((s.left_tree = None && (s.left_selection = Selected || s.left_selection = Dont_care)) || (all_true s.left_tree)) &&
         ((s.right_tree = None && (s.right_selection = Selected || s.right_selection = Dont_care)) || (all_true s.right_tree))
    in
    let prefix = List.map ( (^) "a!") prefix in
    let rec aux = function
      | None -> ["0"]
      | Some s ->
        let left =
          if all_true s.left_tree || (s.left_tree = None && (s.left_selection = Selected || s.left_selection = Dont_care)) then
            List.map (fun p -> p ^ s.var_left) prefix
          else ["0"]
        in
        let right =
          if all_true s.right_tree || (s.right_tree = None && (s.right_selection = Selected || s.right_selection = Dont_care)) then
            List.map (fun p -> p ^ s.var_right) prefix
          else ["0"]
        in
        left @ right @ (if all_true s.left_tree then [] else aux s.left_tree) @ (if all_true s.right_tree then [] else aux s.right_tree)
    in
    aux sub
    


end
