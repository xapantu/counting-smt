open Utils

(* Ideally, that module should be parametrized by the data type (Bool, Int, Range, Reals) 
 * only bools for now *)
module Array_solver = struct

  exception Not_implemented

  include Arith_array_language

  type my_array = {
    name: string;
    indexes: interval;
  }

  type selection =
    | Selected
    | Unselected
    | Dont_care

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
      | None -> Format.printf "%s -@." s
      | Some a -> Format.printf "%s%s@." s a.name; aux (s ^ a.var_left ^ "\t") a.left_tree; aux (s ^ a.var_right ^ "\t") a.right_tree
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
              s.left_selection <- Unselected;
              s.right_selection <- Selected;

              unselect_all s.left_tree;
              select_dont_care s.right_tree;
            )
          else
            (
              s.right_selection <- Unselected;
              s.left_selection <- Selected;

              unselect_all s.right_tree;
              select_dont_care s.left_tree;
            )
        else
          begin
            s.left_tree <- find_node_aux s.left_tree;
            s.right_tree <- find_node_aux s.right_tree;
          end
        end;
        Some s
      | None ->
        Some { name;
               var_left = ctx.fresh_var ();
               var_right = ctx.fresh_var ();
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
  let rec constraints_subdiv: array_ctx -> string -> string -> array_subdivision -> string = fun ctx prefix total a ->
    let prefix = "a!" ^ prefix in
    let rec all_subdiv = function
      | None -> "true", None
      | Some s ->
        let left_constraint, var_left = all_subdiv s.left_tree in
        let right_constraint, var_right = all_subdiv s.right_tree in
        ctx.ensure_var_exists (prefix ^ s.var_left);
        ctx.ensure_var_exists (prefix ^ s.var_right);
        (if s.left_tree = None then
           "true"
         else
          Format.sprintf "(= %s%s %s) (= %s%s %s) %s %s" prefix s.var_left (unwrap var_left) prefix s.var_right (unwrap var_right) left_constraint right_constraint),
        Some (Format.sprintf "(+ %s%s %s%s)" prefix s.var_left prefix s.var_right)
    in
    let constraints_total_sum, additional = all_subdiv a in
    let constraints_total_sum = if additional = None then constraints_total_sum else
        Format.sprintf "(= %s %s) %s" total (unwrap additional) constraints_total_sum
    in
    let rec extract_from_tree = function
      | None -> []
      | Some s ->
        let left =
          if s.left_tree = None then
            [prefix ^ s.var_left]
          else
            extract_from_tree s.left_tree
        in
        let right =
          if s.right_tree = None then
            [prefix ^ s.var_right]
          else
            extract_from_tree s.right_tree
        in
        left @ right
    in
    extract_from_tree a
    |> List.fold_left (fun l s -> Format.sprintf "%s (>= %s 0)" l s) ""
    |> fun s ->
        Format.sprintf "(and %s %s)" s constraints_total_sum

  (* the first subdivision must be smaller than the second one *)
  let array_sub_intersect: array_ctx -> array_subdivision -> array_subdivision -> array_subdivision = fun ctx a b ->
    let rec intersect_aux a b =
      match a, b with
      | None, None -> None
      | None, Some s -> Some s
      | Some a, Some b ->
        assert (a.name = b.name && a.var_right = b.var_right && a.var_left = b.var_left);
        let left_selection, left_tree =
          if a.left_selection <> Unselected && b.left_selection = Selected then
            b.left_selection, intersect_aux a.left_tree b.left_tree
          else if b.left_selection = Unselected || b.left_selection = Unselected then
            Unselected, b.left_tree
          else if b.left_selection = Dont_care && a.left_selection = Selected then
            a.left_selection, intersect_aux a.left_tree b.left_tree
          else (* two Dont_care *)
            Dont_care, intersect_aux a.left_tree b.left_tree
        in
        let right_selection, right_tree =
          if a.right_selection <> Unselected && b.right_selection = Selected then
            b.right_selection, intersect_aux a.right_tree b.right_tree
          else if b.right_selection = Unselected || b.right_selection = Unselected then
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
    let rec neg_aux = function
      | None -> None
      | Some a ->
      if a.left_tree = None || a.right_tree = None then
        Some { a with left_selection = a.right_selection; right_selection = a.left_selection; }
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
    array_sub_neg ctx (array_sub_intersect ctx (array_sub_neg ctx mysub) (array_sub_neg ctx mysub2))


  let mk_full_subdiv: array_ctx -> interval -> array_subdivision = fun a b ->
    array_sub_dup a.hyps |> dont_care

  let rec is_top: array_subdivision -> bool = function
    | None -> true
    | Some a -> ((a.left_tree <> None || a.left_selection = Dont_care) && (a.right_tree <> None || a.right_selection = Dont_care) && is_top a.right_tree && is_top a.left_tree)


  let array_sub_to_string ctx prefix sub interval =
    let prefix = List.map ( (^) "a!") prefix in
    let rec aux = function
      | None -> ["0"]
      | Some s ->
        let left =
          if s.left_tree = None && (s.left_selection = Selected || s.left_selection = Dont_care) then
            List.map (fun p -> p ^ s.var_left) prefix
          else ["0"]
        in
        let right =
          if s.right_tree = None && (s.right_selection = Selected || s.right_selection = Dont_care) then
            List.map (fun p -> p ^ s.var_right) prefix
          else ["0"]
        in
        left @ right @ (aux s.left_tree) @ (aux s.right_tree)
    in
    aux sub
    


end
