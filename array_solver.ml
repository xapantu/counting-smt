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
  
  type domain = interval list

  type array_subdivision = hyp_tree option

  type array_ctx = { arrays: (string, my_array) Hashtbl.t;
                     mutable hyps: hyp_tree option;
                   }

  let new_array ctx name indexes =
    Hashtbl.add ctx.arrays name { name; indexes; }

  let new_ctx () =
    { arrays = Hashtbl.create 10; hyps = None; }

  let equality_arrays: array_ctx -> bool array term -> bool array term -> bool -> array_subdivision = fun _ ->
    raise Not_implemented

  let v = ref 0
  let fresh_var () =
    incr v;
    "array!" ^ (string_of_int !v)
  
  let assume tree name value =
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
               var_left = fresh_var ();
               var_right = fresh_var ();
               left_tree = None;
               right_tree = None;
               left_selection = (if value then Unselected else Selected);
               right_selection = (if value then Selected else Unselected);
             }
    in
    find_node_aux tree

  let equality_array: array_ctx -> bool array term -> bool -> array_subdivision -> array_subdivision = fun ctx t value sub ->
    let Array_term(name) = t in
    let tree = assume sub name value in
    ctx.hyps <- tree; tree

  let rec constraints_subdiv: array_ctx -> array_subdivision -> string = fun ctx a ->
    let rec all_subdiv = function
      | None -> "0"
      | Some s ->
        let left =
          if s.left_tree = None then
            s.var_left
          else
            all_subdiv s.left_tree
        in
        let right =
          if s.right_tree = None then
            s.var_right
          else
            all_subdiv s.right_tree
        in
        Format.sprintf "(+ %s %s)" left right
    in
    if a = None then "true"
    else Format.sprintf "(= %s %s)" "N" (all_subdiv a)


  let constraints_term: array_ctx -> array_subdivision -> int term = fun _ ->
    raise Not_implemented

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
    in
    intersect_aux a b

  let array_sub_dup: array_subdivision -> array_subdivision = fun a ->
    let rec dup_aux = function
      | Some a ->
      Some { a with left_tree = dup_aux a.left_tree; right_tree = dup_aux a.left_tree; }
      | None -> None
    in
    dup_aux a

  let unwrap = function
    | Some s -> s
    | None -> failwith "none, really?"

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

  let dont_care a =
    let rec aux = function
      | None -> None
      | Some s -> Some { s with left_selection = Dont_care; right_selection = Dont_care; left_tree = aux s.left_tree; right_tree = aux s.right_tree; }
    in
    aux a

  let mk_full_subdiv: array_ctx -> interval -> array_subdivision = fun a b ->
    array_sub_dup a.hyps |> dont_care

  let rec is_top: array_subdivision -> bool = function
    | None -> true
    | Some a -> ((a.left_tree <> None || a.left_selection = Dont_care) && (a.right_tree <> None || a.right_selection = Dont_care) && is_top a.right_tree && is_top a.left_tree)


  let array_sub_to_string: array_ctx -> array_subdivision -> interval -> string =
    fun ctx sub interval ->
      let rec aux = function
        | None -> "0"
        | Some s ->
          let left =
            if s.left_tree = None && (s.left_selection = Selected || s.left_selection = Dont_care) then s.var_left
            else "0"
          in
          let right =
            if s.right_tree = None && (s.right_selection = Selected || s.right_selection = Dont_care) then s.var_right
            else "0"
          in
          Format.sprintf "(+ %s (+ %s (+ %s %s)))" left right (aux s.left_tree) (aux s.right_tree)
      in
      aux sub
    


end
