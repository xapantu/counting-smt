(* Ideally, that module should be parametrized by the data type (Bool, Int, Range, Reals) 
 * only bools for now *)
module Array_solver = struct

  exception Not_implemented

  include Arith_array_language

  type my_array = {
    name: string;
    indexes: interval;
  }

  type equality_type =
    | ArrayValue of string * bool
    | ArrayArray of bool * bool

  type array_subdivision =
    | Div of (equality_type list list) * interval
    | Bottom

  type domain = interval list

  type array_ctx = (string, my_array) Hashtbl.t

  let new_array ctx name indexes =
    Hashtbl.add ctx name { name; indexes; }

  let full_array_subdivision = Div ([], (Ninf, Pinf))

  let new_ctx () =
    Hashtbl.create 10

  let equality_arrays: array_ctx -> bool array term -> bool array term -> bool -> array_subdivision = fun _ ->
    raise Not_implemented

  let equality_array: array_ctx -> bool array term -> bool -> array_subdivision = fun ctx t value ->
    let Array_term(name) = t in
    Div ([[ArrayValue(name, value)]], (Ninf, Pinf))

  let constraints_subdiv: array_ctx -> array_subdivision -> rel list = fun _ ->
    raise Not_implemented

  let constraints_term: array_ctx -> array_subdivision -> int term = fun _ ->
    raise Not_implemented

  let array_sub_intersect: array_ctx -> array_subdivision -> array_subdivision -> array_subdivision = fun _ a b ->
    a

  let array_sub_neg: array_ctx -> array_subdivision -> array_subdivision = fun a b -> Bottom

  let mk_full_subdiv: array_ctx -> interval -> array_subdivision = fun a b ->
    full_array_subdivision

  let array_sub_to_string: array_ctx -> array_subdivision -> interval -> string =
    (fun ctx sub interval ->
       (assert (sub <> Bottom);
        interval_to_string interval)
    )


end
