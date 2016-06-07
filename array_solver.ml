(* Ideally, that module should be parametrized by the data type (Bool, Int, Range, Reals) 
 * only bools for now *)
module Array_solver = struct

  exception Not_implemented

  include Arith_array_language

  type my_array = {
    name: string;
    indexes: interval;
  }

  type array_subdivision =
    | Div of (string * bool) list list
    | Bottom
  type domain = interval list

  type array_ctx = (string, my_array) Hashtbl.t

  let new_array ctx name indexes =
    Hashtbl.add ctx name { name; indexes; }

  let full_array_subdivision = Div []

  let new_ctx () =
    Hashtbl.create 10

  let equality_arrays: array_ctx -> bool array term -> bool array term -> bool -> array_subdivision = fun _ ->
    raise Not_implemented

  let equality_array: array_ctx -> bool array term -> bool -> array_subdivision = fun ctx t value ->
    let Array_term(name) = t in
    Div [[name, value]]

  let constraints_subdiv: array_ctx -> array_subdivision -> rel list = fun _ ->
    raise Not_implemented


  let constraints_term: array_ctx -> array_subdivision -> int term = fun _ ->
    raise Not_implemented

  let array_sub_intersect: array_ctx -> array_subdivision -> array_subdivision -> array_subdivision = fun _ a b ->
    Bottom

  let array_sub_neg: array_ctx -> array_subdivision -> array_subdivision = fun a b -> Bottom

  let mk_full_subdiv: array_ctx -> interval -> array_subdivision = fun _ _ -> full_array_subdivision
  
  let array_sub_to_string: array_ctx -> array_subdivision -> interval -> string =
    fun ctx sub interval ->
      (*if sub <> Bottom then*)
        interval_to_string interval
      (*else
        "0"*)


end
