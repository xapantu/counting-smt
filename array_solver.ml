(* Ideally, that module should be parametrized by the data type (Bool, Int, Range, Reals) 
 * only bools for now *)
module Array_solver = struct

  exception Not_implemented

  include Arith_array_language

  type array = {
    name: string;
    indexes: interval;
  }

  type array_subdivision = int
  type domain = interval list

  type array_ctx = int (* = string (domain list) Hashtbl.t*)

  let new_array ctx name indexes =
    Hashtbl.add ctx name { name; indexes; }

  let full_array_subdivision = 1

  let new_ctx () =
    0

  let equality_arrays: array_ctx -> domain list -> array -> array -> bool -> array_subdivision = fun _ ->
    raise Not_implemented

  let equality_array: array_ctx -> domain list -> array -> bool -> array_subdivision = fun _ ->
    raise Not_implemented

  let constraints_subdiv: array_ctx -> array_subdivision -> rel list = fun _ ->
    raise Not_implemented


  let constraints_term: array_ctx -> array_subdivision -> int term = fun _ ->
    raise Not_implemented

  let array_sub_neg: array_ctx -> array_subdivision -> array_subdivision = fun a b -> -b

  let mk_full_subdiv: array_ctx -> interval -> array_subdivision = fun _ _ -> full_array_subdivision
  
  let array_sub_to_string: array_ctx -> array_subdivision -> interval -> string =
    fun ctx sub interval ->
      if sub > 0 then
        interval_to_string interval
      else
        "0"


end
