(* Ideally, that module should be parametrized by the data type (Bool, Int, Range, Reals) 
 * only bools for now *)
module Array_solver = struct

  include Arith_array_language

  type array = {
    name: string;
    indexes: interval;
  }

  type array_subdivision

  type array_ctx(* = string (domain list) Hashtbl.t*)

  let new_array name indexes =
    Hashtbl.add name { name; indexes; }

  val new_ctx: unit -> array_ctx

  val equality_arrays: array_ctx -> domain list -> array -> array -> array_subdivision

  val equality_array: array_ctx -> domain list -> array -> array_subdivision

  val constraints_subdiv: array_ctx -> array_subdivision -> list rel

  val constraints_term: array_ctx -> array_subdivision -> int term


end
