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
    | ArrayValue of string * bool
    | ArrayArray of string * string * bool
    | EAnd of equality_type * equality_type
    | EOr of equality_type * equality_type
    | True
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
    ArrayValue (name, value)

  let constraints_subdiv: array_ctx -> array_subdivision -> rel list = fun _ ->
    raise Not_implemented

  let constraints_term: array_ctx -> array_subdivision -> int term = fun _ ->
    raise Not_implemented

  let array_sub_intersect: array_ctx -> array_subdivision -> array_subdivision -> array_subdivision = fun _ a b ->
    EAnd(a, b)

  let rec array_sub_to_dnf = function
    | EAnd(a, b) ->
      let a = array_sub_to_dnf a in
      let b = array_sub_to_dnf b in
      List.map (fun l ->
          List.map (fun k ->
              l @ k) b
        ) |> List.concat

  let array_sub_neg: array_ctx -> array_subdivision -> array_subdivision =
    fun a ->
      let rec aux = function
        | ArrayValue (n, t) -> ArrayValue (n, not t)
        | ArrayArray (n, m, t) -> ArrayValue (n, m, not t)
        | EAnd(a, b) -> EOr (aux a, aux b)
        | EOr(a, b) -> EAnd(aux a, aux b)
        | True -> Bottom
        | Bottom -> faulwith "neg of bottom"
      in aux

  let mk_full_subdiv: array_ctx -> interval -> array_subdivision = fun a b ->
    True

  let array_sub_to_string: array_ctx -> (unit -> string) -> ((array_subdivision, string) Hashtbl.t) -> array_subdivision -> interval -> string =
    fun ctx fresh_var htbl sub interval ->
       (assert (sub <> Bottom);
        let n =
          try
            Hashtbl.find htbl sub
          with
          | Not_found ->
            (let y = fresh_var () in
             Hashtbl.add htbl sub y;
             y)
        in
        interval_to_string interval)
    


end
