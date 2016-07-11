open Arith_array_language

module type VM = sig
  val get_sort: string -> sort
  val get_range: string -> sort
end

module Variable_manager (Formula:sig
  type expr =
    | And of expr * expr
    | Or of expr * expr
    | Theory_expr of rel
    | Not of expr
  end) = struct

  exception Unknown_sort_for_var of string
  exception TypeCheckingError of string * string * string

  open Formula
  type var = { name: string; sort: sort; internal: bool; }
  let vars = ref []
  let range = Hashtbl.create 10
  let get_range = Hashtbl.find range

  let new_variables = React.new_event ()

  let use_var ?internal:(internal=false) sort name =
    let v = { name; sort; internal; } in
    vars := v :: !vars;
    React.event new_variables v
  
  let new_range: string -> bound -> bound -> unit =
    fun name b1 b2 ->
      Hashtbl.add range name (Range (b1, b2))

  let reset () =
    vars := []; Hashtbl.reset range 
  
  let constraints_on_sort sort name = match sort with
    | Int | Bool -> Theory_expr(Bool (BValue true))
    | Range(Expr a, Expr b) -> And(Theory_expr(Greater(b, IVar(name, 1))), Theory_expr(Greater(IVar(name, 0), a)))
    | Range(Ninf, Expr b) -> Theory_expr(Greater(b, IVar(name, 1)))
    | Range(Expr a, Pinf) -> Theory_expr(Greater(IVar(name, 0), a))
    | _ -> assert false

  let use_quantified_var name sort f =
    let v = { sort; name; internal = true; } in
    vars := v :: !vars;
    let a = f (constraints_on_sort sort name) in
    let first = ref true in
    vars := List.filter (fun x -> 
        if x = v then
          if !first then
            (first := false; false)
          else
            true
        else
          true) !vars;
    assert (not !first);
    a

  let get_sort name =
    try
    (List.find (fun v -> name = v.name) !vars).sort
    with
    | Not_found -> raise (Unknown_sort_for_var(name))

  let ensure_int name =
    match get_sort name with
    | Int | Range(_) -> ()
    | s -> raise (TypeCheckingError (name, "int", sort_to_string s))

  let ensure_bool name =
    let sort = get_sort name in
    if sort <> Bool then
        raise (TypeCheckingError (name, "bool", sort_to_string sort))

end
