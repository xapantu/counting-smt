open Arith_array_language

module type VM = sig
  val get_sort: string -> sort
  val get_range: string -> sort
  val find_all: (var -> bool) -> var list
  val new_variables: var React.event
  val fold_rels: (bool term -> var -> 'c -> 'c) -> 'c -> 'c
end

module Variable_manager (Formula:sig
  type expr =
    | And of expr * expr
    | Or of expr * expr
    | Theory_expr of bool term
    | Not of expr
  end) = struct

  exception Unknown_sort_for_var of string
  exception TypeCheckingError of string * string * string

  open Formula
  let vars = ref (Hashtbl.create 1000)
  let range = Hashtbl.create 10
  let rels = ref (Hashtbl.create 100)
  let get_range = Hashtbl.find range

  let new_variables = React.new_event ()

  let fold_rels f c =
    Hashtbl.fold f !rels c

  let find a =
    Hashtbl.find !vars a

  let fresh_var =
    let i = ref 0 in
    fun () ->
      incr i;
      "rel!" ^ string_of_int !i

  let use_var ?internal:(internal=false) sort name =
    let v = { name; sort; internal; } in
    Hashtbl.add !vars v.name v;
    React.event new_variables v

  let has_rel rel =
    Hashtbl.mem !rels rel

  let use_var_for_rel (rel:bool term) =
    try
      Hashtbl.find !rels rel
    with
    | Not_found ->
      let v = { name = fresh_var (); sort = Bool; internal = true; } in
      Hashtbl.add !vars v.name v;
      Hashtbl.add !rels rel v;
      React.event new_variables v; v
  
  let new_range: string -> bound -> bound -> unit =
    fun name b1 b2 ->
      Hashtbl.add range name (Range (b1, b2))

  let reset () =
    Hashtbl.reset !vars; Hashtbl.reset range; Hashtbl.reset !rels
  
  let constraints_on_sort sort name = match sort with
    | Int | Bool -> Theory_expr(BValue true)
    | Range(Expr a, Expr b) -> And(Theory_expr(Greater(b, IVar(name, 1))), Theory_expr(Greater(IVar(name, 0), a)))
    | Range(Ninf, Expr b) -> Theory_expr(Greater(b, IVar(name, 1)))
    | Range(Expr a, Pinf) -> Theory_expr(Greater(IVar(name, 0), a))
    | _ -> assert false

  let use_quantified_var name sort f =
    let v = { sort; name; internal = true; } in
    Hashtbl.add !vars v.name v;
    let a = f (constraints_on_sort sort name) in
    Hashtbl.remove !vars v.name; 
    a

  let find_all f =
    let s = ref [] in
    Hashtbl.iter (fun a b ->
        if f b then
          s := b :: !s;
      ) !vars;
    !s

  let get_sort name =
    try
      (Hashtbl.find !vars name).sort
    with
    | Not_found -> raise (Unknown_sort_for_var(name))

  let rec get_sort_for_term: type a. a term -> sort = function
    | IVar(_) -> Int
    | IValue(_) -> Int
    | BVar(_) -> Bool
    | BValue (_) -> Bool
    | Array_term(a, _) ->
      get_sort a
    | Ite(a, b, c) -> get_sort_for_term b
    | Mod(_) -> Bool
    | Greater(_) -> Bool
    | Int_equality(_) -> Bool
    | Bool_equality(_)  -> Bool
    | Array_bool_equality(_) -> Bool
    | Array_store(a, _, _) ->
      get_sort_for_term a
    | Array_access(a, _, _) ->
      match get_sort_for_term a with
      | Array(_, a) -> a
      | _ -> failwith "humm this array is not an array!?"

  
  let ensure_int name =
    match get_sort name with
    | Int | Range(_) -> ()
    | s -> raise (TypeCheckingError (name, "int", sort_to_string s))

  let ensure_bool name =
    let sort = get_sort name in
    if sort <> Bool then
        raise (TypeCheckingError (name, "bool", sort_to_string sort))

end
