exception Unprintable_elements of string
exception Unbounded_interval

type _ term =
  | IValue : int -> int term
  | IVar : string * int -> int term
  | BValue : bool -> bool term
  | BVar : string * bool -> bool term
  | Array_term : string -> bool array term
  | Array_access : bool array term * int term * bool (* last one is the negation *) -> bool term

type concrete_value =
  | VBool of bool
  | VInt of int

type rel =
  | Greater of int term * int term
  | IEquality of int term * int term
  | BEquality of bool term * bool term
  | Bool of bool term

type bound =
  | Ninf
  | Pinf
  | Expr of int term

type interval = bound * bound

type sort =
  | Int
  | Bool
  | Array of sort * sort
  | Range of interval

type assignation = string * concrete_value
type model = assignation list

let rec term_to_string: type a. a term -> string = function
  | IVar (s, 0) -> s
  | IVar (s, i) when i > 0 -> "(+ " ^ s ^ " " ^ string_of_int i ^ ")"
  | IVar (s, i) (* when i < 0 *) -> "(- " ^ s ^ " " ^ string_of_int (-i) ^ ")"
  | BValue(false) -> "false"
  | BValue(true) -> "true"
  | BVar(s, true) -> s
  | BVar(s, false) -> Format.sprintf "(not %s)" s
  | IValue i -> string_of_int i
  | Array_term e ->
    raise (Unprintable_elements e)
  | Array_access(tab, index, false) ->
    Format.sprintf "(not %s)" (term_to_string (Array_access(tab, index, true)))
  | Array_access(tab, index, true) ->
    let tab =
      try
        term_to_string tab
      with
      | Unprintable_elements(e) -> e
    in
    let index = term_to_string index in
    raise (Unprintable_elements (Format.sprintf "%s[%s]" tab index))


let rec rel_to_smt = function
  | Greater(e1, e2) ->
    "(>= " ^ term_to_string e1 ^ " " ^ term_to_string e2 ^ ")"
  | IEquality(e1, e2) ->
    "(= " ^ term_to_string e1 ^ " " ^ term_to_string e2 ^ ")"
  | BEquality(e1, e2) ->
    "(= " ^ term_to_string e1 ^ " " ^ term_to_string e2 ^ ")"
  | Bool(b) ->
    term_to_string b

let bound_to_string = function
  | Ninf | Pinf -> raise Unbounded_interval
  | Expr e -> term_to_string e

let interval_to_string (l, u) =
  "(- " ^ bound_to_string u ^ " " ^ bound_to_string l ^ ")"
