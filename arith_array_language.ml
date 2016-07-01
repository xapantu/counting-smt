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
  | Real
  | Array of sort * sort
  | Range of interval

type assignation = string * concrete_value
type model = assignation list

let apply_not: bool term -> bool term = function
  | BValue(b) -> BValue(not b)
  | BVar(s, b) -> BVar(s, not b)
  | Array_access(a, i, v) -> Array_access(a, i, not v)


let rec term_to_string : type a. a term -> string = function
  | IVar (s, 0) -> s
  | IVar (s, i) when i > 0 -> Format.sprintf "(+ %s %d)" s i
  | IVar (s, i) (* when i < 0 *) -> Format.sprintf "(- %s %d)" s (-i)
  | BValue(false) -> "false"
  | BValue(true) -> "true"
  | BVar(s, true) -> s
  | BVar(s, false) -> Format.sprintf "(not %s)" s
  | IValue i -> string_of_int i
  | Array_term e ->
    Format.eprintf "this array should not be printed@.";
    e
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
    Format.eprintf "this array should not be printed@.";
    Format.sprintf "(select %s %s)" tab index

let replace input output =
      Str.global_replace (Str.regexp_string input) output

let sanitize s =
  replace "." "" s |> replace "|" ""


let rec term_to_uid : type a. a term -> string = function
  | IVar (s, 0) -> (sanitize s)
  | IVar (s, i) when i > 0 -> Format.sprintf "!plus!%s!%d!" (sanitize s) i
  | IVar (s, i) (* when i < 0 *) -> Format.sprintf "!minus!%s!%d!" (sanitize s) (-i)
  | BValue(false) -> "false"
  | BValue(true) -> "true"
  | BVar(s, true) -> (sanitize s)
  | BVar(s, false) -> Format.sprintf "!not!%s!" (sanitize s)
  | IValue i -> string_of_int i
  | Array_term e ->
    raise (Unprintable_elements e)
  | _ -> failwith "no uid"

let rec rel_to_smt = function
  | Greater(e1, e2) ->
    Format.sprintf "(>= %s %s)" (term_to_string e1) (term_to_string e2)
  | IEquality(e1, e2) ->
    Format.sprintf "(= %s %s)" (term_to_string e1) (term_to_string e2)
  | BEquality(e1, e2) ->
    Format.sprintf "(= %s %s)" (term_to_string e1) (term_to_string e2)
  | Bool(b) ->
    term_to_string b

let bound_to_string = function
  | Ninf | Pinf -> raise Unbounded_interval
  | Expr e -> term_to_string e

let interval_to_string (l, u) =
  Format.sprintf "(- %s %s)" (bound_to_string u) (bound_to_string l)

let (plus_one: int term -> int term) = function
  | IVar(a, i) -> IVar(a, i + 1)
  | IValue(i) -> IValue (i + 1)

let (minus_one: int term -> int term) = function
  | IVar(a, i) -> IVar(a, i - 1)
  | IValue(i) -> IValue (i - 1)


let minus:int -> int term -> int term = fun n -> function
  | IVar(a, i) -> IVar(a, i - n)
  | IValue(i) -> IValue (i - n)

let not_term: bool term -> bool term = function
  | BValue(k) -> BValue(not k)
  | BVar(s, k) -> BVar (s, not k)
  | Array_access(tab, index, k) -> Array_access(tab, index, not k)

let bound_inf_to_string = function
  | Ninf | Pinf -> "inf"
  | Expr e -> term_to_string e

