exception Unprintable_elements of string
exception Unbounded_interval

type _ term_sort =
  | Tint : int term_sort
  | TBool: bool term_sort


type _ term =
  | IValue : int -> int term
  | IVar : string * int -> int term
  | BValue : bool -> bool term
  | BVar : string * bool -> bool term
  | Array_term : string * 'a term_sort -> 'a array term
  | Array_store : 'a array term * int term * 'a term -> 'a array term
  | Array_access : 'a array term * int term * bool (* last one is the negation *) -> 'a term
  | Ite: bool term * 'a term * 'a term -> 'a term
  | Mod: int term * int * int -> bool term
  | Greater: int term * int term -> bool term
  | Array_bool_equality: bool array equality -> bool term
  | Int_equality: int equality -> bool term
  | Bool_equality: bool equality -> bool term

and _ equality =
  | AEquality : 'a array term * 'a array term -> 'a array equality
  | NoEquality : 'a term * 'a term -> 'a equality
  | ExtEquality : 'a array term * 'a array term -> 'a array equality
  | Equality : 'a term * 'a term -> 'a equality


type arithmetic_expression =
  | APlus of arithmetic_expression * arithmetic_expression
  | AMinus of arithmetic_expression * arithmetic_expression
  | ATerm of int term

type concrete_value =
  | VBool of bool
  | VInt of int


let int_equality a b = Int_equality(Equality(a, b))

let bool_equality a b = Bool_equality(Equality(a, b))

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

type var = { name: string; sort: sort; internal: bool; }

type assignation = var * concrete_value
type model = assignation list

let rec term_to_string : type a. a term -> string = function
  | IVar (s, 0) -> s
  | IVar (s, i) when i > 0 -> Format.sprintf "(+ %s %d)" s i
  | IVar (s, i) (* when i < 0 *) -> Format.sprintf "(- %s %d)" s (-i)
  | BValue(false) -> "false"
  | BValue(true) -> "true"
  | BVar(s, true) -> s
  | BVar(s, false) -> Format.sprintf "(not %s)" s
  | IValue i -> string_of_int i
  | Array_term(e, _) ->
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
    Format.sprintf "(select %s %s)" tab index
  | Ite(a, b, c) ->
    Format.sprintf "(ite %s %s %s)" (term_to_string a) (term_to_string b) (term_to_string c)
  | Array_store(tab, index, write) ->
    let tab = term_to_string tab in
    let index = term_to_string index in
    let write = term_to_string write in
    Format.sprintf "(store %s %s %s)" tab index write
  | Greater(e1, e2) ->
    Format.sprintf "(>= %s %s)" (term_to_string e1) (term_to_string e2)
  | Int_equality(a) ->
    eq_to_smt a
  | Bool_equality(a) ->
    eq_to_smt a
  | Array_bool_equality(a) ->
    eq_to_smt a
and eq_to_smt: type a. a equality -> string = function
  | Equality(e1, e2) ->
    Format.sprintf "(= %s %s)" (term_to_string e1) (term_to_string e2)
  | ExtEquality(e1, e2) ->
    Format.sprintf "(= %s %s)" (term_to_string e1) (term_to_string e2)
  | AEquality(e1, e2) ->
    Format.sprintf "(nexteq %s %s)" (term_to_string e1) (term_to_string e2)
  | NoEquality(e1, e2) ->
    Format.sprintf "(not %s)" (eq_to_smt (Equality(e1, e2)))

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
  | Array_term(e, _) ->
    raise (Unprintable_elements e)
  | _ -> failwith "no uid"


let rec arith_expr_to_string = function
  | ATerm e -> term_to_string e
  | APlus(a, b) ->
    let a = arith_expr_to_string a in
    let b = arith_expr_to_string b in
    if a = "0" then b 
    else if b = "0" then a
    else
      Format.sprintf "(+ %s %s)" a b
  | AMinus(a, b) ->
    let a = arith_expr_to_string a in
    let b = arith_expr_to_string b in
    if a = "0" then
      Format.sprintf "(- %s)" b 
    else if b = "0" then
      a
    else
      Format.sprintf "(- %s %s)" a b

let bound_to_arith_expr = function
  | Ninf | Pinf -> raise Unbounded_interval
  | Expr e -> ATerm e

let bound_to_string e = arith_expr_to_string (bound_to_arith_expr e)

let interval_to_string (l, u) =
  arith_expr_to_string (AMinus (bound_to_arith_expr u, bound_to_arith_expr l))

let (plus_one: int term -> int term) = function
  | IVar(a, i) -> IVar(a, i + 1)
  | IValue(i) -> IValue (i + 1)

let (minus_one: int term -> int term) = function
  | IVar(a, i) -> IVar(a, i - 1)
  | IValue(i) -> IValue (i - 1)


let minus:int -> int term -> int term = fun n -> function
  | IVar(a, i) -> IVar(a, i - n)
  | IValue(i) -> IValue (i - n)

let rec not_term: bool term -> bool term = function
  | BValue(k) -> BValue(not k)
  | BVar(s, k) -> BVar (s, not k)
  | Array_access(tab, index, k) -> Array_access(tab, index, not k)
  | Ite(a, b, c) -> Ite(a, not_term b, not_term c)

let bound_inf_to_string = function
  | Ninf | Pinf -> "inf"
  | Expr e -> term_to_string e

let inf_interval_to_string (l, u) =
  "[" ^ bound_inf_to_string l ^ ", " ^ bound_inf_to_string u ^ "]"

let rec sort_to_string = function
  | Int -> "Int"
  | Bool -> "Bool"
  | Real -> "Real"
  | Array(a, b) -> Format.sprintf "(%s -> %s)" (sort_to_string a) (sort_to_string b)
  | Range(i) -> interval_to_string i
