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
type domain = interval list

type sort =
  | Int
  | Bool
  | Array of sort * sort
  | Range of interval

type assignation = string * concrete_value
type model = assignation list
