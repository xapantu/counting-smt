type expr =
  | And of expr * expr
  | Or of expr * expr
  | Greater of expr * expr
  | Equality of expr * expr
  | Value of int
  | Var of string

type litteral =
  | Lit of string
  | NotLit of string
  | Card of string * expr

type sort =
  | Int
  | Bool

type cnf = litteral list list

let litteral_eq_neg a b = match a, b with
  | Lit a, NotLit b when a = b -> true
  | NotLit a, Lit b when a = b -> true
  | _ -> false

let litteral_neg = function
  | Lit a -> NotLit a
  | NotLit a -> Lit a
