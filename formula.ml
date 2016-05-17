module type F = sig

  type texpr

  type expr =
    | And of expr * expr
    | Or of expr * expr
    | Theory_expr of texpr

  type domain

  type litteral =
    | Lit of string
    | NotLit of string
    | Card of string * expr * (domain option)

  type cnf = litteral list list
  type assumptions = litteral list

  val litteral_eq_neg : litteral -> litteral -> bool
  val litteral_neg : litteral -> litteral

end

module IFormula (T : sig
    type texpr
    type domain
  end) = struct

  type texpr = T.texpr
  type domain = T.domain

  type expr =
    | And of expr * expr
    | Or of expr * expr
    | Theory_expr of texpr

  type litteral =
    | Lit of string
    | NotLit of string
    | Card of string * expr * (domain option)

  type cnf = litteral list list

  exception Cardinality_negation

  let litteral_eq_neg a b = match a, b with
    | Lit a, NotLit b when a = b -> true
    | NotLit a, Lit b when a = b -> true
    | _ -> false

  let litteral_neg = function
    | Lit a -> NotLit a
    | NotLit a -> Lit a
    | _ -> raise Cardinality_negation

end
