open Utils
open Arith_array_language
open Lisp

module Array_solver(S: sig
    module V:Variable_manager.VM
    type a
  end) = struct
  
  module V = S.V
  type a = S.a

  module StrSet = Set.Make(String)

  module TC = Lisp_typechecking.Lisp_typechecking(V)

  exception Unsat

  let declare_variable var =
    match var.sort with
        | Array(_, _) -> ()
        | _ -> ()

  type context = (StrSet.t * a array term) list

  let _ = React.iter V.new_variables declare_variable

  let get_array_at: context -> a array term -> int term -> a term = fun context myarray index ->
    Array_access(myarray, index, false)

  (* Record the equalities between the arrays, might raise Unsat at some point *)
  let context_from_equality: a array equality list -> (rel -> bool) -> (context * (a array term * a array term) list) = fun equalities oracle ->
    raise Unsat

end
