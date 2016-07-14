open Formula

(**
 * A theory works as follows: to solve a formula,
 * first a premodel is constructed, then every construct must be solved,
 * if they can be solved with this premodel, it means that the formula is
 * satisfiable, and in this case, it produces an abstract_model, which can then be turned
 * into a full model.
 * If not, then it's up to the user to ask for another premodel and restart.
 **)
module type T = sig
  module Formula : F
  open Formula
  type premodel
  type abstract_model
  type model
  type domain
  (* for instance a cardinality constraints, or a forall, or a exists, or whatever *)
  type construct

  exception Unsat

  val build_domain_for_construct: premodel -> construct -> domain
  val ensure_domain: premodel -> string -> domain -> unit
  val ensure_domain_fun: premodel -> (string -> string) -> domain -> unit
  val ensure_domains_consistency: premodel -> domain list -> unit
  val domain_to_string: domain -> string
  val assert_formula: expr -> unit
  val sort_for_construct: construct -> sort
  
  val build_premodel: unit -> (((string -> string) * domain) list) * premodel
  val build_abstract_model: premodel -> abstract_model
  val build_full_model: abstract_model -> model

  val print_model: model -> unit

end
