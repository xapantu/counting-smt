open Smtlib
open OUnit2
open Theory_model
open Arith_array_language

let test_domain_neg _ =
  let open LA_SMT in
  let a_ctx = LA_SMT.Arrays.new_ctx LA_SMT.fresh_var_array LA_SMT.ensure_var_exists in
  (* LA_SMT.reset_solver (); *)
  let dom = [(LA_SMT.Arrays.mk_full_subdiv a_ctx (Ninf, Pinf)), (Ninf, Pinf)] in
  assert_equal (LA_SMT.domain_neg ([], new Interval_manager.interval_manager, a_ctx) dom) [];
  let dom = [(LA_SMT.Arrays.mk_full_subdiv a_ctx (Ninf, Expr (IValue 6))), (Ninf, Expr (IValue 6))] in
  let dom_neg = domain_neg ([],  new Interval_manager.interval_manager, a_ctx) dom in
  assert_equal (List.length dom_neg) 1;
  assert_equal  (snd @@ List.hd @@ dom_neg) (Expr (IValue 6), Pinf);
  let interv = (Expr (IValue 8), Pinf) in
  let dom = dom @ [LA_SMT.Arrays.mk_full_subdiv a_ctx interv, interv] in
  let dom_neg = domain_neg ([],  new Interval_manager.interval_manager, a_ctx) dom in
  assert_equal (List.length dom_neg) 1;
  assert_equal  (snd @@ List.hd @@ dom_neg) (Expr (IValue 6), Expr (IValue 8));
  ()

let test1 = "test_domain_neg" >:: test_domain_neg

let () = run_test_tt_main test1

