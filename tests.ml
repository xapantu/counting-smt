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

(* let _ = LA_SMT.set_verbose true *)

(* let suite = *)
(*   "suite" >::: *)
(*   [ *)
(* "test1" >:: test_file "test1.smt" (assert_equal "sat\ny = 2\nx = 3\n"); *)
(* "test2" >:: test_file "test2.smt" (assert_equal "unsat\n"); *)
(* "test3" >:: test_file "test3.smt" (assert_equal "sat\n"); *)
(* "test_quant_sum" >:: test_file "test_quant_sum.smt" (assert_equal "unsat\n"); *)
(* "test_sum" >:: test_file "test_sum.smt" (assert_equal "unsat\n"); *)
(* "test_shadowing" >:: test_file "shadowing.smt" (assert_equal "sat\ny = 1\nx = 1\n"); *)
(* "test_lower" >:: test_file "test_lower.smt" (assert_equal "sat\ny = 0\nx = 1\n"); *)
(* "test_birecursion" >:: test_file "birecursion.smt" (assert_equal "sat\ny = 0\nx = 10\n"); *)
(* "test4" >:: test_file "test4.smt" (fun _ -> ()); *)
(* "vars" >:: test_file "vars.smt" (fun _ -> ()); *)
(* "constants" >:: test_file "constants.smt" (assert_equal "sat\ns2 = 1\ns1 = 2\n"); *)
(* "novals" >:: test_file "novars.smt" (assert_equal "sat\n"); *)
(* "strict_comparisons" >:: test_file "strict_comparison.smt" (assert_equal "sat\ns3 = 0\ns2 = 1\ns1 = 2\n"); *)
(* "not" >:: test_file "not.smt" (assert_equal "sat\nx = 10\n"); *)
(* "multiple_cards.smt" >:: test_file "multiple_card.smt" (assert_equal "unsat\n"); *)
    
(* "test_arrays" >:: test_file "test_arrays.smt" (assert_equal "sat\n"); *)
(* "test_arrays2" >:: test_file "test_arrays2.smt" (assert_equal "unsat\n"); *)
(* "test_arrays3" >:: test_file "test_arrays3.smt" (assert_equal "sat\n"); *)
(* "test_arrays4" >:: test_file "test_arrays4.smt" (assert_equal "unsat\n"); *)
(* "test_arrays5" >:: test_file "test_arrays5.smt" (assert_equal "unsat\n"); *)
(* ] *)

let test1 = "test_domain_neg" >:: test_domain_neg

let () = run_test_tt_main test1

