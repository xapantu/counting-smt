open Smtlib
open OUnit2
open Theory_model

let read_not_blocking in_descr in_channel =
  let data = Bytes.create 1000 in
  let offset = ref 0 in
  while (
    let a, b, c = Unix.select [in_descr] [] [] (0.) in
    List.length a + List.length b + List.length c > 0
  )
  do
    
    offset := !offset + input in_channel data !offset 1000;
  done;
  let s = Bytes.to_string (Bytes.sub data 0 !offset)  in
  s

let test_file filename expected_result  _ =
  LA_SMT.reset_solver ();
  let real_name = "examples/" ^ filename in
  let input = open_in real_name in
  let result_descr, output_channel = Unix.pipe () in
  let result_channel, output_channel = Unix.(in_channel_of_descr result_descr, out_channel_of_descr output_channel) in
  let _ = runner output_channel (lexing input) [] in
  flush output_channel;
  let res = read_not_blocking result_descr result_channel in
  expected_result res


let _ = LA_SMT.set_verbose true

let suite =

  "suite" >:::
  [
    "test1" >:: test_file "test1.smt" (assert_equal "sat\ny = 2\nx = 3\n");
    "test2" >:: test_file "test2.smt" (assert_equal "unsat\n");
    "test3" >:: test_file "test3.smt" (assert_equal "sat\n");
    "test_quant_sum" >:: test_file "test_quant_sum.smt" (assert_equal "unsat\n");
    "test_sum" >:: test_file "test_sum.smt" (assert_equal "unsat\n");
    "test_shadowing" >:: test_file "shadowing.smt" (assert_equal "sat\ny = 1\nx = 1\n");
    "test_arrays" >:: test_file "test_arrays.smt" (fun _ -> ());
    "test_lower" >:: test_file "test_lower.smt" (assert_equal "sat\ny = 0\nx = 1\n");
  ]
;;


let () =

  run_test_tt_main suite

