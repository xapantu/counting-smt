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
  assert_equal res expected_result


let _ = LA_SMT.set_verbose true

let suite =

  "suite">:::
  [
    "test1" >:: test_file "test1.smt" "sat\ncard!1 = 2\ny = 2\nx = 3\n";
    "test2" >:: test_file "test2.smt" "unsat\n";
    "test3" >:: test_file "test3.smt" "sat\n";
    "test_quant_sum" >:: test_file "test_quant_sum.smt" "sat\n";
    "test_sum" >:: test_file "test_sum.smt" "sat\n";
  ]
;;


let () =

  run_test_tt_main suite

