open Smtlib
open OUnit2
open Theory_model
open Arith_array_language

let test_domain_neg _ =
  let open LA_SMT in
  let a_ctx = LA_SMT.Arrays.new_ctx LA_SMT.fresh_var_array LA_SMT.ensure_var_exists in
  let dom = [(LA_SMT.Arrays.mk_full_subdiv a_ctx (Ninf, Pinf), (1, 1, [0])), (Ninf, Pinf)] in
  assert_equal (LA_SMT.domain_neg (new_context ()) dom) [];
  let dom = [(LA_SMT.Arrays.mk_full_subdiv a_ctx (Ninf, Expr (IValue 6)), (1, 1, [0])), (Ninf, Expr (IValue 6))] in
  let dom_neg = domain_neg (new_context ()) dom in
  assert_equal (List.length dom_neg) 1;
  assert_equal  (snd @@ List.hd @@ dom_neg) (Expr (IValue 6), Pinf);
  let interv = (Expr (IValue 8), Pinf) in
  let dom = dom @ [(LA_SMT.Arrays.mk_full_subdiv a_ctx interv, (1, 1, [0])), interv] in
  let dom_neg = domain_neg (new_context ()) dom in
  assert_equal (List.length dom_neg) 1;
  assert_equal  (snd @@ List.hd @@ dom_neg) (Expr (IValue 6), Expr (IValue 8));
  ()

let test_array_solver _ =
  let open LA_SMT in
  let module Solver = Array_solver in
  LA_SMT.Variable_manager.use_var (Array(Range(Ninf, Pinf), Bool)) "a";
  LA_SMT.Variable_manager.use_var (Array(Range(Ninf, Pinf), Bool)) "b";
  LA_SMT.Variable_manager.use_var (Array(Range(Ninf, Pinf), Bool)) "c";
  let a = Array_term("a", TBool) in
  let b = Array_term("b", TBool) in
  let ctx, dis = Solver.context_from_equality [AEquality(a, b)] (function
      | Array_bool_equality(AEquality(e, f)) when e = a && f = b -> true
      | _ -> assert false) in
  assert_equal (List.length dis) 0;
  assert_equal (Solver.get_array_at ctx a (IValue 0) false = Array_access (b, IValue 0, false) ||
   Solver.get_array_at ctx b (IValue 0) false = Array_access (a, IValue 0, false)) true;
  let ctx, dis = Solver.context_from_equality [AEquality(a, b)] (function
      | Array_bool_equality(AEquality(e, f)) when e = a && f = b -> false
      | _ -> assert false) in
  assert_equal (List.length dis) 0;
  assert_equal (Solver.get_array_at ctx a (IValue 0) false) (Array_access (a, IValue 0, false));
  let ctx, dis = Solver.context_from_equality [ExtEquality(a, b)] (function
      | Array_bool_equality(ExtEquality(e, f)) when e = a && f = b -> false
      | _ -> assert false) in
  assert_equal dis ([a, b, false]);
  let ctx, dis = Solver.context_from_equality [ExtEquality(a, b)] (function
      | Array_bool_equality(ExtEquality(e, f)) when e = a && f = b -> false
      | _ -> assert false) in
  ()


let test_counting_solver _ =
  let open LA_SMT in
  let open Arrays in
  let a_ctx = Arrays.new_ctx fresh_var_array ensure_var_exists in
  let subdiv = Arrays.mk_full_subdiv a_ctx (Ninf, Pinf)
               |> Arrays.equality_array a_ctx (Array_term("a", TBool)) true
  in
  let subdiv2 = Arrays.mk_full_subdiv a_ctx (Ninf, Pinf) in
  begin
    match subdiv with 
    | Some { name = "a"; left_tree = None; right_tree = None; left_selection = Unselected; right_selection = Selected; _ } -> ()
    | _ -> assert false
  end;
  begin
    match subdiv2 with 
    | Some { name = "a"; left_tree = None; right_tree = None; left_selection = Dont_care; right_selection = Dont_care; _ } -> ()
    | _ -> assert false
  end;
  let subdiv2 = Arrays.equality_array a_ctx (Array_term("b", TBool)) true subdiv2 in
  begin
    match subdiv2 with 
    | Some { name = "a";
             left_tree = Some
                 { name = "b";
                   right_tree = None;
                   left_tree = None;
                   left_selection = Unselected;
                   right_selection = Selected;
                   _ };
             right_tree = Some
                 { name = "b";
                   right_tree = None;
                   left_tree = None;
                   left_selection = Unselected;
                   right_selection = Selected;
                   _ };
             _ } -> ()
    | _ -> assert false
  end;
  let ctx = new_context () in
  let dom1 = [(subdiv, (1, 1, [0])), (Ninf, Pinf)] in
  let dom2 = [(subdiv2, (1, 1, [0])), (Ninf, Pinf)] in
  let dom  = domain_neg ctx dom1 in
  begin
  match dom with
  | [(subdiv, _), (Ninf, Pinf)] ->
    begin
      match subdiv with 
      | Some {
          name = "a";
          left_tree = None;
          right_tree = None;
          left_selection = Selected;
          right_selection = Unselected; _ } -> ()
      | _ -> assert false
    end

  | _ -> assert false
  end;
  let dom  = domain_neg ctx dom2 in
  begin
  match dom with
  | [(subdiv, _), (Ninf, Pinf)] ->
    begin
      match subdiv with 
      | Some { name = "a";
               left_tree = Some
                   { name = "b";
                     right_tree = None;
                     left_tree = None;
                     left_selection = Selected;
                     right_selection = Unselected;
                     _ };
               right_tree = Some
                   { name = "b";
                     right_tree = None;
                     left_tree = None;
                     left_selection = Selected;
                     right_selection = Unselected;
                     _ };
               _ } -> ()
      | _ -> assert false
    end

  | _ -> assert false
  end;
  let dom  = make_domain_intersection ctx (domain_neg ctx dom1) (domain_neg ctx dom2) in
  begin
  match dom with
  | [(subdiv, _), (Ninf, Pinf)] ->
    begin
      match subdiv with 
      | Some { name = "a";
               left_tree = Some
                   { name = "b";
                     right_tree = None;
                     left_tree = None;
                     left_selection = Selected;
                     right_selection = Unselected;
                     _ };
               right_tree = Some
                   { name = "b";
                     right_tree = None;
                     left_tree = None;
                     left_selection = Unselected;
                     right_selection = Unselected;
                     _ };
               _ } -> ()
      | _ -> Arrays.print_tree subdiv; assert false
    end

  | _ -> assert false
  end;
  let dom = make_domain_union ctx dom1 dom2 in
  match dom with
  | [(subdiv, _), (Ninf, Pinf)] ->
    begin
      match subdiv with 
      | Some { name = "a";
               left_tree = Some
                   { name = "b";
                     right_tree = None;
                     left_tree = None;
                     left_selection = Unselected;
                     right_selection = Selected;
                     _ };
               right_tree = Some
                   { name = "b";
                     right_tree = None;
                     left_tree = None;
                     left_selection = Selected;
                     right_selection = Selected;
                     _ };
               _ } -> ()
      | _ -> assert false
    end

  | _ -> assert false

let test1 = "suite" >::: [ "test_domain_neg" >:: test_domain_neg;
                           "test_array_solver" >:: test_array_solver;
                           "test_counting_solver" >:: test_counting_solver;
                         ]


let () = run_test_tt_main test1

