open Utils
open Options
open Formula

module type T = sig
  module Formula : F
  open Formula
  type model
  type domain
  type interval_manager

  exception Unsat

  val new_interval_manager: unit -> interval_manager
  val solve: (model -> 'a) -> 'a
  val solve_formula: expr -> (model -> 'a) -> 'a
  val expr_to_domain: interval_manager -> model -> string -> expr -> domain
  val implies_card: interval_manager -> string -> domain -> unit
  val implies_constraints: interval_manager -> unit
  val solve_assuming: interval_manager -> (model -> 'a) -> 'a
  val domain_to_str: domain -> string

end

let very_verbose = false

(* This theory uses an external solver to solve basic arithmetic
 * and real stuff, and then sends new constraints to the solver for
 * cardinality and arrays. *)
module LA_SMT = struct

  exception Unknown_answer of string
  exception Unknown_sort of string
  exception Unsat
  exception TypeCheckingError of string * string
  exception Bad_interval

  module Arrays = Array_solver.Array_solver
  type model = Arith_array_language.model
  open Arith_array_language


  type arrayed_interval = Arrays.array_subdivision * interval
  type arrayed_domain = arrayed_interval list
  type interval_manager = Interval_manager.interval_manager

  type domain = arrayed_domain


  let domain_to_str d =
    List.map (fun (s, i) ->
         (inf_interval_to_string i)) d
    |> String.concat ", "

  let print_domain_debug l =
    if List.length l > 0 then
    List.iter (fun (s, i) ->
        Arrays.print_tree s;
        Format.eprintf "%s@." (inf_interval_to_string i);) l
    else
      Format.eprintf "(empty domain)@."


  module Formula = IFormula(struct
      type texpr = rel
      let texpr_to_smt = rel_to_smt
      type tsort = sort
    end)

  module Variable_manager = Variable_manager.Variable_manager(Formula)

  open Formula

  type expr = Formula.expr

  type context = model * Interval_manager.interval_manager * Arrays.array_ctx
  
  let array_ctx (_, _, ctx) =
    ctx

  let model_ctx (m, _, _) = m

  let interval_manager (_, i, _) =
    (i:Interval_manager.interval_manager)

  let assumptions_to_expr l =
    if l = [] then Theory_expr (Bool(BValue(true)))
        else List.fold_left (fun l s ->
        And(l, Theory_expr(s))) (Theory_expr (List.hd l)) (List.tl l)

  let solver_in, solver_out =
    let a, b = Unix.open_process solver_command
    in ref a, ref b

  let send_to_solver s =
    output_string !solver_out s;
    if verbose then
      Format.printf " -> %s@." s;
    output_string !solver_out "\n";
    flush !solver_out
  
  let assert_formula str =
    "(assert " ^ str ^ ")"
    |> send_to_solver


  let define_new_variable =
    React.iter Variable_manager.new_variables (fun (name, mytype) ->
        match mytype with
        | Int ->
          send_to_solver @@ "(declare-fun " ^ name ^ " () Int)"
        | Bool ->
          send_to_solver @@ "(declare-fun " ^ name ^ " () Bool)"
        | Real ->
          send_to_solver @@ "(declare-fun " ^ name ^ " () Real)"
        | Range(Expr a, Expr b) ->
          send_to_solver @@ "(declare-fun " ^ name ^ " () Int)";
          send_to_solver @@ Format.sprintf "(assert (and (<= %s %s) (< %s %s)))" (term_to_string a) name name (term_to_string b)
        | Array(Range(_, _), Bool) -> ()
        | e -> failwith "Too complex array type")


  let fresh_var_array =
    let v = ref 0 in
    fun () ->
      incr v;
      let name = "array!" ^ (string_of_int !v) in
      Variable_manager.use_var Int name; name

  let ensure_var_exists ?constraints:(constr=None) a =
    try
      ignore (List.find (fun (s, n) -> n = a) !Variable_manager.vars); ()
    with
    | Not_found -> 
      Variable_manager.use_var Int a;
      match constr with
      | None -> ()
      | Some s -> assert_formula (rel_to_smt s)
  
  let my_array_ctx = ref (Arrays.new_ctx fresh_var_array ensure_var_exists)

  let reset_solver () =
    close_in !solver_in; close_out !solver_out;
    let a, b = Unix.open_process solver_command
    in solver_in := a; solver_out := b; Variable_manager.reset ();
    my_array_ctx := Arrays.new_ctx fresh_var_array ensure_var_exists



  let rec is_sat () =
    let l = input_line !solver_in in
    if l <> "" then
      match l with
      | "sat" -> true
      | "unsat" -> false
      | a -> raise (Unknown_answer a)
    else is_sat ()

  (* true if this variable is seen by the underlying solver (such as yices). For instance,
   * at this moment, arrays are not seen. *)
  let var_is_raw (sort, name) = match sort with
    | Int | Bool | Range(_) | Real -> true
    | _ -> false

  let get_model () =
    send_to_solver @@ Format.sprintf "(get-value (%s))" (List.filter var_is_raw !(Variable_manager.vars) |> List.map snd |> String.concat " ");
    let open Lisp in
    let get_var lisp =
      match lisp with
      | Lisp_rec(Lisp_string b :: Lisp_int v :: []) ->
        (b, VInt v)
      | Lisp_rec(Lisp_string b :: Lisp_rec(Lisp_string "-" :: Lisp_int v :: []) :: []) ->
        (b, VInt(-v))
      | Lisp_rec(Lisp_string b :: Lisp_true :: []) ->
        (b, VBool true)
      | Lisp_rec(Lisp_string b :: Lisp_false :: []) ->
        (b, VBool false)
      | a -> raise (Unknown_answer ("couldn't understand that \"" ^ lisp_to_string a ^ "\""))
    in
    let lisp = !solver_in
               |> Lexing.from_channel
               |> Lisp_parser.prog Lisp_lexer.read in
    match lisp with
    | Lisp_rec(l) ->
      begin
        try
          List.map get_var l
        with
        | Unknown_answer (a) ->
          raise (Unknown_answer ("couldn't understand \n\t" ^ lisp_to_string lisp ^ "\n and more specifically:\n" ^ a))
      end
    | _ -> raise (Unknown_answer ("couldn't understand root "))


  let solve cont =
    send_to_solver "(check-sat)";
    if is_sat () then
      cont @@ get_model ()
    else
      raise Unsat

  let push f =
    send_to_solver "(push 1)";
    let old_v = !(Variable_manager.vars) in
    let old_array_ctx = Arrays.copy_ctx !my_array_ctx in
    f ();
    Variable_manager.vars := old_v;
    my_array_ctx := old_array_ctx;
    send_to_solver "(pop 1)"

  let solve_in_context f cont =
    send_to_solver "(push 1)";
    try
      begin
        f ();
        solve (fun m ->
            let a = cont m in
            send_to_solver "(pop 1)"; a
          )
      end
    with
    | Unsat ->
      begin
        send_to_solver "(pop 1)";
        raise Unsat
      end



  let solve_formula expr cont =
    solve_in_context (fun () ->
        assert_formula @@ expr_to_smt expr
      )
      cont

  let print_model stdout m =
    List.iter (fun (b, v) ->
        match v with
        | VBool(t) ->  Printf.fprintf stdout "%s = %b\n" b t
        | VInt(v) ->
          if(String.length b <= 5 || String.sub b 0 5 <> "card!") then Printf.fprintf stdout "%s = %d\n" b v)
      m

  let rec seq (a, b) =
    if a = b then [a]
    else a :: seq (a+1, b)

  let implies_constraints interval_manager  =
    let rec ensure_arrays a = function
      | [] -> []
      | t::q ->
            Arrays.(constraints_subdiv !my_array_ctx (term_to_uid a ^ "!" ^ term_to_uid t) (interval_to_string (Expr a, Expr t)) !my_array_ctx.hyps :: ensure_arrays t q)
    in
    let ordering = interval_manager#ordering in
    let constraint_sum =
      if List.length ordering >= 2 then
        ensure_arrays (List.hd ordering) (List.tl ordering)
        |> List.concat
        |> List.fold_left (fun l s ->
            And(l, Theory_expr(s))) (Theory_expr(Bool(BValue(true))))
      else
        Theory_expr(Bool(BValue(true)))
    in
    if very_verbose then
      interval_manager#print_ordering;
    let smt_assumptions = assumptions_to_expr interval_manager#assumptions |> expr_to_smt in
    Format.sprintf "(=> %s %s)" smt_assumptions (expr_to_smt constraint_sum) |> assert_formula

  let implies_card interval_manager cardinality_variable domain =
    let smt_assumptions = assumptions_to_expr interval_manager#assumptions |> expr_to_smt in
    begin
      try
        domain
        |> List.map (fun (sub, interval) ->
            if Arrays.is_top sub then
              [interval_to_string interval]
            else
              Arrays.array_sub_to_string !my_array_ctx (interval_manager#get_slices_of_ordering interval) sub interval
          )
        |> List.concat
        |> List.filter ((<>) "0")
        |> String.concat " "
        |> (fun s ->
            if s = "" then "0"
            else s)
        |> Format.sprintf "(+ %s 0)"
        |> (fun res ->
            Theory_expr(IEquality(IVar(cardinality_variable, 0), IVar(res, 0)))
          )
        |> (fun resulting_expression ->
            Format.sprintf "(=> %s %s)"
              smt_assumptions
              (expr_to_smt resulting_expression)
          )
      with
      | Unbounded_interval ->
        Format.sprintf "(=> %s false)" smt_assumptions

    end
    |> assert_formula


  let solve_assuming im cont =
    solve_in_context (fun () ->
        assumptions_to_expr im#assumptions |> expr_to_smt |> assert_formula)
      cont

  let get_val_from_model: type a. model -> a term -> a = fun model -> function
    | IVar(a, i) ->
      begin
        try
        let k = snd @@ List.find (fun (v,b) -> v = a) model in
        match k with
        | VInt(k) -> k+i
        | _ -> raise (TypeCheckingError (a, "int"))
        with
        | Not_found -> failwith ("couldn't get variable " ^ a ^ "from model")
      end
    | IValue(i) -> i
    | BValue(b) -> b
    | BVar(a, modi) ->
      begin
        let k = snd @@ List.find (fun (v,b) -> v = a) model in
        match k with
        | VBool(k) -> (modi && k) || (not modi && not k)
        | _ -> raise (TypeCheckingError (a, "bool"))
      end
    | Array_access(Array_term(a), _, _) ->
      failwith (Format.sprintf "trying to get an array value from a model - should not happen: %s@." a)
    | Array_term(_) ->  failwith "trying to get an array value from a model - should not happen"

  let make_domain_intersection ctx (d1:arrayed_domain) (d2:arrayed_domain) =
    let oracle a b =
      compare (get_val_from_model (model_ctx ctx) a) (get_val_from_model (model_ctx ctx) b)
    in
    if very_verbose then
      (Format.eprintf "from@."; print_domain_debug d1; print_domain_debug d2);
    let d = (interval_manager ctx)#intersection_domains oracle (Arrays.array_subdivision_intersection (array_ctx ctx)) d1 d2 in
    if very_verbose then
        (Format.eprintf "to@."; print_domain_debug d); 
    d

  let domain_neg a d =
    let c = array_ctx a in
    let i = interval_manager a in
    i#complementary_domain d (Arrays.array_subdivision_negation c) (Arrays.mk_full_subdiv c) Arrays.is_top

  let make_domain_union a (d1:arrayed_domain) (d2:arrayed_domain) =
    let d  = make_domain_intersection a (domain_neg a d1) (domain_neg a d2) in
    a, domain_neg a d

  let rec make_domain_from_expr var_name ctx e =
    let model, assum, actx = ctx in
    let oracle a b =
      compare (get_val_from_model (model_ctx ctx) a) (get_val_from_model (model_ctx ctx) b)
    in
    let array_init = Arrays.mk_full_subdiv actx (Ninf, Pinf) in
    match e with
    | Greater(IVar(v, n), a) when v = var_name -> ctx, [array_init, (Expr (minus n a), Pinf)]
    | Greater(a, IVar(v, n)) when v = var_name -> ctx, [array_init, (Ninf, Expr(minus (n-1) a))]
    | IEquality(a, IVar(v, n)) when v = var_name -> ctx, [array_init, (Expr(minus n a), Expr(minus (n-1) a))]
    | IEquality(IVar(v, n), a) when v = var_name -> ctx, [array_init, (Expr(minus n a), Expr(minus (n-1) a))]
    | Greater(a, b) ->
      if a = b then
        ctx, [array_init, (Ninf, Pinf)]
      else
        let a_val = get_val_from_model model a and
        b_val = get_val_from_model model b in
        if a_val >= b_val then
          begin
            assum#assume_oracle oracle (Greater(a, b));
            ctx, [array_init, (Ninf, Pinf)]
          end
        else
          begin
            assum#assume_oracle oracle (Greater(b, plus_one b));
            ctx, []
          end
    | IEquality(a, b) ->
      if a = b then
        ctx, [array_init, (Ninf, Pinf)]
      else
        let a_val = get_val_from_model model a and
        b_val = get_val_from_model model b in
        if a_val = b_val then
          begin
            assum#assume_oracle oracle (IEquality(a, b));
            ctx, [array_init, (Ninf, Pinf)]
          end
        else if a_val > b_val then
          begin
            assum#assume_oracle oracle (Greater(a, plus_one b));
            ctx, []
          end
        else
          begin
            assum#assume_oracle oracle (Greater(b, plus_one a));
            ctx, []
          end
    | BEquality(Array_access(tab1, index1, neg1), Array_access(tab2, index2, neg2)) ->
      if index1 <> IVar(var_name, 0) then
        failwith (Format.sprintf "incorrect index %s" (term_to_string index1));
      if index2 <> IVar(var_name, 0) then
        failwith (Format.sprintf "incorrect index %s" (term_to_string index2));
      ctx, [Arrays.equality_arrays actx tab1 tab2 (not @@ xor neg1 neg2) array_init, (Ninf, Pinf)]
    | BEquality(Array_access(tab, index, neg), a) ->
      assert (index = IVar(var_name, 0)); 
      let a_val = get_val_from_model model a in
      if a_val then
        assum#assume((Bool(a)):rel)
      else
        assum#assume(Bool(not_term a));
      ctx, [Arrays.equality_array actx tab (xor (not neg) a_val) array_init, (Ninf, Pinf)]
    | BEquality(a, Array_access(tab, index, neg)) ->
      make_domain_from_expr var_name ctx (BEquality(Array_access(tab, index, neg), a))
    | BEquality(a, b) ->
      let a_val = get_val_from_model model a and
      b_val = get_val_from_model model b in
      if a_val = b_val then
        begin
          assum#assume (BEquality(a, b));
          ctx, [array_init, (Ninf, Pinf)]
        end
      else
        begin
          assum#assume (BEquality(not_term a, b));
          ctx, []
        end
    | Bool(Array_access(tab, index, neg)) ->
      (assert (index = IVar(var_name, 0));
       ctx, [Arrays.equality_array actx tab neg array_init, (Ninf, Pinf)])
    | Bool(a) ->
      let a_val = get_val_from_model model a in
      if a_val then
        begin
          assum#assume (Bool(a));
          ctx, [array_init, (Ninf, Pinf)]
        end
      else
        begin
          assum#assume (Bool(not_term a));
          ctx, []
        end

  let expr_to_domain im model var_name expr =
    let rec expr_to_domain_aux a expr =
      match expr with
      | And(e1, e2) ->
        let a, d1 = expr_to_domain_aux a e1 in
        let a, d2 = expr_to_domain_aux a e2 in
        a, make_domain_intersection a d1 d2
      | Or(e1, e2) ->
        let a, d1 = expr_to_domain_aux a e1 in
        let a, d2 = expr_to_domain_aux a e2 in
        make_domain_union a d1 d2
      | Not(e) ->
        let a, d = expr_to_domain_aux a e in
        a, domain_neg a d
      | Theory_expr(e) ->
        let a, d = make_domain_from_expr var_name a e in
        a, d
    in
      let ctx, d = expr_to_domain_aux (model, im, !my_array_ctx) expr
      in d

  let new_interval_manager () = new Interval_manager.interval_manager

end
