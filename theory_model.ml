open Utils
open Options
open Formula

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
  open Arith_array_language


  type congruence = int * int list (* modulo * remainder *)
  type arrayed_interval = (Arrays.array_subdivision * congruence) * interval
  type arrayed_domain = arrayed_interval list
  type interval_manager = Interval_manager.interval_manager

  type domain = arrayed_domain


  let domain_to_string d =
    List.map (fun (s, i) ->
         (inf_interval_to_string i)) d
    |> String.concat ", "

  let print_domain_debug l =
    if List.length l > 0 then
      List.iter (fun ((s, (m, r)), i) ->
          Arrays.print_tree s;
          Format.eprintf "%s [%d] = (%s)@." (inf_interval_to_string i) m (List.map string_of_int r |> String.concat ", ");) l
    else
      Format.eprintf "(empty domain)@."

  let sort_for_construct _ =
    Int

  module Formula = IFormula(struct
      type texpr = rel
      let texpr_to_smt = rel_to_smt
      type tsort = sort
    end)

  module Variable_manager = Variable_manager.Variable_manager(Formula)

  open Formula

  type expr = Formula.expr

  (* hum, there is one model which should be removed here *)
  type premodel = {interval_manager:Interval_manager.interval_manager; array_ctx: Arrays.array_ctx; model: Arith_array_language.model; }
  type abstract_model = premodel
  type model = Arith_array_language.model
  type construct = { quantified_var:string; expr:expr; quantified_sort: sort; }
  
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
  
  let assert_formula_str str =
    "(assert " ^ str ^ ")"
    |> send_to_solver


  let define_new_variable =
    Variable_manager.(React.iter new_variables (fun var ->
        let name = var.name in
        match var.sort with
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
        | e -> failwith "Too complex array type"))


  let fresh_var_array =
    let v = ref 0 in
    fun () ->
      incr v;
      let name = "array!" ^ (string_of_int !v) in
      Variable_manager.use_var Int name; name

  let ensure_var_exists ?constraints:(constr=None) a =
    try
      ignore Variable_manager.(List.find (fun v -> v.name = a) !vars); ()
    with
    | Not_found -> 
      Variable_manager.use_var Int a;
      match constr with
      | None -> ()
      | Some s -> assert_formula_str (rel_to_smt s)
  
  let reset_solver () =
    close_in !solver_in; close_out !solver_out;
    let a, b = Unix.open_process solver_command
    in solver_in := a; solver_out := b; Variable_manager.reset ()



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
  let var_is_raw v =
    match Variable_manager.(v.sort) with
    | Int | Bool | Range(_) | Real -> true
    | _ -> false

  let get_model () =
    let open Variable_manager in
    send_to_solver @@ Format.sprintf "(get-value (%s))" (List.filter var_is_raw !vars |> List.map (fun v -> v.name) |> String.concat " ");
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

  (* ok, so, ATM creating a new array context every time is way more costly, maybe it is a good heuristic to process
   * the first cardinalities first, I have no idea *)
  let a = ref (Arrays.new_ctx fresh_var_array ensure_var_exists)
  let new_array_ctx () = !a 

  let push f =
    send_to_solver "(push 1)";
    let old_v = !(Variable_manager.vars) in
    let open Arrays in
    let sub = array_subdivision_duplicate !a.hyps in
    f ();
    Variable_manager.vars := old_v;
    !a.hyps <- sub;
    send_to_solver "(pop 1)"

  let print_model m =
    List.iter (fun (b, v) ->
        match v with
        | VBool(t) ->  Printf.fprintf stdout "%s = %b\n" b t
        | VInt(v) ->
          if(String.length b <= 5 || String.sub b 0 5 <> "card!") then Printf.fprintf stdout "%s = %d\n" b v)
      m

  let rec seq (a, b) =
    if a = b then [a]
    else a :: seq (a+1, b)
  
  let get_val_from_model:type a. Arith_array_language.model -> a term -> a = fun model ->
    function
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


  let ensure_domains_consistency premodel (all_domains:domain list) =
    let interval_manager = premodel.interval_manager in
    let model = premodel.model in
    let oracle a b =
      compare (get_val_from_model model a) (get_val_from_model model b)
    in
    let is_top = fun (a, (m, r)) ->
        Arrays.is_top a && (m = List.length r)
    in
    interval_manager#add_to_ordering is_top oracle (List.concat all_domains);
    interval_manager#fix_ordering oracle;
    let rec ensure_arrays a = function
      | [] -> []
      | t::q ->
            Arrays.(constraints_subdiv premodel.array_ctx (term_to_uid a ^ "!" ^ term_to_uid t) (interval_to_string (Expr a, Expr t)) premodel.array_ctx.hyps :: ensure_arrays t q)
    in
    let ordering = interval_manager#ordering |> List.map List.hd in
    if very_verbose then
      interval_manager#print_ordering;
    if List.length ordering >= 2 then
      let all_constraints = ensure_arrays (List.hd ordering) (List.tl ordering)
                            |> List.concat
      in
      match all_constraints with
      | t::q ->
        let constraint_sum = List.fold_left (fun l s -> And(l, Theory_expr(s))) (Theory_expr t) q in
        let smt_assumptions = assumptions_to_expr interval_manager#assumptions |> expr_to_smt in
        Format.sprintf "(=> %s %s)" smt_assumptions (expr_to_smt constraint_sum) |> assert_formula_str
      | [] -> ()

  let ensure_domain premodel cardinality_variable domain =
    let interval_manager = premodel.interval_manager in
    let smt_assumptions = assumptions_to_expr interval_manager#assumptions |> expr_to_smt in
    begin
      try
        domain
        |> List.map (fun ((sub, congruence), interval) ->
            if Arrays.is_top sub then
              [interval_to_string interval]
            else
              Arrays.array_sub_to_string premodel.array_ctx (interval_manager#get_slices_of_ordering interval) sub interval
          )
        |> List.concat
        |> List.filter ((<>) "0")
        |> (fun l ->
          match List.length l with
            | 0 -> "0"
            | 1 -> List.hd l
            | _ ->
              String.concat " " l
              |> Format.sprintf "(+ %s)")
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
    |> assert_formula_str


  let make_domain_intersection premodel (d1:arrayed_domain) (d2:arrayed_domain) =
    let oracle a b =
      compare (get_val_from_model premodel.model a) (get_val_from_model premodel.model b)
    in
    if very_verbose then
      (Format.eprintf "from@."; print_domain_debug d1; print_domain_debug d2);
    let d = premodel.interval_manager#intersection_domains oracle
        (fun (arrays1, congruence1) (arrays2, congruence2) ->
           Arrays.array_subdivision_intersection premodel.array_ctx arrays1 arrays2, congruence1) d1 d2 in
    if very_verbose then
        (Format.eprintf "to@."; print_domain_debug d); 
    d

  let domain_neg premodel d =
    let c = premodel.array_ctx in
    let i = premodel.interval_manager in
    i#complementary_domain d
      (fun (arrays1, congruence1) ->
        Arrays.array_subdivision_negation c arrays1, congruence1)
      (fun i ->
         Arrays.mk_full_subdiv c i, (1, [0]))
      (fun (a, (m, r)) ->
        Arrays.is_top a && (m = List.length r))

  let make_domain_union a (d1:arrayed_domain) (d2:arrayed_domain) =
    let d  = make_domain_intersection a (domain_neg a d1) (domain_neg a d2) in
    domain_neg a d

  let rec make_domain_from_expr var_name premodel e =
    let model = premodel.model in
    let actx = premodel.array_ctx in
    let assum = premodel.interval_manager in
    let oracle a b =
      compare (get_val_from_model model a) (get_val_from_model model b)
    in
    let array_init = Arrays.mk_full_subdiv actx (Ninf, Pinf) in
    let auxiliary_constraints = array_init, (1, [0]) in
    match e with
    | Greater(IVar(v, n), a) when v = var_name -> [auxiliary_constraints, (Expr (minus n a), Pinf)]
    | Greater(a, IVar(v, n)) when v = var_name -> [auxiliary_constraints, (Ninf, Expr(minus (n-1) a))]
    | IEquality(a, IVar(v, n)) when v = var_name -> [auxiliary_constraints, (Expr(minus n a), Expr(minus (n-1) a))]
    | IEquality(IVar(v, n), a) when v = var_name -> [auxiliary_constraints, (Expr(minus n a), Expr(minus (n-1) a))]
    | Greater(a, b) ->
      if a = b then
        [auxiliary_constraints, (Ninf, Pinf)]
      else
        let a_val = get_val_from_model model a and
        b_val = get_val_from_model model b in
        if a_val >= b_val then
          begin
            assum#assume_oracle oracle (Greater(a, b));
            [auxiliary_constraints, (Ninf, Pinf)]
          end
        else
          begin
            assum#assume_oracle oracle (Greater(b, plus_one b));
            []
          end
    | IEquality(a, b) ->
      if a = b then
        [auxiliary_constraints, (Ninf, Pinf)]
      else
        let a_val = get_val_from_model model a and
        b_val = get_val_from_model model b in
        if a_val = b_val then
          begin
            assum#assume_oracle oracle (IEquality(a, b));
            [auxiliary_constraints, (Ninf, Pinf)]
          end
        else if a_val > b_val then
          begin
            assum#assume_oracle oracle (Greater(a, plus_one b));
            []
          end
        else
          begin
            assum#assume_oracle oracle (Greater(b, plus_one a));
            []
          end
    | BEquality(Array_access(tab1, index1, neg1), Array_access(tab2, index2, neg2)) ->
      if index1 <> IVar(var_name, 0) then
        failwith (Format.sprintf "incorrect index %s" (term_to_string index1));
      if index2 <> IVar(var_name, 0) then
        failwith (Format.sprintf "incorrect index %s" (term_to_string index2));
      [(Arrays.equality_arrays actx tab1 tab2 (not @@ xor neg1 neg2) array_init, (1, [0])), (Ninf, Pinf)]
    | BEquality(Array_access(tab, index, neg), a) ->
      assert (index = IVar(var_name, 0)); 
      let a_val = get_val_from_model model a in
      if a_val then
        assum#assume((Bool(a)):rel)
      else
        assum#assume(Bool(not_term a));
      [(Arrays.equality_array actx tab (xor (not neg) a_val) array_init, (1, [0])), (Ninf, Pinf)]
    | BEquality(a, Array_access(tab, index, neg)) ->
      make_domain_from_expr var_name premodel (BEquality(Array_access(tab, index, neg), a))
    | BEquality(a, b) ->
      let a_val = get_val_from_model model a and
      b_val = get_val_from_model model b in
      if a_val = b_val then
        begin
          assum#assume (BEquality(a, b));
          [auxiliary_constraints, (Ninf, Pinf)]
        end
      else
        begin
          assum#assume (BEquality(not_term a, b));
           []
        end
    | Bool(Array_access(tab, index, neg)) ->
      (assert (index = IVar(var_name, 0));
       [(Arrays.equality_array actx tab neg array_init, (1, [0])), (Ninf, Pinf)])
    | Bool(a) ->
      let a_val = get_val_from_model model a in
      if a_val then
        begin
          assum#assume (Bool(a));
          [auxiliary_constraints, (Ninf, Pinf)]
        end
      else
        begin
          assum#assume (Bool(not_term a));
          []
        end

  let build_domain_for_construct premodel cardinality =
    let rec expr_to_domain_aux a expr =
      match expr with
      | And(e1, e2) ->
        let d1 = expr_to_domain_aux a e1 in
        let d2 = expr_to_domain_aux a e2 in
        make_domain_intersection a d1 d2
      | Or(e1, e2) ->
        let d1 = expr_to_domain_aux a e1 in
        let d2 = expr_to_domain_aux a e2 in
        make_domain_union a d1 d2
      | Not(e) ->
        let d = expr_to_domain_aux a e in
        domain_neg a d
      | Theory_expr(e) ->
        make_domain_from_expr cardinality.quantified_var a e
    in
      expr_to_domain_aux premodel cardinality.expr

  let new_interval_manager () = new Interval_manager.interval_manager
  
  let new_context () = { model = []; interval_manager = new_interval_manager (); array_ctx =  new_array_ctx (); }

  let build_full_model (m:abstract_model) = m.model

  let build_premodel () =
    send_to_solver "(check-sat)";
    if is_sat () then
      { model = get_model (); interval_manager = new_interval_manager (); array_ctx = new_array_ctx (); }
    else
      raise Unsat
  
  let build_abstract_model_in_context f =
    send_to_solver "(push 1)";
    try
      begin
        f ();
        let m = build_premodel () in
        send_to_solver "(pop 1)"; m
      end
    with
    | Unsat ->
      begin
        send_to_solver "(pop 1)";
        raise Unsat
      end

  let build_abstract_model premodel =
    let im = premodel.interval_manager in
    build_abstract_model_in_context (fun () ->
        assumptions_to_expr im#assumptions |> expr_to_smt |> assert_formula_str)

  let assert_formula e =
    expr_to_smt e |> assert_formula_str
  


end
