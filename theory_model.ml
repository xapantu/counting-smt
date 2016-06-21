open Utils
open Options
open Formula

module type T = sig
  module Formula : F
  open Formula
  type model
  type domain

  exception Unsat

  val solve: (model -> 'a) -> 'a
  val solve_formula: expr -> (model -> 'a) -> 'a
  val expr_to_domain: model -> string -> expr -> (domain * assumptions)
  val implies_card: assumptions -> string -> domain -> unit
  val solve_assuming: assumptions -> (model -> 'a) -> 'a
  val domain_to_str: domain -> string

end

module LA_SMT = struct

  include Arith_array_language

  exception Unknown_answer of string
  exception Unsat
  exception TypeCheckingError of string

  module Arrays = Array_solver.Array_solver

  type arrayed_interval = Arrays.array_subdivision * interval
  type arrayed_domain = arrayed_interval list

  type domain = arrayed_domain

  let bound_inf_to_string = function
    | Ninf | Pinf -> "inf"
    | Expr e -> term_to_string e


  let inf_interval_to_string (l, u) =
    "[" ^ bound_inf_to_string l ^ ", " ^ bound_inf_to_string u ^ "]"
  
  let domain_to_str d =
    d
    |> List.map (fun (s, i) ->
         (inf_interval_to_string i))
    |> String.concat ", "


  module Formula = IFormula(struct
      type texpr = rel
      let texpr_to_smt = rel_to_smt
      type tsort = sort
    end)

  open Formula

  type context = model * Interval_manager.interval_manager * Arrays.array_ctx

  let vars = ref []
  let range = Hashtbl.create 10
  let get_range = Hashtbl.find range

  let solver_in, solver_out =
    let a, b = Unix.open_process solver_command
    in ref a, ref b

  let send_to_solver s =
    output_string !solver_out s;
    if verbose then
      Format.printf " -> %s@." s;
    output_string !solver_out "\n";
    flush !solver_out

  let use_var name = function
    | Int ->
      let () = vars := (Int, name) :: !vars in
      send_to_solver @@ "(declare-fun " ^ name ^ " () Int)"
    | Bool ->
      let () = vars := (Bool, name) :: !vars in
      send_to_solver @@ "(declare-fun " ^ name ^ " () Bool)"
    | Array(Range(_, _), Bool) as e ->
      vars := (e, name) :: !vars
    | _ -> failwith "Too complex array type"


  let v = ref 0
  let fresh_var_array () =
    incr v;
    let name = "array!" ^ (string_of_int !v) in
    use_var name Int; name
  
  let my_array_ctx = ref (Arrays.new_ctx fresh_var_array)

  let new_range: string -> bound -> bound -> unit =
    fun name b1 b2 ->
      Hashtbl.add range name (Range (b1, b2))

  let domain_cardinality = function
    | [] -> "0"
    | dom -> dom
             |> List.map (fun (s, i) ->
                 Arrays.array_sub_to_string !my_array_ctx s i)
             |> List.fold_left (fun l a -> Format.sprintf "(+ %s %s)" l a) "0"

  let reset_solver () =
    close_in !solver_in; close_out !solver_out;
    let a, b = Unix.open_process solver_command
    in solver_in := a; solver_out := b; vars := [];
    Hashtbl.reset range; my_array_ctx := Arrays.new_ctx fresh_var_array


  let constraints_on_sort sort name = match sort with
    | Int | Bool -> Theory_expr(Bool (BValue true))
    | Range(Expr a, Expr b) -> And(Theory_expr(Greater(b, IVar(name, 1))), Theory_expr(Greater(IVar(name, 0), a)))
    | Range(Ninf, Expr b) -> Theory_expr(Greater(b, IVar(name, 1)))
    | Range(Expr a, Pinf) -> Theory_expr(Greater(IVar(name, 0), a))
    | _ -> assert false

  let use_quantified_var name sort f =
      let () = vars := (sort, name) :: !vars in
      let a = f (constraints_on_sort sort name) in
      let first = ref true in
      let () = vars := List.filter (fun x -> 
          let (a, b) = x in
          if b = name then
            if !first then
              (first := false; false)
            else
              true
          else
            true) !vars in
      assert (not !first);
      a

  let get_sort name =
    fst @@ List.find (fun (s, n) -> name = n) !vars

  let ensure_int name =
    match get_sort name with
    | Int | Range(_) -> ()
    | _ -> raise (TypeCheckingError name)

  let ensure_bool name =
    if get_sort name = Bool then ()
    else raise (TypeCheckingError name)


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
  let var_is_raw (sort, name) =
    sort = Int || sort = Bool

  let get_model () =
    send_to_solver @@ Format.sprintf "(get-value (%s))" (List.filter var_is_raw !vars |> List.map snd |> String.concat " ");
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
    f ();
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



  let assert_formula str =
    "(assert " ^ str ^ ")"
    |> send_to_solver

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


  let implies_card assumptions cardinality_variable domain =
    (*let () = "(=> " ^
             assumptions_to_smt assumptions ^
             begin
               try
                 " (= " ^
                 str ^ " " ^ domain_cardinality domain ^ "))"
               with
               | Unbounded_interval -> " false)"
             end
             |> assert_formula
    in*)
    let () =
      domain
      |> List.map fst
      |> List.map (Arrays.constraints_subdiv !my_array_ctx)
      |> List.iter assert_formula
    in
    let smt_assumptions = assumptions_to_smt assumptions in
    let () =
      begin
        try
          domain
          |> List.map (fun (sub, interval) ->
              if Arrays.is_top sub then
                interval_to_string interval
              else
                Arrays.array_sub_to_string !my_array_ctx sub interval
            )
          |> List.fold_left (fun l s -> "(+ " ^ l ^ " " ^ s ^ ")") "0"
          |> (fun resulting_expression ->
              Format.sprintf "(=> %s (= %s %s))"
                smt_assumptions
                cardinality_variable
                resulting_expression
            )
        with
        | Unbounded_interval ->
          Format.sprintf "(=> %s false)" smt_assumptions

      end
      |> assert_formula
    in
    ()


  let solve_assuming assumptions cont =
    solve_in_context (fun () ->
        assumptions_to_smt assumptions |> assert_formula)
      cont



  let get_val_from_model: type a. model -> a term -> a = fun model -> function
    | IVar(a, i) ->
      begin
        let k = snd @@ List.find (fun (v,b) -> v = a) model in
        match k with
        | VInt(k) -> k+i
        | _ -> raise (TypeCheckingError a)
      end
    | IValue(i) -> i
    | BValue(b) -> b
    | BVar(a, modi) ->
      begin
        let k = snd @@ List.find (fun (v,b) -> v = a) model in
        match k with
        | VBool(k) -> (modi && k) || (not modi && not k)
        | _ -> raise (TypeCheckingError a)
      end
      | Array_access(_)  -> failwith "trying to get an array value from a model - should not happen"
      | Array_term(_) ->  failwith "trying to get an array value from a model - should not happen"

  exception Bad_interval

  let array_ctx (_, _, ctx) =
    ctx

  let model_ctx (m, _, _) = m

  let interval_manager (_, i, _) =
    (i:Interval_manager.interval_manager)

  let make_domain_intersection ctx (d1:arrayed_domain) (d2:arrayed_domain) =
    let oracle a b =
      compare (get_val_from_model (model_ctx ctx) a) (get_val_from_model (model_ctx ctx) b)
    in
    (interval_manager ctx)#intersection_domains oracle (Arrays.array_sub_intersect (array_ctx ctx)) d1 d2

  let domain_neg a d =
    let c = array_ctx a in
    let i = interval_manager a in
    i#complementary_domain d (Arrays.array_sub_neg c) (Arrays.mk_full_subdiv c) Arrays.is_top

  let make_domain_union a (d1:arrayed_domain) (d2:arrayed_domain) =
    let d  = make_domain_intersection a (domain_neg a d1) (domain_neg a d2) in
    a, domain_neg a d

  let make_domain_from_expr var_name ctx e =
    let model, assum, actx = ctx in
    let array_init = Arrays.mk_full_subdiv actx (Ninf, Pinf) in
    match e with
    | Greater(IVar(v, n), a) when v = var_name -> ctx, [array_init, (Expr (minus n a), Pinf)]
    | Greater(a, IVar(v, n)) when v = var_name -> ctx, [array_init, (Ninf, Expr(minus (n-1) a))]
    | IEquality(a, IVar(v, n)) when v = var_name -> ctx, [array_init, (Expr(minus n a), Expr(minus (n-1) a))]
    | IEquality(IVar(v, n), a) when v = var_name -> ctx, [array_init, (Expr(minus n a), Expr(minus (n-1) a))]
    | Greater(a, b) ->
      let a_val = get_val_from_model model a and
      b_val = get_val_from_model model b in
      if a_val >= b_val then
        begin
          assum#assume (Greater(a, b));
          ctx, [array_init, (Ninf, Pinf)]
        end
      else
        begin
          assum#assume (Greater(b, plus_one b));
          ctx, []
        end
    | IEquality(a, b) ->
      let a_val = get_val_from_model model a and
      b_val = get_val_from_model model b in
      if a_val = b_val then
        begin
          assum#assume (IEquality(a, b));
          ctx, [array_init, (Ninf, Pinf)]
        end
      else if a_val > b_val then
        begin
          assum#assume (Greater(a, plus_one b));
          ctx, []
        end
      else
        begin
          assum#assume (Greater(b, plus_one a));
          ctx, []
        end
    | BEquality(Array_access(tab1, index1, neg1), Array_access(tab2, index2, neg2)) ->
      assert (index1 = IVar(var_name, 0));
      assert (index2 = IVar(var_name, 0));
      ctx, [Arrays.equality_arrays actx tab1 tab2 (xor neg1 neg2) array_init, (Ninf, Pinf)]
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

  let expr_to_domain model var_name expr =
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
    let (_ , a, _), d = expr_to_domain_aux (model, new Interval_manager.interval_manager, !my_array_ctx) expr
    in d, a#assumptions

end
