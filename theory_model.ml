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
         (string_of_int s) ^ " " ^ (inf_interval_to_string i))
    |> String.concat ", "


  module Formula = IFormula(struct
      type texpr = rel
      let texpr_to_smt = rel_to_smt
      type tsort = sort
    end)

  open Formula
  
  type context = model * assumptions * Arrays.array_ctx

  let solver_command = "yices-smt2 --incremental"
  let vars = ref []
  let range = Hashtbl.create 10
  let get_range = Hashtbl.find range

  let solver_in, solver_out =
    let a, b = Unix.open_process solver_command
    in ref a, ref b


  let my_array_ctx = ref (Arrays.new_ctx ())

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
    Hashtbl.reset range; my_array_ctx := Arrays.new_ctx ()

  let verbose = ref false
  let set_verbose s = verbose := s

  let send_to_solver s =
    output_string !solver_out s;
    if !verbose then
      Format.printf " -> %s@." s;
    output_string !solver_out "\n";
    flush !solver_out

  let new_range: string -> bound -> bound -> unit =
    fun name b1 b2 ->
      Hashtbl.add range name (Range (b1, b2))

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

  let use_quantified_var name sort f =
      let () = vars := (sort, name) :: !vars in
      let a = f () in
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


  let implies_card assumptions str domain =
    "(=> " ^
    assumptions_to_smt assumptions ^
    begin
    try
      " (= " ^
      str ^ " " ^ domain_cardinality domain ^ "))"
    with
    | Unbounded_interval -> " false)"
    end
      |> assert_formula


  let solve_assuming assumptions cont =
    solve_in_context (fun () ->
        assumptions_to_smt assumptions |> assert_formula)
      cont



  let (plus_one: int term -> int term) = function
    | IVar(a, i) -> IVar(a, i + 1)
    | IValue(i) -> IValue (i + 1)

  let (minus_one: int term -> int term) = function
    | IVar(a, i) -> IVar(a, i - 1)
    | IValue(i) -> IValue (i - 1)


  let minus:int -> int term -> int term = fun n -> function
    | IVar(a, i) -> IVar(a, i - n)
    | IValue(i) -> IValue (i - n)

  let not_term: bool term -> bool term = function
    | BValue(k) -> BValue(not k)
    | BVar(s, k) -> BVar (s, not k)
    | Array_access(tab, index, k) -> Array_access(tab, index, not k)

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

  exception Bad_interval

  let array_ctx (_, _, ctx) =
    ctx

  (* ok, this could be rewritten *)
  let domain_neg ctx d =
    let ctx = array_ctx ctx in
    let rec domain_neg_aux old_bound dom =
      match dom with
      | (arrays, interv) :: q ->
        begin
          match interv with
          | (Ninf, Expr a) -> domain_neg_aux (Expr  (plus_one a)) q
          | (Expr a, Pinf) ->
            if Expr a = old_bound then
              []
            else
              let interv = (old_bound, Expr (minus_one a)) in
              [Arrays.mk_full_subdiv ctx interv, interv]
          | (Expr a, Expr b) ->
            if Expr a = old_bound then
              domain_neg_aux (Expr (plus_one b)) q
            else
              let interv = (old_bound, Expr (minus_one a)) in
              (Arrays.mk_full_subdiv ctx interv, interv) :: domain_neg_aux (Expr (plus_one b)) q
          | (Pinf, _) | (_, Ninf) -> raise Bad_interval
          | (Ninf, Pinf) -> []
        end

      | [] ->
        let interv = (old_bound, Pinf) in
        [Arrays.mk_full_subdiv ctx interv, interv]
    in
    let dneg = domain_neg_aux Ninf d
    in
    if d = [] then dneg
    else
      let rec one_on_one l1 = function
        | t :: q ->t :: (one_on_one q l1)
        | [] -> l1 in
      let fin =
        let d = List.map (fun (l, i) -> Arrays.array_sub_neg ctx l, i) d in
        match List.hd d with
        | (_, (Ninf, _)) -> one_on_one dneg d
        | _ -> one_on_one d dneg
      in 
      fin


  let rec interval_domain_inter (model, a, array_ctx) ((arr, (l1, u1)): arrayed_interval) (d2:arrayed_domain) (cont: 'a -> arrayed_domain -> 'c) : 'c =
    let assum = ref a in
    let assume l =
      assum := l::!assum
    in
    (* >= *)
    let greater a b =
      match a, b with
      | _, Ninf -> true
      | Ninf, _ -> false
      | Pinf, _  -> true
      | _, Pinf  -> false
      | Expr a, Expr b ->
        let a_val, b_val = get_val_from_model model a, get_val_from_model model b in
        if a_val >= b_val then
          (assume (Greater(a, b)); true)
        else
          (assume (Greater(b, plus_one a)); false)
    in
    let equal a b =
      match a, b with
      | Ninf, Ninf -> true
      | Pinf, Pinf -> true
      | Expr a, Expr b ->
        let a_val, b_val = get_val_from_model model a, get_val_from_model model b in
        if a_val = b_val then
          (assume (IEquality(a, b)); true)
        else if a_val > b_val then
          (assume (Greater(a, plus_one b)); false)
        else
          (assume (Greater(b, plus_one a)); false)
      | _ -> false
    in
    let rec extract_inter = function
      | [] -> []
      | (arrays, (l, u))::q ->
        let intersect_arrays = Arrays.array_sub_intersect array_ctx arr arrays in
        if greater l u1 then
          if equal l u1 then
            [intersect_arrays, (l, u1)]
          else
            []
        else if greater l l1 then
          if greater u u1 then
            (intersect_arrays, (l, u1))::extract_inter q
          else
            (intersect_arrays, (l, u))::extract_inter q
        else if greater u l1 then
          if greater u u1 then
            (intersect_arrays, (l1, u1))::extract_inter q
          else
            (intersect_arrays, (l1, u))::extract_inter q
        else
          extract_inter q
    in
    extract_inter d2
    |> cont (model, !assum, array_ctx)



  let rec make_domain_intersection (a:context) (d1:arrayed_domain) (d2:arrayed_domain) (cont:'a -> arrayed_domain -> 'c) : 'c =
    match d1 with
    | [] -> cont a []
    | t1::q1 ->
      interval_domain_inter a t1 d2 (fun a dt1 ->
          make_domain_intersection a  q1 d2 (fun a dq1 ->
              cont a (dt1 @ dq1)
            ))

  let make_domain_union a (d1:arrayed_domain) (d2:arrayed_domain) (cont:'a -> arrayed_domain -> 'c) : 'c =
    make_domain_intersection a (domain_neg  a d1) (domain_neg a d2) (fun a d ->
        domain_neg a d
        |> cont a)


  let make_domain_from_expr var_name ctx e cont =
    let model, assum, actx = ctx in
    let array_init = Arrays.full_array_subdivision in
    match e with
    | Greater(IVar(v, n), a) when v = var_name -> cont ctx [array_init, (Expr (minus n a), Pinf)]
    | Greater(a, IVar(v, n)) when v = var_name -> cont ctx [array_init, (Ninf, Expr(minus n a))]
    | IEquality(a, IVar(v, n)) when v = var_name -> cont ctx [array_init, (Expr(minus n a), Expr(minus n a))]
    | IEquality(IVar(v, n), a) when v = var_name -> cont ctx [array_init, (Expr(minus n a), Expr(minus n a))]
    | Greater(a, b) ->
      let a_val = get_val_from_model model a and
      b_val = get_val_from_model model b in
      if a_val >= b_val then
        cont (model, (Greater(a, b))::assum, actx) [array_init, (Ninf, Pinf)]
      else
        cont (model, (Greater(b, plus_one a))::assum, actx) []
    | IEquality(a, b) ->
      let a_val = get_val_from_model model a and
      b_val = get_val_from_model model b in
      if a_val = b_val then
        cont (model, (IEquality(a, b))::assum, actx) [array_init, (Ninf, Pinf)]
      else if a_val > b_val then
        cont (model, (Greater(a, plus_one b))::assum, actx) []
      else
        cont (model, (Greater(b, plus_one a))::assum, actx) []
    | BEquality(a, b) ->
      let a_val = get_val_from_model model a and
      b_val = get_val_from_model model b in
      if a_val = b_val then
        cont (model, (BEquality(a, b))::assum, actx) [array_init, (Ninf, Pinf)]
      else
        cont (model, (BEquality(not_term a, b))::assum, actx) []
    | Bool(a) ->
      let a_val = get_val_from_model model a in
      if a_val then
        cont (model, Bool(a)::assum, actx) [array_init, (Ninf, Pinf)]
      else
        cont (model, Bool(not_term a)::assum, actx) []

  let expr_to_domain model var_name expr =
    let rec (expr_to_domain_cps:
               context -> expr -> (context -> arrayed_domain -> 'a) -> 'a)
      = fun a expr cont ->
        match expr with
        | And(e1, e2) ->
          expr_to_domain_cps a e1 (fun a d1 ->
              expr_to_domain_cps a e2 (fun a d2 ->
                  make_domain_intersection a d1 d2 cont
                )
            )
        | Or(e1, e2) ->
          expr_to_domain_cps a e1 (fun a d1 ->
              expr_to_domain_cps a e2 (fun a d2 ->
                  make_domain_union a d1 d2 cont
                )
            )
        | Not(e) ->
          expr_to_domain_cps a e (fun a d ->
              cont a (domain_neg a d)
            )
        | Theory_expr(e) -> make_domain_from_expr var_name a e cont
    in
    expr_to_domain_cps (model, [], !my_array_ctx) expr (fun (_, a, _) d -> d, a)

end
