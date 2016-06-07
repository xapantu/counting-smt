open Formula

module type T = sig
  module Formula : F
  open Formula
  type model
  type domain

  exception Unsat

  val solve: (model -> 'a) -> 'a
  val solve_formula: expr -> (model -> 'a) -> 'a
  val domain_cardinality: domain -> string
  val expr_to_domain: model -> string -> expr -> (domain * assumptions)
  val implies_card: assumptions -> string -> domain -> unit
  val solve_assuming: assumptions -> (model -> 'a) -> 'a

end

module LA_SMT = struct

  type sort =
    | Int
    | Bool

  type _ term =
    | IValue : int -> int term
    | IVar : string * int -> int term
    | BValue : bool -> bool term
    | BVar : string * bool -> bool term
    | Array_term : int term * int term * string -> bool array term (* index, array length, array name *)

  type concrete_value =
    | VBool of bool
    | VInt of int

  type rel =
    | Greater of int term * int term
    | IEquality of int term * int term
    | BEquality of bool term * bool term
    | Bool of bool term

  type bound =
    | Ninf
    | Pinf
    | Expr of int term

  type interval = bound * bound
  type domain = interval list

  type assignation = string * concrete_value
  type model = assignation list

  exception Unknown_answer of string
  exception Unbounded_interval
  exception Unsat
  exception TypeCheckingError of string

  let term_to_string: type a. a term -> string = function
    | IVar (s, 0) -> s
    | IVar (s, i) when i > 0 -> "(+ " ^ s ^ " " ^ string_of_int i ^ ")"
    | IVar (s, i) (* when i < 0 *) -> "(- " ^ s ^ " " ^ string_of_int (-i) ^ ")"
    | BValue(false) -> "false"
    | BValue(true) -> "true"
    | BVar(s, true) -> s
    | BVar(s, false) -> Format.sprintf "(not %s)" s
    | IValue i -> string_of_int i


  let rec rel_to_smt = function
    | Greater(e1, e2) ->
      "(>= " ^ term_to_string e1 ^ " " ^ term_to_string e2 ^ ")"
    | IEquality(e1, e2) ->
      "(= " ^ term_to_string e1 ^ " " ^ term_to_string e2 ^ ")"
    | BEquality(e1, e2) ->
      "(= " ^ term_to_string e1 ^ " " ^ term_to_string e2 ^ ")"
    | Bool(b) ->
      term_to_string b

  let bound_to_string = function
    | Ninf | Pinf -> raise Unbounded_interval
    | Expr e -> term_to_string e

  let interval_to_string (l, u) =
    "(+ (- " ^ bound_to_string u ^ " " ^ bound_to_string l ^ ") 1)"

  let domain_cardinality = function
    | [] -> "0"
    | dom -> dom
             |> List.map interval_to_string
             |> String.concat "+"

  module Formula = IFormula(struct
      type texpr = rel
      let texpr_to_smt = rel_to_smt
    end)

  open Formula

  let solver_command = "yices-smt2 --incremental"
  let vars = ref []

  let solver_in, solver_out =
    let a, b = Unix.open_process solver_command
    in ref a, ref b

  let reset_solver () =
    close_in !solver_in; close_out !solver_out;
    let a, b = Unix.open_process solver_command
    in solver_in := a; solver_out := b; vars := []

  let verbose = ref false
  let set_verbose s = verbose := s

  let send_to_solver s =
    output_string !solver_out s;
    if !verbose then
      Format.printf " -> %s@." s;
    output_string !solver_out "\n";
    flush !solver_out

  (* let () = send_to_solver "(set-logic QF_LIA)"*)

  let use_var name = function
    | Int ->
      let () = vars := (Int, name) :: !vars in
      send_to_solver @@ "(declare-fun " ^ name ^ " () Int)"
    | Bool ->
      let () = vars := (Bool, name) :: !vars in
      send_to_solver @@ "(declare-fun " ^ name ^ " () Bool)"

  let use_quantified_var name f = function
    | Int ->
      let () = vars := (Int, name) :: !vars in
      let a = f () in
      let first = ref true in
      let () = vars := List.filter (fun x -> 
          if x = (Int, name) then
            if !first then
              false
            else
              (first := false; true)
          else
            true) !vars in
      a
    | Bool ->
      let () = vars := (Bool, name) :: !vars in
      let a = f () in
      let () = vars := List.tl !vars in
      a

  let get_sort name =
    fst @@ List.find (fun (s, n) -> name = n) !vars

  let ensure_int name =
    if get_sort name = Int then ()
    else raise (TypeCheckingError name)

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

  let get_model () =
    send_to_solver (Format.sprintf "(get-value (%s))" (List.map snd !vars |> String.concat " "));
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
          raise (Unknown_answer ("couldn't understand \"" ^ lisp_to_string lisp ^ "\" and more specifically:\n" ^ a))
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
        | VInt(v) -> Printf.fprintf stdout "%s = %d\n" b v)
      m


  let implies_card assumptions str domain =
    "(=> " ^
    assumptions_to_smt assumptions ^ " (= " ^
    str ^ " " ^ domain_cardinality domain ^ "))"
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

  let domain_neg d =
    let rec domain_neg_aux old_bound = function
      | (Ninf, Expr a)::q -> domain_neg_aux (Expr  (plus_one a)) q
      | (Expr a, Pinf)::q -> [(old_bound, Expr (minus_one a))]
      | (Expr a, Expr b)::q -> (old_bound, Expr (minus_one a)) :: domain_neg_aux (Expr (plus_one b)) q
      | (Pinf, _)::_ | (_, Ninf)::_ -> raise Bad_interval
      | (Ninf, Pinf)::_ -> []
      | [] -> [(old_bound, Pinf)]
    in
    domain_neg_aux Ninf d


  let rec interval_domain_inter (model, a) (l1, u1) d2 cont =
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
      | (l, u)::q ->
        if greater l u1 then
          if equal l u1 then
            [(l, u1)]
          else
            []
        else if greater l l1 then
          if greater u u1 then
            (l, u1)::extract_inter q
          else
            (l, u)::extract_inter q
        else if greater u l1 then
          if greater u u1 then
            (l1, u1)::extract_inter q
          else
            (l1, u)::extract_inter q
        else
          extract_inter q
    in
    extract_inter d2
    |> cont (model, !assum)



  let rec make_domain_intersection a d1 d2 cont =
    match d1 with
    | [] -> cont a []
    | t1::q1 ->
      interval_domain_inter a t1 d2 (fun a dt1 ->
          make_domain_intersection a  q1 d2 (fun a dq1 ->
              cont a (dt1 @ dq1)
            ))

  let make_domain_union a d1 d2 cont =
    make_domain_intersection a (domain_neg d1) (domain_neg d2) (fun a d ->
        domain_neg d
        |> cont a)


  let make_domain_from_expr var_name (model, assum) e cont =
    match e with
    | Greater(IVar(v, n), a) when v = var_name -> cont (model, assum) [(Expr (minus n a), Pinf)]
    | Greater(a, IVar(v, n)) when v = var_name -> cont (model, assum) [(Ninf, Expr(minus n a))]
    | IEquality(a, IVar(v, n)) when v = var_name -> cont (model, assum) [(Expr(minus n a), Expr(minus n a))]
    | IEquality(IVar(v, n), a) when v = var_name -> cont (model, assum) [(Expr(minus n a), Expr(minus n a))]
    | Greater(a, b) ->
      let a_val = get_val_from_model model a and
      b_val = get_val_from_model model b in
      if a_val >= b_val then
        cont (model, (Greater(a, b))::assum) [(Ninf, Pinf)]
      else
        cont (model, (Greater(b, plus_one a))::assum) []
    | IEquality(a, b) ->
      let a_val = get_val_from_model model a and
      b_val = get_val_from_model model b in
      if a_val = b_val then
        cont (model, (IEquality(a, b))::assum) [(Ninf, Pinf)]
      else if a_val > b_val then
        cont (model, (Greater(a, plus_one b))::assum) []
      else
        cont (model, (Greater(b, plus_one a))::assum) []
    | BEquality(a, b) ->
      let a_val = get_val_from_model model a and
      b_val = get_val_from_model model b in
      if a_val = b_val then
        cont (model, (BEquality(a, b))::assum) [(Ninf, Pinf)]
      else
        cont (model, (BEquality(not_term a, b))::assum) []
    | Bool(a) ->
      let a_val = get_val_from_model model a in
      if a_val then
        cont (model, Bool(a)::assum) [(Ninf, Pinf)]
      else
        cont (model, Bool(not_term a)::assum) []

  let expr_to_domain model var_name expr =
    let rec (expr_to_domain_cps:
               (model * assumptions) -> expr -> ((model * assumptions) -> domain -> 'a) -> 'a)
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
              cont a (domain_neg d)
            )
        | Theory_expr(e) -> make_domain_from_expr var_name a e cont
    in
    expr_to_domain_cps (model, []) expr (fun (_, a) d -> d, a)

end
