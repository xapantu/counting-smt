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
  val expr_to_domain: model -> expr -> (domain * assumptions)
  val implies_card: assumptions -> string -> domain -> unit
  val solve_assuming: assumptions -> (model -> 'a) -> 'a

end

module LA_SMT = struct

  type sort =
    | Int
    | Bool

  type term =
    | Value of int
    | Var of string * int

  type rel =
    | Greater of term * term
    | Equality of term * term

  type bound =
    | Ninf
    | Pinf
    | Expr of term

  type interval = bound * bound
  type domain = interval list

  type assignation = string * int
  type model = assignation list

  exception Unknown_answer of string
  exception Unbounded_interval
  exception Unsat

  let expr_to_string = function
    | Var (s, 0) -> s
    | Var (s, i) when i > 0 -> "(+ " ^ s ^ " " ^ string_of_int i ^ ")"
    | Var (s, i) when i < 0 -> "(- " ^ s ^ " " ^ string_of_int (-i) ^ ")"
    | Value i -> string_of_int i

  let rec rel_to_smt = function
    | Greater(e1, e2) ->
      "(>= " ^ expr_to_string e1 ^ " " ^ expr_to_string e2 ^ ")"
    | Equality(e1, e2) ->
      "(= " ^ expr_to_string e1 ^ " " ^ expr_to_string e2 ^ ")"

  let bound_to_string = function
    | Ninf | Pinf -> raise Unbounded_interval
    | Expr e -> expr_to_string e

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

  let solver_in, solver_out = Unix.open_process solver_command

  let verbose = ref false
  let set_verbose s = verbose := s

  let send_to_solver s =
    output_string solver_out s;
    if !verbose then
    Format.printf " -> %s@." s;
    output_string solver_out "\n";
    flush solver_out

  (* let () = send_to_solver "(set-logic QF_LIA)"*)

  let vars = ref []
  let use_var name = function
    | Int ->
      let () = vars := name :: !vars in
      send_to_solver @@ "(declare-fun " ^ name ^ " () Int)"
    | Bool ->
      let () = vars := name :: !vars in
      send_to_solver @@ "(declare-fun " ^ name ^ " () Bool)"


  let rec is_sat () =
    let l = input_line solver_in in
    if l <> "" then
    match l with
    | "sat" -> true
    | "unsat" -> false
    | a -> raise (Unknown_answer a)
    else is_sat ()

  let get_model () =
    send_to_solver (Format.sprintf "(get-value (%s))" (String.concat " " !vars));
    let get_var lisp =
      let open Lisp in
      match lisp with
      | Lisp_rec(Lisp_string b :: Lisp_int v :: []) ->
        (b, v)
      | Lisp_rec(Lisp_string b :: Lisp_rec(Lisp_string "-" :: Lisp_int v :: []) :: []) ->
        (b, -v)
      | Lisp_rec(Lisp_string b :: Lisp_true :: []) ->
        (b, 1)
      | Lisp_rec(Lisp_string b :: Lisp_false :: []) ->
        (b, 0)
      | a -> raise (Unknown_answer ("couldn't understand that " ^ lisp_to_string a))
    in
    let lisp = solver_in
               |> Lexing.from_channel
               |> Lisp_parser.prog Lisp_lexer.read in
    match lisp with
    | Lisp_rec(l) -> List.map get_var l
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

  let print_model m =
    List.iter (fun (b, v) ->
        Format.printf "%s = %d@." b v)
      m


  let implies_card assumptions str domain =
    "(assert (=> " ^
    assumptions_to_smt assumptions ^ " (= " ^
    str ^ " " ^ domain_cardinality domain ^ ")))"
    |> send_to_solver


  let solve_assuming assumptions cont =
    solve_in_context (fun () ->
        send_to_solver (Format.sprintf "(assert %s)" (assumptions_to_smt assumptions)))
      cont



  let plus_one = function
    | Var(a, i) -> Var(a, i + 1)
    | Value(i) -> Value (i + 1)

  let minus_one = function
    | Var(a, i) -> Var(a, i - 1)
    | Value(i) -> Value (i - 1)

  let get_val model = function
    | Var(a, i) ->
      (snd @@ List.find (fun (v,b) -> v = a) model) + i
    | Value(i) -> i


  let domain_neg d =
    let rec domain_neg_aux old_bound = function
      | (Ninf, Expr a)::q -> domain_neg_aux (Expr  (plus_one a)) q
      | (Expr a, Pinf)::q -> [(old_bound, Expr (minus_one a))]
      | (Expr a, Expr b)::q -> (old_bound, Expr (minus_one a)) :: domain_neg_aux (Expr (plus_one b)) q
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
        let a_val, b_val = get_val model a, get_val model b in
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
        let a_val, b_val = get_val model a, get_val model b in
        if a_val = b_val then
          (assume (Equality(a, b)); true)
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


  let make_domain_from_expr assum e cont =
    match e with
    | Greater(Var("z", 0), a) -> cont assum [(Expr a, Pinf)]
    | Greater(a, Var("z", 0)) -> cont assum [(Ninf, Expr a)]
    | Equality(a, Var("z", 0)) -> cont assum [(Expr a, Expr a)]
    | Equality(Var("z", 0), a) -> cont assum [(Expr a, Expr a)]

  let expr_to_domain model expr =
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
        | Theory_expr(e) -> make_domain_from_expr a e cont
    in
    expr_to_domain_cps (model, []) expr (fun (_, a) d -> d, a)

end
