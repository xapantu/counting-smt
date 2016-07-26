open Arith_array_language

type congruence = int * int * int list (* modulo * coeff * remainder *)
exception Unsat

let check_good_congruence (a, c, b) =
  List.iter (fun b ->
      assert (0 <= b && b < a);
    ) b

let is_top c =
  check_good_congruence c;
  let a, d, b = c in
  List.sort_uniq compare b |> List.length = a

let rec gcd a b =
  match (a mod b) with
  | 0 -> b
  | r -> gcd b r

let interval_to_string (a, c, b) (l, u) =
  assert (b = [0]);
  match l, u with
  | Expr l, Expr u ->
    let u, l = term_to_string u, term_to_string l in
    Format.sprintf "(+ (div (- %s %s) %d) (ite (> (- (mod %s %d) (mod %s %d)) 0) 1 0))" u l a l a u a
  | _ -> raise Unsat

let intersection (a, b, c) (d, e, f) =
  if a > d then a, b, c else d, e, f
