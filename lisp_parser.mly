%token <int> INT
%token <string> STRING
%token LEFT_BRACE
%token RIGHT_BRACE
%token TRUE
%token FALSE
(* part 1 *)
%start <Lisp.lisp> prog
%%
(* part 2 *)
prog:
  | v = value { v }
  ;

(* part 3 *)
value:
  | LEFT_BRACE; obj = list(value); RIGHT_BRACE
    { Lisp.Lisp_rec obj }
  | s = STRING
    { Lisp.Lisp_string s }
  | i = INT
    { Lisp.Lisp_int i }
  | FALSE
    { Lisp.Lisp_false }
  | TRUE
    { Lisp.Lisp_true }
  ;
