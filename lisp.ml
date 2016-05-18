type lisp =
  | Lisp_rec of lisp list
  | Lisp_string of string
  | Lisp_int of int
  | Lisp_false
  | Lisp_true

let rec lisp_to_string = function
  | Lisp_rec(l) -> List.map lisp_to_string l
                   |> String.concat " "
                   |> Format.sprintf "(%s)"
  | Lisp_string(s) -> s
  | Lisp_int(i) -> string_of_int i
  | Lisp_false -> "false"
  | Lisp_true -> "true"
