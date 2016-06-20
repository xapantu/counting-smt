(** OPTIONS *)

let usage = "usage: ./tests.native file.test"

let solver_path = ref ""

let solver_option = ref []

let nocolor = ref false

let set_options_solver s =
  solver_option := s :: !solver_option

let specs = [
    "-path-solver", Arg.Set_string solver_path, "Set the path to the solver";
    "-ps", Arg.Set_string solver_path, "Alias for -path-solver";
    "-op-solver", Arg.String set_options_solver, 
    "Set options for the solver (can be called multiple times)";
    "-os", Arg.String set_options_solver, "Alias for -op-solver";
    "-nocolor", Arg.Set nocolor, " disable colors in ouptut";
  ]

let alspecs = Arg.align specs

(* file containing the files to test and the expected results *)
let cin =
  let ofile = ref None in
  let set_file s =
    if Filename.check_suffix s ".test" then ofile := Some s
    else raise (Arg.Bad "no .test extension");
  in
  Arg.parse alspecs set_file usage;
  match !ofile with
    | Some f ->  open_in f
    | None -> stdin

let nocolor = !nocolor

let solver_path = match !solver_path with
    | "" -> ""
    | p -> Format.sprintf "-ps %s" p

let solver_options =
  let l = List.map (fun op -> Format.sprintf "-os %s" op) !solver_option in
  String.concat " " l
