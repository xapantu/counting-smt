let usage = "basic smt solver, takes input from stdin"
let file = ref "_stdin"
               
let solver_path = 
  ref (
      try Printf.sprintf "%s/%s" (Sys.getenv "YICESDIR") "yices-smt2"
      with Not_found -> 
        let ecode = Sys.command "dtype yices-smt2" in
        if ecode = 0 then 
          "yices-smt2"
        else ""
    )
                      
let solver_option = ref ["--incremental"]

let set_options_solver s =
  solver_option := s :: !solver_option

let verbose = ref false

let args = [
    "--path-solver", Arg.Set_string solver_path, "Set the path to the solver";
    "-ps", Arg.Set_string solver_path, "Alias for -path-solver";
    "--op-solver", Arg.String set_options_solver, "Set options for the solver (can be called multiple times)";
    "-os", Arg.String set_options_solver, "Alias for -op-solver";
    "--verbose", Arg.Set verbose, "be verbose";
    "-v", Arg.Set verbose, "be verbose";
  ] 

let alargs = Arg.align args

let cin =
  let ofile = ref None in
  let set_file s = ofile := Some s in
  Arg.parse alargs set_file usage;
  match !ofile with 
    | Some f -> file := f ; open_in f 
    | None -> stdin

let file = !file

let solver_path = match !solver_path with
    | "" -> 
      Format.eprintf 
        "yices-smt2 is required but can not be found\n\
         (tests performed : $YICESDIR\\yices-smt2 and yices-smt2)\n\
         You should export a path or give it with the -ps option@.";
      exit 1
    | s -> s

let solver_command = Printf.sprintf "%s %s" solver_path 
                                    (String.concat " " !solver_option)

let verbose = !verbose
