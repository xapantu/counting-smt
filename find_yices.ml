let find () = 
  let fcmd = try let dir = Sys.getenv "YICESDIR" 
                 in Some (Format.sprintf "find %s -iname yices-smt2" dir)
             with Not_found -> None in
  
  let wcmd = Format.sprintf "which yices-smt2 > /dev/null" in
  let sp = match fcmd with 
      | Some c -> let out_cin = Unix.open_process_in c in
                  let l = input_line out_cin in
                  let _ = Unix.close_process_in out_cin in l
      | None ->
        if Sys.command wcmd = 0 then "yices-smt2"
        else ""
  in
  match sp with 
    | "" -> 
      Format.eprintf 
        "yices-smt2 is required but can not be found\n\
         (tests performed : %s%s)\n\
         You should export a path or give it with the -ps option@." wcmd 
        (match fcmd with | Some c -> Format.sprintf ", %s" c | None -> "");
      exit 1
    | s -> s
