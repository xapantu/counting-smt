open Exttestsoptions
open Exttestspretty

(** TEST FUNCTION *)

(* Read one by one the files to test and pipe the output to an input_channel
 then check if the result is consistent with the expected one *)
let read_file f res = 
  try 
    let f = 
      if Filename.check_suffix f ".smt" then f
      else raise Exit
    in 
    let cmd = Format.sprintf "./solver.native %s %s %s" 
                             f solver_path solver_options in
    Format.printf "Testing : %s : @?" cmd;
    let out_cin = Unix.open_process_in cmd in
    let rec concat_input ll =
      try 
        let l = input_line out_cin in
        concat_input (l :: ll)
      with End_of_file -> String.concat " " (List.rev ll)
    in 
    let out_res = concat_input [] in
    let _ = Unix.close_process_in out_cin in
    if out_res = res then
      begin
        Format.printf "@{<b>@{<fg_green>OK@}@}\n@.";
        Format.printf "Obtained : @{<fg_green>%s@}@." out_res;
      end
    else
      begin
        Format.printf "@{<b>@{<fg_red>Not OK@}@}\n@.";
        Format.printf "Expected : @{<fg_green>%s@}@." res;
        Format.printf "Obtained : @{<fg_red>%s@}@." out_res;
      end;
    Format.printf "-----------@\n@."
  with
    | Exit -> Format.printf "The file %s doesn't have a .smt extension@." f
    | Sys_error s -> Format.printf "%s" s


(** READING OF THE TEST FILE *)

let () =
  let re = Str.regexp "^\"\\([^\"]*\\)\" \"\\([^\"]*\\)\"" in
  let nl = Str.regexp "\\\\n" in
  try
    while true do
      let line = input_line cin in
      let line = Str.global_replace nl " " line in
      let _ = Str.string_match re line 0 in
      try
        let f = Str.matched_group 1 line in
        try 
          let s = Str.matched_group 2 line in
          read_file f s;
        with Not_found -> Format.printf "No expected result given@."
      with _ -> ()
    done
  with End_of_file -> close_in cin; exit 0
  
