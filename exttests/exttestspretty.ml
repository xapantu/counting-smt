type style =
  | Normal
  | Bold
  | Bold_off
  | FG_Red
  | FG_Green
  | FG_Default
      
let assoc_style =  function
  | Normal -> "0"
  | Bold -> "1"
  | Bold_off -> "22"
  | FG_Red -> "31"
  | FG_Green -> "32"
  | FG_Default -> "39"

let style_of_tag = function
  | "n" -> Normal
  | "b" -> Bold
  | "/b" -> Bold_off
  | "fg_red" -> FG_Red
  | "fg_green" -> FG_Green
  | "fg_default" -> FG_Default
  | _ -> assert false

let start_tag t = 
  try Printf.sprintf "[%sm" (assoc_style (style_of_tag t))
  with Not_found -> ""

let stop_tag t = 
  let st = match style_of_tag t with
    | Bold -> Bold_off
    | FG_Red | FG_Green -> FG_Default
    | _ -> Normal
  in
  Printf.sprintf "[%sm" (assoc_style st)

let add_colors formatter =
  Format.pp_set_tags formatter true;
  let old_fs = Format.pp_get_formatter_tag_functions formatter () in
  Format.pp_set_formatter_tag_functions formatter
    { old_fs with
      Format.mark_open_tag = start_tag;
      Format.mark_close_tag = stop_tag }

let _ =
  if not Exttestsoptions.nocolor then begin
    add_colors Format.std_formatter;
    add_colors Format.err_formatter;
  end
