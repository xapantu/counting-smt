open Lisp
open Arith_array_language
module Lisp_typechecking(V:Variable_manager.VM) = struct

  exception Not_allowed_for_type of string * string

  let rec infer =
    let open Lisp in
    function
    | Lisp_string a ->
      V.get_sort a
    | Lisp_int _ ->
      Int
    | Lisp_true | Lisp_false | Lisp_rec (Lisp_string "not" :: _) ->
      Bool
    | Lisp_rec (Lisp_string "#" :: q) ->
      Int (* anyway, a lot of check will be run or q later *)
    | Lisp_rec (Lisp_string "and" :: q) | Lisp_rec (Lisp_string "true" ::q) ->
      List.iter (fun l -> assert (infer l = Bool)) q;
      Bool
    | Lisp_rec(Lisp_string "+" :: q)
    | Lisp_rec (Lisp_string "-" :: q)
    | Lisp_rec (Lisp_string "*" :: q)
    | Lisp_rec (Lisp_string "mod" :: ((_ :: _ :: []) as q) ) ->
      List.iter (fun l -> if infer l <> Int && infer l <> Real then
                    failwith ("couldn't ensure type for " ^ (lisp_to_string l) ^ " is int")
                ) q;
      Int
    | Lisp_rec (Lisp_string "select" :: a :: b) ->
      Bool
    | Lisp_rec (Lisp_string "store" :: a :: b) ->
      infer a
    | l -> failwith ("couldn't infer type for " ^ (lisp_to_string l))

  let to_sort =
    let open Lisp in
    function
    | Lisp_string "Int" -> Int
    | Lisp_string "Bool" -> Bool
    | Lisp_string "Real" -> Real
    | Lisp_rec(Lisp_string "Array" :: Lisp_string x :: Lisp_string "Bool" :: []) ->
      Array(V.get_range x, Bool)
    | (Lisp_string a) as e ->
      begin
        try
          V.get_range a
        with
        | Not_found ->
          raise (Not_allowed_for_type (lisp_to_string e, "sort"))
      end
    | e ->
      raise (Not_allowed_for_type (lisp_to_string e, "sort"))


end

