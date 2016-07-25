open Lisp
open Arith_array_language
module Lisp_typechecking(V:Variable_manager.VM) = struct

  exception Not_allowed_for_type of string * string
  exception Incompatible_equality

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
    | Lisp_rec (Lisp_string "forall" :: q) ->
      Bool
    | Lisp_rec (Lisp_string "and" :: q) | Lisp_rec (Lisp_string "or" ::q) ->
      List.iter (fun l -> assert (infer l = Bool)) q;
      Bool
    | Lisp_rec (Lisp_string "=" :: a :: b :: []) ->
      let ta = infer a and tb = infer b in
      if ta = tb then
        Bool
      else
        raise Incompatible_equality
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
    | Lisp_rec (Lisp_string "const-array" :: a :: []) ->
      Array(Int, infer a)
    | Lisp_rec (Lisp_rec (Lisp_string "as" :: Lisp_string "const" :: q :: []) :: _ ) ->
      to_sort q
    | l -> failwith ("couldn't infer type for " ^ (lisp_to_string l))


  and to_sort =
    let open Lisp in
    function
    | Lisp_string "Int" -> Int
    | Lisp_string "Bool" -> Bool
    | Lisp_string "Real" -> Real
    | Lisp_rec(Lisp_string "Array" :: Lisp_string x :: Lisp_string "Bool" :: []) ->
      begin
        try
          match x with 
          | "Int" -> Array(Int, Bool)
          | _ -> Array(V.get_range x, Bool)
        with
        | Not_found -> failwith (Format.sprintf "Unknown range type %s" x)
      end
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

