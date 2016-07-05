type 'a event = ('a -> unit) list ref

let iter e f =
  e := f :: !e

let event e a =
  List.iter (fun f -> f a) !e

let new_event () =
  ref []
