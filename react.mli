type 'a event

val iter: 'a event -> ('a -> unit) -> unit
val event: 'a event -> 'a -> unit
val new_event: unit -> 'a event
