let xor a b =
  a && (not b) || b && (not a)

exception Oops_unwrap
let unwrap = function
| Some s -> s
| None -> raise Oops_unwrap

