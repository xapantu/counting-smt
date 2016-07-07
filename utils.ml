let xor a b =
  a && (not b) || b && (not a)

exception Oops_unwrap
let unwrap = function
| Some s -> s
| None -> raise Oops_unwrap

let modp a b =
  let c = a mod b in
  if c >= 0 then c
  else c + b
