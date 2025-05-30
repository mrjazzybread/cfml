type name = int
type t = name ref

let initial = 0
let create () = ref initial

let next x =
  x := !x + 1;
  if !x < 0 then failwith "Internal error: integer flow";
  !x

let reset x = x := initial
let get x = !x
