type name
type gen

(*@ owns_name (g : ...) (n : ...) *)

val create : unit -> gen
val next : gen -> name
(*@  *)

val reset : gen -> unit
