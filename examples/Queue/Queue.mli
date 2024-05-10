(*@ open Sequence *)

type t
(*@ mutable model : int sequence *)

val push : t -> int -> unit
(*@ push q x
    modifies q
    ensures q = old q ++ (singleton x) *)

val pop : t -> int
(*@ x = pop q
    modifies q
    ensures q = cons x (old q) *)
