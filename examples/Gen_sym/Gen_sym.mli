(*@ type name *)

type name
(*@ model : name *)

type gen
(*@ mutable model : name Set.t *)

val create : unit -> gen
(*@ let g = create () in
      ensures g = Set.empty *)

val next : gen -> name
(*@ modifies g
    let n = next g in
      ensures not (Set.mem n (old g))
      ensures g = Set.add n (old g) *)

val reset : gen -> unit
(*@ modifies g
    let () = reset g in
      ensures g = Set.empty *)
