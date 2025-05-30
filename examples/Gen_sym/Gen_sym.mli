(*@ type name *)

type name
(*@ model : name *)

type t
(*@ mutable model : name Set.t *)

val create : unit -> t
(*@ let g = create () in
      ensures g = Set.empty *)

val next : t -> name
(*@ let n = next g in
      ensures Set.mem n g
      ensures not (Set.mem n (old g))
      ensures Set.subset (old g) g *)

val reset : t -> unit
(*@ modifies g
    let () = reset g in
      ensures g = Set.empty *)
