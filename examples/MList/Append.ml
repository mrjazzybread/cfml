type 'a contents = Nil | Cons of 'a * 'a mlist
and 'a mlist = 'a contents ref

let create () = ref Nil

let rec append (l1 : 'a mlist) (l2 : 'a mlist) : unit =
  match !l1 with Nil -> l1 := !l2 | Cons (x, t) -> append t l2
