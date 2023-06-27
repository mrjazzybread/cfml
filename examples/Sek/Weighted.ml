type 'a weighted = {
  elem : 'a;
  weight : int
}

let mk_weighted e w =
  { elem = e; weight = w }
let dummy_weighted e = mk_weighted e 0