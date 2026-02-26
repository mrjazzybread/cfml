(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*         Francois Pottier, projet Cristal, INRIA Rocquencourt           *)
(*                  Jeremie Dimino, Jane Street Europe                    *)
(*                                                                        *)
(*   Copyright 2002 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

type 'a cell' = { content : 'a; mutable next : 'a cell }
and 'a cell = Nil | Cons of 'a cell'

type 'a t = {
  mutable length : int;
  mutable first : 'a cell;
  mutable last : 'a cell;
}

let create () = { length = 0; first = Nil; last = Nil }
