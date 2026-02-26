(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*                                                                        *)
(*   Copyright 1996 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(** First-in first-out queues.

    This module implements queues (FIFOs), with in-place modification.

    {b Warning} This module is not thread-safe: each {!Queue.t} value must be
    protected from concurrent access (e.g. with a [Mutex.t]). Failure to do so
    can lead to a crash. *)

(*@ open Sequence *)

type !'a t
(** The type of queues containing elements of type ['a]. *)
(*@ model : val sequence *)

exception Empty
(** Raised when {!Queue.take} or {!Queue.peek} is applied to an empty queue. *)

val create : unit -> 'a t
(** Return a new queue, initially empty. *)
(*@ q = create ()
    ensures q = [] *)
