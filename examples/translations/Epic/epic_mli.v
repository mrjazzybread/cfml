Set Implicit Arguments.

Require Import gospelstdlib_verified.

Require Coq.ZArith.BinInt TLC.LibLogic TLC.LibRelation TLC.LibInt TLC.LibListZ.

Require Import CFML.SepBase CFML.SepLifted CFML.WPLib CFML.WPLifted CFML.WPRecord CFML.WPArray CFML.WPBuiltin.

Require CFML.Stdlib.Array_ml CFML.Stdlib.List_ml CFML.Stdlib.Sys_ml.

Require Import Coq.ZArith.BinIntDef CFML.Semantics CFML.WPHeader.

Delimit Scope Z_scope with Z.

Axiom fold_left_cons :
  forall {a44 : Type},
  forall {a45 : Type},
  forall {Ih_a44 : Inhab a44},
  forall {Ih_a45 : Inhab a45},
  forall f : sequence a45 -> a44 -> sequence a45,
  forall acc : sequence a45,
  forall x : a44,
  forall l : sequence a44,
  eq (fold_left f acc (cons x l)) (@empty a45 Ih_a45).


