Require Import CFML.SepBase.
Require Import CFML.SepLifted.
Require Import CFML.WPLib.
Require Import CFML.WPLifted.
Require Import CFML.WPRecord.
Require Import CFML.WPArray.
Require Import CFML.WPBuiltin.
Require Import CFML.Semantics.
Require Import CFML.WPHeader.

Require Coq.ZArith.BinInt TLC.LibLogic TLC.LibRelation TLC.LibInt TLC.LibListZ.

Require CFML.SepBase CFML.SepLifted CFML.WPLifted CFML.WPRecord CFML.WPArray CFML.WPBuiltin.

Require CFML.Stdlib.Array_ml CFML.Stdlib.List_ml CFML.Stdlib.Sys_ml.

Require Import Coq.ZArith.BinIntDef CFML.Semantics CFML.WPHeader.

Notation unit_ := (unit) (only parsing).
Definition Unit (x : unit) (y : unit) := \[x = y].

Notation int_ := (Z) (only parsing).
Definition Int (x : Z) (y : Z) := \[x = y].

Notation bool_ := (bool) (only parsing).
Definition Bool (x : bool) (y : Prop) := \[x = true <-> y].

Require Import
  Stdlib.Floats.Floats
  Stdlib.ZArith.BinIntDef
  Stdlib.Strings.Ascii.

Notation option_ := (option) (only parsing).
Definition Option {A} (x : option A) (y : option A) :=
  \[x = y].

Notation list_ := (list) (only parsing).
Definition List {A} (x : list A) (y : list A) := \[x = y].

Notation array_ := (array) (only parsing).
Notation Array := (Array) (only parsing).

Notation ref_ := (fun _ : Type => loc) (only parsing).
Notation Ref x y := (x ~~> y) (only parsing).
