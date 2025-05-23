Set Implicit Arguments.

Require Import gospelstdlib_verified.

Require Coq.ZArith.BinInt TLC.LibLogic TLC.LibRelation TLC.LibInt TLC.LibListZ.

Require Import CFML.SepBase CFML.SepLifted CFML.WPLib CFML.WPLifted CFML.WPRecord CFML.WPArray CFML.WPBuiltin.

Require CFML.Stdlib.Array_ml CFML.Stdlib.List_ml CFML.Stdlib.Sys_ml.

Require Import Coq.ZArith.BinIntDef CFML.Semantics CFML.WPHeader.

Delimit Scope Z_scope with Z.

Axiom add_ge :
  forall x : Z,
  forall y : Z,
  Coq.Init.Logic.and (ge (plus x y) y) (ge (plus x y) x).

Parameter T :
  Z -> loc -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Axiom t_0 :
  CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.himpl CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hempty (
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hforall (
      fun _prog_t : Z =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hforall (
        fun t : Z =>
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hwand (
          CFML.SepBase.SepBasicSetup.HS.repr (T t) _prog_t
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
            CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (eq t (0)%Z)
          ) (CFML.SepBase.SepBasicSetup.HS.repr (T t) _prog_t)
        )
      )
    )
  ).

Axiom extensionality :
  forall {a48 : Type},
  forall {Ih_a48 : Inhab a48},
  forall s1 : sequence a48,
  forall s2 : sequence a48,
  Coq.Init.Logic.iff (eq s1 s2) (
    forall i : Z,
    Coq.Init.Logic.and (le (0)%Z i) (lt i (length s1)) ->
    eq (seq_get s1 i) (seq_get s2 i)
  ).


