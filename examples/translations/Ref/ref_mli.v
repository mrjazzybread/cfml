Set Implicit Arguments.

Require Import gospelstdlib_verified.

Require Coq.ZArith.BinInt TLC.LibLogic TLC.LibRelation TLC.LibInt TLC.LibListZ.

Require Import CFML.SepBase CFML.SepLifted CFML.WPLib CFML.WPLifted CFML.WPRecord CFML.WPArray CFML.WPBuiltin.

Require CFML.Stdlib.Array_ml CFML.Stdlib.List_ml CFML.Stdlib.Sys_ml.

Require Import Coq.ZArith.BinIntDef CFML.Semantics CFML.WPHeader.

Delimit Scope Z_scope with Z.

Import Stdlib.

Import Gospelstdlib.

Parameter ref : Type -> Type.

Parameter __Enc_ref : forall a : Type, CFML.SepLifted.Enc (ref a).

Instance _Enc_ref : forall a : Type, CFML.SepLifted.Enc (ref a) :=
__Enc_ref.

Parameter Ref :
  forall a : Type,
  forall {aIh : Inhab a},
  forall {Ea : CFML.SepLifted.Enc a},
  a -> loc -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter _ref : CFML.Semantics.val.

Lemma _ref_spec :
  forall a : Type,
  forall {aIh : Inhab a},
  forall {Ea : CFML.SepLifted.Enc a},
  forall v : a,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _ref (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make a _ v) Coq.Lists.List.nil
    )
  ) CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hempty (
    fun _prog_r : loc =>
    CFML.SepBase.SepBasicSetup.HS.repr (Ref v) _prog_r
  ). Admitted.

Parameter _get : CFML.Semantics.val.

Lemma _get_spec :
  forall a : Type,
  forall {aIh : Inhab a},
  forall {Ea : CFML.SepLifted.Enc a},
  forall _prog_r : loc,
  forall r : a,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _get (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_r) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (Ref r) _prog_r) (
    fun v : a =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Ref r) _prog_r
    ) (
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
        Coq.Init.Logic.eq r v
      )
    )
  ). Admitted.

Parameter _update : CFML.Semantics.val.

Lemma _update_spec :
  forall a : Type,
  forall {aIh : Inhab a},
  forall {Ea : CFML.SepLifted.Enc a},
  forall _prog_r : loc,
  forall r : a,
  forall v : a,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _update (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_r) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make a _ v) Coq.Lists.List.nil
      )
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (Ref r) _prog_r) (
    fun _ : Coq.Init.Datatypes.unit =>
    CFML.SepBase.SepBasicSetup.HS.repr (Ref v) _prog_r
  ). Admitted.


