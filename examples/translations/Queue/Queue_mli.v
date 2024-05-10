Set Implicit Arguments.

Require Import Gospel.

Require Coq.ZArith.BinInt TLC.LibLogic TLC.LibRelation TLC.LibInt TLC.LibListZ.

Require Import CFML.SepBase CFML.SepLifted CFML.WPLib CFML.WPLifted CFML.WPRecord CFML.WPArray CFML.WPBuiltin.

Require CFML.Stdlib.Array_ml CFML.Stdlib.List_ml CFML.Stdlib.Sys_ml.

Require Import Coq.ZArith.BinIntDef CFML.Semantics CFML.WPHeader.

Delimit Scope Z_scope with Z.

Parameter MQueue :
  Coq.Lists.List.list int ->
  loc -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.
Module Type Queue_spec.
Parameter push : CFML.Semantics.val.

Parameter Triple_push :
  forall _prog_q : loc,
  forall q : Coq.Lists.List.list int,
  forall _prog_x : int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps push (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_q) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make int _ _prog_x) Coq.Lists.List.nil
      )
    )
  ) (
      CFML.SepBase.SepBasicSetup.HS.repr (MQueue q) _prog_q
  ) (
    fun _ : Coq.Init.Datatypes.unit =>
        CFML.SepBase.SepBasicSetup.HS.repr (MQueue (Coq.Lists.List.app q (Gospel.singleton _prog_x))) _prog_q
  ).

Parameter pop : CFML.Semantics.val.

Parameter Triple_pop :
  forall _prog_q : loc,
  forall q : Coq.Lists.List.list int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps pop (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_q) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (MQueue q) _prog_q) (
    fun _prog_x : int =>
          CFML.SepBase.SepBasicSetup.HS.repr (MQueue  (Coq.Lists.List.app q (Gospel.singleton _prog_x))) _prog_q
  ).


End Queue_spec.
