Set Implicit Arguments.

Require Import Gospel.

Require Coq.ZArith.BinInt TLC.LibLogic TLC.LibRelation TLC.LibInt TLC.LibListZ.

Require Import CFML.SepBase CFML.SepLifted CFML.WPLib CFML.WPLifted CFML.WPRecord CFML.WPArray CFML.WPBuiltin.

Require CFML.Stdlib.Array_ml CFML.Stdlib.List_ml CFML.Stdlib.Sys_ml.

Require Import Coq.ZArith.BinIntDef CFML.Semantics CFML.WPHeader.

Delimit Scope Z_scope with Z.

Parameter Ref :
  Coq.Numbers.BinNums.Z ->
  loc -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter ref : CFML.Semantics.val.

Parameter _ref_spec :
  forall _prog_v : int,
  forall v : Coq.Numbers.BinNums.Z,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps ref (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make int _ _prog_v) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (Int v) _prog_v) (
    fun _prog_r : loc =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun r : Coq.Numbers.BinNums.Z =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (Int v) _prog_v
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.HS.repr (Ref r) _prog_r
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
            Coq.Init.Logic.eq r v
          )
        )
      )
    )
  ).

Parameter get : CFML.Semantics.val.

Parameter _get_spec :
  forall _prog_r : loc,
  forall r : Coq.Numbers.BinNums.Z,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps get (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_r) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (Ref r) _prog_r) (
    fun _prog_v : int =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun v : Coq.Numbers.BinNums.Z =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (Ref r) _prog_r
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.HS.repr (Int v) _prog_v
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
            Coq.Init.Logic.eq r v
          )
        )
      )
    )
  ).

Parameter update : CFML.Semantics.val.

Parameter _update_spec :
  forall _prog_r : loc,
  forall r : Coq.Numbers.BinNums.Z,
  forall _prog_v : int,
  forall v : Coq.Numbers.BinNums.Z,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps update (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_r) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make int _ _prog_v) Coq.Lists.List.nil
      )
    )
  ) (
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Ref r) _prog_r
    ) (CFML.SepBase.SepBasicSetup.HS.repr (Int v) _prog_v)
  ) (
    fun __UNUSED__ : Coq.Init.Datatypes.unit =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun _r' : Coq.Numbers.BinNums.Z =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (Ref _r') _prog_r
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.HS.repr (Int v) _prog_v
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
            Coq.Init.Logic.eq _r' v
          )
        )
      )
    )
  ).


