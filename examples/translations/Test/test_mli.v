Set Implicit Arguments.

Require Import gospelstdlib_verified.

Require Coq.ZArith.BinInt TLC.LibLogic TLC.LibRelation TLC.LibInt TLC.LibListZ.

Require Import CFML.SepBase CFML.SepLifted CFML.WPLib CFML.WPLifted CFML.WPRecord CFML.WPArray CFML.WPBuiltin.

Require CFML.Stdlib.Array_ml CFML.Stdlib.List_ml CFML.Stdlib.Sys_ml.

Require Import Coq.ZArith.BinIntDef CFML.Semantics CFML.WPHeader.

Delimit Scope Z_scope with Z.

Import Stdlib.

Import Gospelstdlib.

Record t : Type := _mk_t { y : int; x : int }.

Parameter _t : Type.

Parameter __Enc__t : CFML.SepLifted.Enc _t.

Instance _Enc__t : CFML.SepLifted.Enc _t := __Enc__t.

Parameter Test :
  t -> _t -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter _f : CFML.Semantics.val.

Parameter _f_spec :
  forall _prog_arg : _t,
  forall arg : t,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _f (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make _t _ _prog_arg) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (Test arg) _prog_arg) (
    fun _prog_r : _t =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun r : t =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (Test arg) _prog_arg
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.HS.repr (Test r) _prog_r
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
            Coq.Init.Logic.eq (x arg) (y r)
          )
        )
      )
    )
  ).


