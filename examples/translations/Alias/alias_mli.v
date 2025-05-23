Set Implicit Arguments.

Require Import gospelstdlib_verified.

Require Coq.ZArith.BinInt TLC.LibLogic TLC.LibRelation TLC.LibInt TLC.LibListZ.

Require Import CFML.SepBase CFML.SepLifted CFML.WPLib CFML.WPLifted CFML.WPRecord CFML.WPArray CFML.WPBuiltin.

Require CFML.Stdlib.Array_ml CFML.Stdlib.List_ml CFML.Stdlib.Sys_ml.

Require Import Coq.ZArith.BinIntDef CFML.Semantics CFML.WPHeader.

Delimit Scope Z_scope with Z.

Import Stdlib.

Import Gospelstdlib.

Parameter t : Type.

Parameter __Enc_t : CFML.SepLifted.Enc t.

Instance _Enc_t : CFML.SepLifted.Enc t := __Enc_t.

Parameter _Alias :
  t -> t -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter _st_eq : CFML.Semantics.val.

Parameter _st_eq_spec :
  forall _prog_x : t,
  forall x : t,
  forall _prog_y : t,
  forall y : t,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _st_eq (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make t _ _prog_x) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make t _ _prog_y) Coq.Lists.List.nil
      )
    )
  ) (
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (_Alias x) _prog_x
    ) (CFML.SepBase.SepBasicSetup.HS.repr (_Alias y) _prog_y)
  ) (
    fun _prog_b : bool =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (_Alias x) _prog_x
    ) (
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (_Alias y) _prog_y
      ) (
        CFML.SepBase.SepBasicSetup.HS.repr (Bool (Coq.Init.Logic.eq x y)) _prog_b
      )
    )
  ).

Parameter _ph_eq : CFML.Semantics.val.


