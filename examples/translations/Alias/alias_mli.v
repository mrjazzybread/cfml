Set Implicit Arguments.

Require Import Gospel.

Require Coq.ZArith.BinInt TLC.LibLogic TLC.LibRelation TLC.LibInt TLC.LibListZ.

Require Import CFML.SepBase CFML.SepLifted CFML.WPLib CFML.WPLifted CFML.WPRecord CFML.WPArray CFML.WPBuiltin.

Require CFML.Stdlib.Array_ml CFML.Stdlib.List_ml CFML.Stdlib.Sys_ml.

Require Import Coq.ZArith.BinIntDef CFML.Semantics CFML.WPHeader.

Delimit Scope Z_scope with Z.

Parameter T :
  int -> loc -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter st_eq : CFML.Semantics.val.

Parameter _st_eq_spec :
  forall _prog_x : loc,
  forall x : int,
  forall _prog_y : loc,
  forall y : int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps st_eq (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_x) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_y) Coq.Lists.List.nil
      )
    )
  ) (
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (T x) _prog_x
    ) (CFML.SepBase.SepBasicSetup.HS.repr (T y) _prog_y)
  ) (
    fun _prog_b : bool =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun b : bool =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (T x) _prog_x
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.HS.repr (T y) _prog_y
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
            CFML.SepBase.SepBasicSetup.HS.repr (Bool b) _prog_b
          ) (
            CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
              Coq.Init.Logic.iff (Coq.Init.Logic.eq b true) (
                Coq.Init.Logic.eq x y
              )
            )
          )
        )
      )
    )
  ).

Parameter ph_eq : CFML.Semantics.val.

Parameter _ph_eq_spec :
  forall _prog_x : loc,
  forall x : loc,
  forall _prog_y : loc,
  forall y : loc,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps ph_eq (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_x) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_y) Coq.Lists.List.nil
      )
    )
  ) (
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Loc x) _prog_x
    ) (CFML.SepBase.SepBasicSetup.HS.repr (Loc y) _prog_y)
  ) (
    fun _prog_b : bool =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun b : bool =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (Loc x) _prog_x
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.HS.repr (Loc y) _prog_y
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
            CFML.SepBase.SepBasicSetup.HS.repr (Bool b) _prog_b
          ) (
            CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
              Coq.Init.Logic.iff (Coq.Init.Logic.eq b true) (
                Coq.Init.Logic.eq x y
              )
            )
          )
        )
      )
    )
  ).


