Set Implicit Arguments.

Require Import Gospel.

Require Coq.ZArith.BinInt TLC.LibLogic TLC.LibRelation TLC.LibInt TLC.LibListZ.

Require Import CFML.SepBase CFML.SepLifted CFML.WPLib CFML.WPLifted CFML.WPRecord CFML.WPArray CFML.WPBuiltin.

Require CFML.Stdlib.Array_ml CFML.Stdlib.List_ml CFML.Stdlib.Sys_ml.

Require Import Coq.ZArith.BinIntDef CFML.Semantics CFML.WPHeader.

Delimit Scope Z_scope with Z.

Parameter T :
  Coq.Lists.List.list int ->
  loc -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter create : CFML.Semantics.val.

Parameter _create_spec :
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps create Coq.Lists.List.nil
  ) CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hempty (
    fun _prog_p : loc =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun p : Coq.Lists.List.list int =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (T p) _prog_p
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
          Coq.Init.Logic.eq p Coq.Lists.List.nil
        )
      )
    )
  ).

Parameter push : CFML.Semantics.val.

Parameter _push_spec :
  forall _prog_p : loc,
  forall p : Coq.Lists.List.list int,
  forall _prog_x : int,
  forall x : int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps push (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_p) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make int _ _prog_x) Coq.Lists.List.nil
      )
    )
  ) (
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (T p) _prog_p
    ) (CFML.SepBase.SepBasicSetup.HS.repr (Int x) _prog_x)
  ) (
    fun _ : Coq.Init.Datatypes.unit =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun _p' : Coq.Lists.List.list int =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (T _p') _prog_p
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.HS.repr (Int x) _prog_x
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
            Coq.Init.Logic.eq _p' (Coq.Lists.List.cons x p)
          )
        )
      )
    )
  ).

Parameter pop : CFML.Semantics.val.

Parameter _pop_spec :
  forall _prog_p : loc,
  forall p : Coq.Lists.List.list int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps pop (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_p) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (T p) _prog_p) (
    fun _prog_r : int =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun _p' : Coq.Lists.List.list int =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
        fun r : int =>
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.HS.repr (T _p') _prog_p
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
            CFML.SepBase.SepBasicSetup.HS.repr (Int r) _prog_r
          ) (
            CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
              Coq.Init.Logic.eq p (Coq.Lists.List.cons r _p')
            )
          )
        )
      )
    )
  ).

Parameter clear : CFML.Semantics.val.

Parameter _clear_spec :
  forall _prog_p : loc,
  forall p : Coq.Lists.List.list int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps clear (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_p) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (T p) _prog_p) (
    fun _ : Coq.Init.Datatypes.unit =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun _p' : Coq.Lists.List.list int =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (T _p') _prog_p
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
          Coq.Init.Logic.eq _p' Coq.Lists.List.nil
        )
      )
    )
  ).

Parameter rev_append : CFML.Semantics.val.

Parameter _rev_append_spec :
  forall _prog_p1 : loc,
  forall p1 : Coq.Lists.List.list int,
  forall _prog_p2 : loc,
  forall p2 : Coq.Lists.List.list int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps rev_append (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_p1) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_p2) Coq.Lists.List.nil
      )
    )
  ) (
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (T p1) _prog_p1
    ) (CFML.SepBase.SepBasicSetup.HS.repr (T p2) _prog_p2)
  ) (
    fun _ : Coq.Init.Datatypes.unit =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun _p1' : Coq.Lists.List.list int =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
        fun _p2' : Coq.Lists.List.list int =>
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.HS.repr (T _p1') _prog_p1
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
            CFML.SepBase.SepBasicSetup.HS.repr (T _p2') _prog_p2
          ) (
            CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
              CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
                Coq.Init.Logic.eq _p1' Coq.Lists.List.nil
              )
            ) (
              CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
                Coq.Init.Logic.eq _p2' (Coq.Lists.List.app _p2' (rev _p1'))
              )
            )
          )
        )
      )
    )
  ).


