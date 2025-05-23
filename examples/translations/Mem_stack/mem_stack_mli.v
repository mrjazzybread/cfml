Set Implicit Arguments.

Require Import gospelstdlib_verified.

Require Coq.ZArith.BinInt TLC.LibLogic TLC.LibRelation TLC.LibInt TLC.LibListZ.

Require Import CFML.SepBase CFML.SepLifted CFML.WPLib CFML.WPLifted CFML.WPRecord CFML.WPArray CFML.WPBuiltin.

Require CFML.Stdlib.Array_ml CFML.Stdlib.List_ml CFML.Stdlib.Sys_ml.

Require Import Coq.ZArith.BinIntDef CFML.Semantics CFML.WPHeader.

Delimit Scope Z_scope with Z.

Import Stdlib.

Import Gospelstdlib.

Parameter Estack :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  forall {Enc_a : Enc a},
  sequence a ->
  loc -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter _ecreate : CFML.Semantics.val.

Parameter _ecreate_spec :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  forall {Enc_a : Enc a},
  forall x : a,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _ecreate (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make a _ x) Coq.Lists.List.nil
    )
  ) CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hempty (
    fun _res_ : loc =>
    let '(_prog_r) := _res_ in
    CFML.SepBase.SepBasicSetup.HS.repr (Estack (@Sequence.empty a Ih_a)) _prog_r
  ).

Parameter _epush : CFML.Semantics.val.

Parameter _epush_spec :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  forall {Enc_a : Enc a},
  forall _prog_s : loc,
  forall s : sequence a,
  forall x : a,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _epush (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_s) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make a _ x) Coq.Lists.List.nil
      )
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (Estack s) _prog_s) (
    fun _res_ : Coq.Init.Datatypes.unit =>
    CFML.SepBase.SepBasicSetup.HS.repr (Estack (Sequence.cons x s)) _prog_s
  ).

Parameter _epop : CFML.Semantics.val.

Parameter _epop_spec :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  forall {Enc_a : Enc a},
  forall _prog_s : loc,
  forall s : sequence a,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _epop (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_s) Coq.Lists.List.nil
    )
  ) (
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Estack s) _prog_s
    ) (
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
        Coq.Init.Logic.not (Coq.Init.Logic.eq s (@Sequence.empty a Ih_a))
      )
    )
  ) (
    fun _res_ : a =>
    let '(r) := _res_ in
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun _s_ : sequence a =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (Estack _s_) _prog_s
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
          Coq.Init.Logic.eq s (Sequence.cons r _s_)
        )
      )
    )
  ).

Parameter pstack : Type -> Type.

Parameter _pcreate : CFML.Semantics.val.

Parameter _pcreate_spec :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  forall {Enc_a : Enc a},
  forall x : a,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _pcreate (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make a _ x) Coq.Lists.List.nil
    )
  ) CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hempty (
    fun _res_ : pstack a =>
    let '(_prog_r) := _res_ in
    CFML.SepBase.SepBasicSetup.HS.repr (Pstack (@Sequence.empty a Ih_a)) _prog_r
  ).

Parameter _ppush : CFML.Semantics.val.

Parameter _ppush_spec :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  forall {Enc_a : Enc a},
  forall _prog_s : pstack a,
  forall s : sequence a,
  forall x : a,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _ppush (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make (pstack a) _ _prog_s) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make a _ x) Coq.Lists.List.nil
      )
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (Pstack s) _prog_s) (
    fun _res_ : pstack a =>
    let '(_prog_r) := _res_ in
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun _s_ : sequence a =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (Pstack _s_) _prog_s
      ) (
        CFML.SepBase.SepBasicSetup.HS.repr (Pstack (Sequence.cons x _s_)) _prog_r
      )
    )
  ).

Parameter _ppop : CFML.Semantics.val.

Parameter _ppop_spec :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  forall {Enc_a : Enc a},
  forall _prog_s : pstack a,
  forall s : sequence a,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _ppop (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make (pstack a) _ _prog_s) Coq.Lists.List.nil
    )
  ) (
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Pstack s) _prog_s
    ) (
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
        Coq.Init.Logic.not (Coq.Init.Logic.eq s (@Sequence.empty a Ih_a))
      )
    )
  ) (
    fun _res_ : Coq.Init.Datatypes.prod (pstack a) a =>
    let '(_prog_rs, res) := _res_ in
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun rs : sequence a =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (Pstack (Sequence.cons res rs)) _prog_s
      ) (CFML.SepBase.SepBasicSetup.HS.repr (Pstack rs) _prog_rs)
    )
  ).

Parameter _pstack_to_estack : CFML.Semantics.val.

Parameter _pstack_to_estack_spec :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  forall {Enc_a : Enc a},
  forall _prog_ps : pstack a,
  forall ps : sequence a,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _pstack_to_estack (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make (pstack a) _ _prog_ps) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (Pstack ps) _prog_ps) (
    fun _res_ : loc =>
    let '(_prog_re) := _res_ in
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Pstack ps) _prog_ps
    ) (CFML.SepBase.SepBasicSetup.HS.repr (Estack ps) _prog_re)
  ).

Parameter _estack_to_pstack : CFML.Semantics.val.

Parameter _estack_to_pstack_spec :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  forall {Enc_a : Enc a},
  forall _prog_es : loc,
  forall es : sequence a,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _estack_to_pstack (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_es) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (Estack es) _prog_es) (
    fun _res_ : pstack a =>
    let '(_prog_rp) := _res_ in
    CFML.SepBase.SepBasicSetup.HS.repr (Pstack es) _prog_rp
  ).


