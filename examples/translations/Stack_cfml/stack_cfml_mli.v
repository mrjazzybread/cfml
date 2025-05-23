Set Implicit Arguments.

Require Import gospelstdlib_verified.

Require Coq.ZArith.BinInt TLC.LibLogic TLC.LibRelation TLC.LibInt TLC.LibListZ.

Require Import CFML.SepBase CFML.SepLifted CFML.WPLib CFML.WPLifted CFML.WPRecord CFML.WPArray CFML.WPBuiltin.

Require CFML.Stdlib.Array_ml CFML.Stdlib.List_ml CFML.Stdlib.Sys_ml.

Require Import Coq.ZArith.BinIntDef CFML.Semantics CFML.WPHeader.

Delimit Scope Z_scope with Z.

Import Stdlib.

Import Gospelstdlib.

Import Sequence.

Parameter Stack_cfml :
  forall a : Type,
  forall {aIh : Inhab a},
  forall {Ea : CFML.SepLifted.Enc a},
  sequence a ->
  loc -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter _create : CFML.Semantics.val.

Parameter _create_spec :
  forall a : Type,
  forall {aIh : Inhab a},
  forall {Ea : CFML.SepLifted.Enc a},
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _create (
      Coq.Lists.List.cons (
        @CFML.SepLifted.dyn_make CFML.Semantics.val _ Coq.Init.Datatypes.tt
      ) Coq.Lists.List.nil
    )
  ) CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hempty (
    fun _prog_q : loc =>
    CFML.SepBase.SepBasicSetup.HS.repr (Stack_cfml (@empty a aIh)) _prog_q
  ).

Parameter _is_empty : CFML.Semantics.val.

Parameter _is_empty_spec :
  forall a : Type,
  forall {aIh : Inhab a},
  forall {Ea : CFML.SepLifted.Enc a},
  forall _prog_q : loc,
  forall q : sequence a,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _is_empty (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_q) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (Stack_cfml q) _prog_q) (
    fun _prog_b : bool =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Stack_cfml q) _prog_q
    ) (
      CFML.SepBase.SepBasicSetup.HS.repr (
        Bool (Coq.Init.Logic.eq q (@empty a aIh))
      ) _prog_b
    )
  ).
Parameter _push : CFML.Semantics.val.

Parameter _push_spec :
  forall a : Type,
  forall {aIh : Inhab a},
  forall {Ea : CFML.SepLifted.Enc a},
  forall _prog_p : loc,
  forall p : sequence a,
  forall x : a,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _push (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_p) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make a _ x) Coq.Lists.List.nil
      )
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (Stack_cfml p) _prog_p) (
    fun _ : Coq.Init.Datatypes.unit =>
    CFML.SepBase.SepBasicSetup.HS.repr (Stack_cfml (cons x p)) _prog_p
  ).

Parameter _pop : CFML.Semantics.val.

Lemma _pop_spec :
  forall a : Type,
  forall {aIh : Inhab a},
  forall {Ea : CFML.SepLifted.Enc a},
  forall _prog_p : loc,
  forall p : sequence a,
  Coq.Init.Logic.not (Coq.Init.Logic.eq p (@empty a aIh)) ->
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _pop (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_p) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (Stack_cfml p) _prog_p) (
    fun r : a =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun _p_ : sequence a =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (Stack_cfml _p_) _prog_p
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
          Coq.Init.Logic.eq p (cons r _p_)
        )
      )
    )
  ). Admitted.

Parameter _clear : CFML.Semantics.val.

Parameter _clear_spec :
  forall a : Type,
  forall {aIh : Inhab a},
  forall {Ea : CFML.SepLifted.Enc a},
  forall _prog_p : loc,
  forall p : sequence a,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _clear (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_p) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (Stack_cfml p) _prog_p) (
    fun _ : Coq.Init.Datatypes.unit =>
    CFML.SepBase.SepBasicSetup.HS.repr (Stack_cfml (@empty a aIh)) _prog_p
  ).

Parameter _concat : CFML.Semantics.val.

Parameter _concat_spec :
  forall a : Type,
  forall {aIh : Inhab a},
  forall {Ea : CFML.SepLifted.Enc a},
  forall _prog_q1 : loc,
  forall q1 : sequence a,
  forall _prog_q2 : loc,
  forall q2 : sequence a,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _concat (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_q1) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_q2) Coq.Lists.List.nil
      )
    )
  ) (
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Stack_cfml q1) _prog_q1
    ) (CFML.SepBase.SepBasicSetup.HS.repr (Stack_cfml q2) _prog_q2)
  ) (
    fun _ : Coq.Init.Datatypes.unit =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Stack_cfml (app q1 q2)) _prog_q1
    ) (
      CFML.SepBase.SepBasicSetup.HS.repr (Stack_cfml (@empty a aIh)) _prog_q2
    )
  ).

Parameter _rev_append : CFML.Semantics.val.

Parameter _rev_append_spec :
  forall a : Type,
  forall {aIh : Inhab a},
  forall {Ea : CFML.SepLifted.Enc a},
  forall _prog_p1 : loc,
  forall p1 : sequence a,
  forall _prog_p2 : loc,
  forall p2 : sequence a,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _rev_append (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_p1) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_p2) Coq.Lists.List.nil
      )
    )
  ) (
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Stack_cfml p1) _prog_p1
    ) (CFML.SepBase.SepBasicSetup.HS.repr (Stack_cfml p2) _prog_p2)
  ) (
    fun _ : Coq.Init.Datatypes.unit =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Stack_cfml (@empty a aIh)) _prog_p1
    ) (
      CFML.SepBase.SepBasicSetup.HS.repr (Stack_cfml (app (rev p1) p2)) _prog_p2
    )
  ).


