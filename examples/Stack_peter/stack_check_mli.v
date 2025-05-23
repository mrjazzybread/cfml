Set Implicit Arguments.

Require Import gospelstdlib_verified.

Require Coq.ZArith.BinInt TLC.LibLogic TLC.LibRelation TLC.LibInt TLC.LibListZ.

Require Import CFML.SepBase CFML.SepLifted CFML.WPLib CFML.WPLifted CFML.WPRecord CFML.WPArray CFML.WPBuiltin.

Require CFML.Stdlib.Array_ml CFML.Stdlib.List_ml CFML.Stdlib.Sys_ml.

Require Import Coq.ZArith.BinIntDef CFML.Semantics CFML.WPHeader.

Delimit Scope Z_scope with Z.

Import Stdlib.

Import Gospelstdlib.

Import List.

Parameter t : Type -> Type.

Module Type Stack.

Parameter Stack :
  forall a : Type,  
  forall {Ea : CFML.SepLifted.Enc a},
  list a ->
  loc -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter create : CFML.Semantics.val.

Parameter create_spec :
  forall a : Type,
  forall {Ea : CFML.SepLifted.Enc a},
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps create (
      Coq.Lists.List.cons (
        @CFML.SepLifted.dyn_make CFML.Semantics.val _ Coq.Init.Datatypes.tt
      ) Coq.Lists.List.nil
    )
  ) CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hempty (
    fun _prog_q : loc =>
    CFML.SepBase.SepBasicSetup.HS.repr (Stack (@nil a )) _prog_q
  ).

Parameter is_empty : CFML.Semantics.val.

Parameter is_empty_spec :
  forall a : Type,
  forall {Ea : CFML.SepLifted.Enc a},
  forall _prog_q : loc,
  forall q : list a,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps is_empty (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_q) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (Stack q) _prog_q) (
    fun _prog_b : bool =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        hpure (_prog_b = isTrue (Coq.Init.Logic.eq q (@nil a)))
      ) (
        CFML.SepBase.SepBasicSetup.HS.repr (Stack q) _prog_q
    )
  ).

Parameter push : CFML.Semantics.val.

Parameter push_spec :
  forall a : Type,
  forall {Ea : CFML.SepLifted.Enc a},
  forall _prog_p : loc,
  forall p : list a,
  forall x : a,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps push (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_p) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make a _ x) Coq.Lists.List.nil
      )
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (Stack p) _prog_p) (
    fun _ : Coq.Init.Datatypes.unit =>
    CFML.SepBase.SepBasicSetup.HS.repr (Stack (cons x p)) _prog_p
  ).

Parameter pop : CFML.Semantics.val.

Parameter pop_spec :
  forall a : Type,
  forall {Ea : CFML.SepLifted.Enc a},
  forall _prog_p : loc,
  forall p : list a,
  Coq.Init.Logic.not (Coq.Init.Logic.eq p (@nil a)) ->
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps pop (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_p) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (Stack p) _prog_p) (
    fun r : a =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun _p_ : list a =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
          Coq.Init.Logic.eq p (cons r _p_)
        )
      ) (
        CFML.SepBase.SepBasicSetup.HS.repr (Stack _p_) _prog_p
      )
    )
    ).

Parameter clear : CFML.Semantics.val.

Parameter clear_spec :
  forall a : Type,  
  forall {Ea : CFML.SepLifted.Enc a},
  forall _prog_p : loc,
  forall p : list a,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps clear (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_p) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (Stack p) _prog_p) (
    fun _ : Coq.Init.Datatypes.unit =>
    CFML.SepBase.SepBasicSetup.HS.repr (Stack (@nil a )) _prog_p
  ).

Parameter concat : CFML.Semantics.val.

Parameter concat_spec :
  forall a : Type,
  forall {Ea : CFML.SepLifted.Enc a},
  forall _prog_q1 : loc,
  forall _prog_q2 : loc,    
  forall q1 : list a,
  forall q2 : list a,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps concat (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_q1) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_q2) Coq.Lists.List.nil
      )
    )
  ) (
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Stack q1) _prog_q1
    ) (CFML.SepBase.SepBasicSetup.HS.repr (Stack q2) _prog_q2)
  ) (
    fun _ : Coq.Init.Datatypes.unit =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Stack (q1 ++ q2)) _prog_q1
    ) (
      CFML.SepBase.SepBasicSetup.HS.repr (Stack (@nil a )) _prog_q2
    )
  ).

Parameter rev_append : CFML.Semantics.val.

Parameter rev_append_spec :
  forall a : Type,
  forall {Ea : CFML.SepLifted.Enc a},
  forall _prog_p1 : loc,
  forall _prog_p2 : loc,
  forall p1 : list a,
  forall p2 : list a,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps rev_append (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_p1) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_p2) Coq.Lists.List.nil
      )
    )
  ) (
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Stack p1) _prog_p1
    ) (CFML.SepBase.SepBasicSetup.HS.repr (Stack p2) _prog_p2)
  ) (
    fun _ : Coq.Init.Datatypes.unit =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Stack (@nil a )) _prog_p1
    ) (
      CFML.SepBase.SepBasicSetup.HS.repr (Stack (rev p1 ++ p2)) _prog_p2
    )
    ).

End Stack.
