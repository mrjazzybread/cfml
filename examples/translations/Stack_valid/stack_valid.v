(* Created module type
   T -> Stack
   CFML example is now monomorphic
   Added aliases for ocaml functions
   removed underscore from spec names
   added hypothesis to pop
   general inlining.
   changed order of arguments.
   removed redundant representation predicate Int.
   changed is_empty so that it uses the isTrue predicate. 
 *)

Require Import Gospel.

Require Coq.ZArith.BinInt TLC.LibLogic TLC.LibRelation TLC.LibInt TLC.LibListZ.

Require Import CFML.SepBase CFML.SepLifted CFML.WPLib CFML.WPLifted CFML.WPRecord CFML.WPArray CFML.WPBuiltin.

Require CFML.Stdlib.Array_ml CFML.Stdlib.List_ml CFML.Stdlib.Sys_ml.

Require Import Coq.ZArith.BinIntDef CFML.Semantics CFML.WPHeader.

Module Type T.
Set Implicit Arguments.

Parameter Stack :
  Coq.Lists.List.list int ->
  loc -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter create : CFML.Semantics.val.

Parameter create_spec :
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps create (cons (@CFML.SepLifted.dyn_make unit _ tt) nil)
  ) CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hempty (
    fun _prog_p : loc =>
        CFML.SepBase.SepBasicSetup.HS.repr (Stack nil) _prog_p
    ). 

Parameter is_empty : CFML.Semantics.val.

Parameter is_empty_spec :
  forall _prog_q : loc,
  forall q : Coq.Lists.List.list int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps is_empty (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_q) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (Stack q) _prog_q) (
    fun b : bool =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
              Coq.Init.Logic.eq b (isTrue(Coq.Init.Logic.eq q Coq.Lists.List.nil))
            )

        ) (
          CFML.SepBase.SepBasicSetup.HS.repr (Stack q) _prog_q
        )
    ).
  
Parameter push : CFML.Semantics.val.

Parameter push_spec :
  forall _prog_p : loc,
  forall x : int,    
  forall p : Coq.Lists.List.list int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps push (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_p) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make int _ x) Coq.Lists.List.nil
      )
    )
    ) (CFML.SepBase.SepBasicSetup.HS.repr (Stack p) _prog_p) (
    fun _ : Coq.Init.Datatypes.unit =>
      CFML.SepBase.SepBasicSetup.HS.repr (Stack (Coq.Lists.List.cons x p)) _prog_p
  ).

Parameter pop : CFML.Semantics.val.

Parameter pop_spec :
  forall _prog_p : loc,
  forall p : Coq.Lists.List.list int,
    p <> nil ->
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps pop (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_p) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (Stack p) _prog_p) (
    fun r : int =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun _p' : Coq.Lists.List.list int =>
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar
          (
            CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
              Coq.Init.Logic.eq p (Coq.Lists.List.cons r _p')
            )
          )
          (
          CFML.SepBase.SepBasicSetup.HS.repr (Stack _p') _prog_p
        )         
      )
    )
  .

Parameter clear : CFML.Semantics.val.

Parameter clear_spec :
  forall _prog_p : loc,
  forall p : Coq.Lists.List.list int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps clear (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_p) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (Stack p) _prog_p) (
    fun _ : Coq.Init.Datatypes.unit =>
      CFML.SepBase.SepBasicSetup.HS.repr (Stack Coq.Lists.List.nil) _prog_p  
  ).

Parameter concat : CFML.Semantics.val.


Parameter concat_spec :
  forall _prog_q1 : loc,
  forall _prog_q2 : loc,
  forall q1 : Coq.Lists.List.list int,    
  forall q2 : Coq.Lists.List.list int,
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
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar
                        (
            CFML.SepBase.SepBasicSetup.HS.repr (Stack (TLC.LibList.app q1 q2)) _prog_q1
        )

        (
          CFML.SepBase.SepBasicSetup.HS.repr (Stack Coq.Lists.List.nil) _prog_q2
        )

      )
  .

Parameter rev_append : CFML.Semantics.val.

Parameter rev_append_spec :
  forall _prog_p1 : loc,
  forall _prog_p2 : loc,
  forall p1 : Coq.Lists.List.list int,
  forall p2 : Coq.Lists.List.list int,
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
          CFML.SepBase.SepBasicSetup.HS.repr (Stack Coq.Lists.List.nil) _prog_p1
        ) (
            CFML.SepBase.SepBasicSetup.HS.repr (Stack (TLC.LibList.app (rev p1) p2)) _prog_p2
    )
  ).



End T.
