Set Implicit Arguments.

Require Import gospelstdlib_verified.

Require Coq.ZArith.BinInt TLC.LibLogic TLC.LibRelation TLC.LibInt TLC.LibListZ.

Require Import CFML.SepBase CFML.SepLifted CFML.WPLib CFML.WPLifted CFML.WPRecord CFML.WPArray CFML.WPBuiltin.

Require CFML.Stdlib.Array_ml CFML.Stdlib.List_ml CFML.Stdlib.Sys_ml.

Require Import Coq.ZArith.BinIntDef CFML.Semantics CFML.WPHeader.

Delimit Scope Z_scope with Z.

Import Stdlib.

Import Gospelstdlib.

Import _Set.

Definition valid  (n : Coq.Numbers.BinNums.Z) : Prop:=
Coq.Init.Logic.and (ge n (0)%Z) (lt n Sys.word_size).

Parameter t : Type.

Parameter __Enc_t : CFML.SepLifted.Enc t.

Instance _Enc_t : CFML.SepLifted.Enc t := __Enc_t.

Parameter BitSet :
  set int -> t -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter _singleton : CFML.Semantics.val.

Lemma _singleton_spec :
  forall _prog_v : int,
  forall v : int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _singleton (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make int _ _prog_v) Coq.Lists.List.nil
    )
  ) (
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Int v) _prog_v
    ) (CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (valid v))
  ) (
    fun _prog_s : t =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Int v) _prog_v
    ) (CFML.SepBase.SepBasicSetup.HS.repr (BitSet (singleton v)) _prog_s)
  ). Admitted.

Parameter _add : CFML.Semantics.val.

Lemma _add_spec :
  forall _prog_i : int,
  forall i : int,
  forall _prog_s1 : t,
  forall s1 : set int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _add (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make int _ _prog_i) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make t _ _prog_s1) Coq.Lists.List.nil
      )
    )
  ) (
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Int i) _prog_i
    ) (
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (BitSet s1) _prog_s1
      ) (CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (valid i))
    )
  ) (
    fun _prog_s2 : t =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Int i) _prog_i
    ) (
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (BitSet s1) _prog_s1
      ) (CFML.SepBase.SepBasicSetup.HS.repr (BitSet (add i s1)) _prog_s2)
    )
  ). Admitted.

Parameter _remove : CFML.Semantics.val.

Lemma _remove_spec :
  forall _prog_i : int,
  forall i : int,
  forall _prog_s1 : t,
  forall s1 : set int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _remove (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make int _ _prog_i) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make t _ _prog_s1) Coq.Lists.List.nil
      )
    )
  ) (
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Int i) _prog_i
    ) (
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (BitSet s1) _prog_s1
      ) (CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (valid i))
    )
  ) (
    fun _prog_s2 : t =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Int i) _prog_i
    ) (
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (BitSet s1) _prog_s1
      ) (CFML.SepBase.SepBasicSetup.HS.repr (BitSet (remove i s1)) _prog_s2)
    )
  ). Admitted.

Parameter _is_singleton : CFML.Semantics.val.

Lemma _is_singleton_spec :
  forall _prog_s : t,
  forall s : set int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _is_singleton (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make t _ _prog_s) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (BitSet s) _prog_s) (
    fun _prog_b : bool =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (BitSet s) _prog_s
    ) (
      CFML.SepBase.SepBasicSetup.HS.repr (
        Bool (
          Coq.Init.Logic.ex (
            fun v : int =>
            Coq.Init.Logic.eq s (_Set.singleton v)
          )
        )
      ) _prog_b
    )
  ). Admitted.
