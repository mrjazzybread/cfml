Set Implicit Arguments.

Require Import Gospel.

Require Coq.ZArith.BinInt TLC.LibLogic TLC.LibRelation TLC.LibInt TLC.LibListZ.

Require Import CFML.SepBase CFML.SepLifted CFML.WPLib CFML.WPLifted CFML.WPRecord CFML.WPArray CFML.WPBuiltin.

Require CFML.Stdlib.Array_ml CFML.Stdlib.List_ml CFML.Stdlib.Sys_ml.

Require Import Coq.ZArith.BinIntDef CFML.Semantics CFML.WPHeader.

Delimit Scope Z_scope with Z.

Definition valid  (n : Coq.Numbers.BinNums.Z) : Prop:=
Coq.Init.Logic.and (TLC.LibOrder.ge n (0)%Z) (
  TLC.LibOrder.lt n word_size
).

Parameter t : Type.

Context  (_Et : CFML.SepLifted.Enc t).

Parameter T :
  TLC.LibSet.set int ->
  t -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter singleton : CFML.Semantics.val.

Parameter _singleton_spec :
  forall _prog_v : int,
  forall v : int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps singleton (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make int _ _prog_v) Coq.Lists.List.nil
    )
  ) (
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Int v) _prog_v
    ) (CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (valid v))
  ) (
    fun _prog_s : t =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun s : TLC.LibSet.set int =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (Int v) _prog_v
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.HS.repr (T s) _prog_s
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
            Coq.Init.Logic.eq s (TLC.LibSet.single_impl v)
          )
        )
      )
    )
  ).

Parameter add : CFML.Semantics.val.

Parameter _add_spec :
  forall _prog_i : int,
  forall i : int,
  forall _prog_s1 : t,
  forall s1 : TLC.LibSet.set int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps add (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make int _ _prog_i) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make t _ _prog_s1) Coq.Lists.List.nil
      )
    )
  ) (
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Int i) _prog_i
    ) (
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (T s1) _prog_s1
      ) (CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (valid i))
    )
  ) (
    fun _prog_s2 : t =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun s2 : TLC.LibSet.set int =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (Int i) _prog_i
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.HS.repr (T s1) _prog_s1
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
            CFML.SepBase.SepBasicSetup.HS.repr (T s2) _prog_s2
          ) (
            CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
              Coq.Init.Logic.eq s2 (Gospel.add_set i s1)
            )
          )
        )
      )
    )
  ).

Parameter remove : CFML.Semantics.val.

Parameter _remove_spec :
  forall _prog_i : int,
  forall i : int,
  forall _prog_s1 : t,
  forall s1 : TLC.LibSet.set int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps remove (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make int _ _prog_i) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make t _ _prog_s1) Coq.Lists.List.nil
      )
    )
  ) (
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Int i) _prog_i
    ) (
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (T s1) _prog_s1
      ) (CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (valid i))
    )
  ) (
    fun _prog_s2 : t =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun s2 : TLC.LibSet.set int =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (Int i) _prog_i
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.HS.repr (T s1) _prog_s1
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
            CFML.SepBase.SepBasicSetup.HS.repr (T s2) _prog_s2
          ) (
            CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
              Coq.Init.Logic.eq s2 (
                TLC.LibSet.remove_impl s1 (TLC.LibSet.single_impl i)
              )
            )
          )
        )
      )
    )
  ).

Parameter is_singleton : CFML.Semantics.val.

Parameter _is_singleton_spec :
  forall _prog_s : t,
  forall s : TLC.LibSet.set int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps is_singleton (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make t _ _prog_s) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (T s) _prog_s) (
    fun _prog_b : bool =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun b : Prop =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (T s) _prog_s
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.HS.repr (Bool b) _prog_b
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
            Coq.Init.Logic.iff b (
              Coq.Init.Logic.ex (
                fun v : int =>
                Coq.Init.Logic.eq s (TLC.LibSet.single_impl v)
              )
            )
          )
        )
      )
    )
  ).


