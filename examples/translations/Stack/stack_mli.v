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
    fun _prog_q : loc =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun q : Coq.Lists.List.list int =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (T q) _prog_q
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
          Coq.Init.Logic.eq q Coq.Lists.List.nil
        )
      )
    )
  ).

Parameter push : CFML.Semantics.val.

Parameter _push_spec :
  forall _prog_q : loc,
  forall q : Coq.Lists.List.list int,
  forall _prog_x : int,
  forall x : int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps push (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_q) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make int _ _prog_x) Coq.Lists.List.nil
      )
    )
  ) (
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (T q) _prog_q
    ) (CFML.SepBase.SepBasicSetup.HS.repr (Int x) _prog_x)
  ) (
    fun _ : Coq.Init.Datatypes.unit =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun _q' : Coq.Lists.List.list int =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (T _q') _prog_q
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.HS.repr (Int x) _prog_x
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
            Coq.Init.Logic.eq _q' (Coq.Lists.List.cons x q)
          )
        )
      )
    )
  ).

Parameter pop_opt : CFML.Semantics.val.

Parameter _pop_opt_spec :
  forall _prog_q : loc,
  forall q : Coq.Lists.List.list int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps pop_opt (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_q) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (T q) _prog_q) (
    fun _prog_r : option int =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun _q' : Coq.Lists.List.list int =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
        fun r : option int =>
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.HS.repr (T _q') _prog_q
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
            CFML.SepBase.SepBasicSetup.HS.repr (Option r) _prog_r
          ) (
            CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
              match r with
              | None => Coq.Init.Logic.and (
                  Coq.Init.Logic.eq q Coq.Lists.List.nil
                ) (Coq.Init.Logic.eq _q' Coq.Lists.List.nil)
                | Some r_val => Coq.Init.Logic.eq q (
                  Coq.Lists.List.cons r_val _q'
                )
                end
            )
          )
        )
      )
    )
  ).

Parameter top_opt : CFML.Semantics.val.

Parameter _top_opt_spec :
  forall _prog_q : loc,
  forall q : Coq.Lists.List.list int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps top_opt (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_q) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (T q) _prog_q) (
    fun _prog_r : option int =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun r : option int =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (T q) _prog_q
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.HS.repr (Option r) _prog_r
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
            match r with
            | None => Coq.Init.Logic.eq q Coq.Lists.List.nil
              | Some r => Coq.Init.Logic.and (
                Coq.Init.Logic.not (Coq.Init.Logic.eq q Coq.Lists.List.nil)
              ) (Coq.Init.Logic.eq r (Gospel.hd q))
              end
          )
        )
      )
    )
  ).

Parameter clear : CFML.Semantics.val.

Parameter _clear_spec :
  forall _prog_q : loc,
  forall q : Coq.Lists.List.list int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps clear (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_q) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (T q) _prog_q) (
    fun _ : Coq.Init.Datatypes.unit =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun _q' : Coq.Lists.List.list int =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (T _q') _prog_q
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
          Coq.Init.Logic.eq _q' Coq.Lists.List.nil
        )
      )
    )
  ).

Parameter copy : CFML.Semantics.val.

Parameter _copy_spec :
  forall _prog_q1 : loc,
  forall q1 : Coq.Lists.List.list int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps copy (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_q1) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (T q1) _prog_q1) (
    fun _prog_q2 : loc =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun q2 : Coq.Lists.List.list int =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (T q1) _prog_q1
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.HS.repr (T q2) _prog_q2
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
            Coq.Init.Logic.eq q2 q1
          )
        )
      )
    )
  ).

Parameter is_empty : CFML.Semantics.val.

Parameter _is_empty_spec :
  forall _prog_q : loc,
  forall q : Coq.Lists.List.list int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps is_empty (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_q) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (T q) _prog_q) (
    fun _prog_b : bool =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun b : Prop =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (T q) _prog_q
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.HS.repr (Bool b) _prog_b
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
            Coq.Init.Logic.iff b (Coq.Init.Logic.eq q Coq.Lists.List.nil)
          )
        )
      )
    )
  ).

Parameter length : CFML.Semantics.val.

Parameter _length_spec :
  forall _prog_q : loc,
  forall q : Coq.Lists.List.list int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps length (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_q) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (T q) _prog_q) (
    fun _prog_l : int =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun l : int =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (T q) _prog_q
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.HS.repr (Int l) _prog_l
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
            Coq.Init.Logic.eq (LibListZ.length q) l
          )
        )
      )
    )
  ).

Parameter transfer : CFML.Semantics.val.

Parameter _transfer_spec :
  forall _prog_q1 : loc,
  forall q1 : Coq.Lists.List.list int,
  forall _prog_q2 : loc,
  forall q2 : Coq.Lists.List.list int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps transfer (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_q1) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_q2) Coq.Lists.List.nil
      )
    )
  ) (
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (T q1) _prog_q1
    ) (CFML.SepBase.SepBasicSetup.HS.repr (T q2) _prog_q2)
  ) (
    fun _ : Coq.Init.Datatypes.unit =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun _q1' : Coq.Lists.List.list int =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
        fun _q2' : Coq.Lists.List.list int =>
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.HS.repr (T _q1') _prog_q1
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
            CFML.SepBase.SepBasicSetup.HS.repr (T _q2') _prog_q2
          ) (
            CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
              CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
                Coq.Init.Logic.eq _q1' Coq.Lists.List.nil
              )
            ) (
              CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
                Coq.Init.Logic.eq _q2' (Coq.Lists.List.app q2 q1)
              )
            )
          )
        )
      )
    )
    ).


