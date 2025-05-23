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

Parameter t : Type.

Parameter __Enc_t : CFML.SepLifted.Enc t.

Instance _Enc_t : CFML.SepLifted.Enc t := __Enc_t.

Parameter Dyn_array :
  sequence int ->
  loc -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter _create : CFML.Semantics.val.

Lemma _create_spec :
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _create (
      Coq.Lists.List.cons (
        @CFML.SepLifted.dyn_make CFML.Semantics.val _ Coq.Init.Datatypes.tt
      ) Coq.Lists.List.nil
    )
  ) CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hempty (
    fun _prog_a : loc =>
    CFML.SepBase.SepBasicSetup.HS.repr (Dyn_array empty) _prog_a
  ). Admitted.

Parameter _make : CFML.Semantics.val.

Lemma _make_spec :
  forall _prog_n : int,
  forall n : int,
  forall _prog_e : int,
  forall e : int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _make (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make int _ _prog_n) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make int _ _prog_e) Coq.Lists.List.nil
      )
    )
  ) (
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Int n) _prog_n
    ) (CFML.SepBase.SepBasicSetup.HS.repr (Int e) _prog_e)
  ) (
    fun _prog_a : loc =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Int n) _prog_n
    ) (
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (Int e) _prog_e
      ) (
        CFML.SepBase.SepBasicSetup.HS.repr (
          Dyn_array (init n (fun _ : Coq.Numbers.BinNums.Z => e))
        ) _prog_a
      )
    )
  ). Admitted.

Parameter _get : CFML.Semantics.val.

Lemma _get_spec :
  forall _prog_a : loc,
  forall a : sequence int,
  forall _prog_i : int,
  forall i : int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _get (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_a) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make int _ _prog_i) Coq.Lists.List.nil
      )
    )
  ) (
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Dyn_array a) _prog_a
    ) (CFML.SepBase.SepBasicSetup.HS.repr (Int i) _prog_i)
  ) (
    fun _prog_r : int =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Dyn_array a) _prog_a
    ) (
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (Int i) _prog_i
      ) (CFML.SepBase.SepBasicSetup.HS.repr (Int (seq_get a i)) _prog_r)
    )
  ). Admitted.

Parameter _set : CFML.Semantics.val.

Parameter _set_spec :
  forall _prog_a : loc,
  forall a : sequence int,
  forall _prog_i : int,
  forall i : int,
  forall _prog_e : int,
  forall e : int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _set (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_a) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make int _ _prog_i) (
          Coq.Lists.List.cons (@CFML.SepLifted.dyn_make int _ _prog_e) Coq.Lists.List.nil
        )
      )
    )
  ) (
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Dyn_array a) _prog_a
    ) (
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (Int i) _prog_i
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.HS.repr (Int e) _prog_e
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
            Coq.Init.Logic.and (le (0)%Z i) (lt i (length a))
          )
        )
      )
    )
  ) (
    fun _ : Coq.Init.Datatypes.unit =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Dyn_array (set a i e)) _prog_a
    ) (
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (Int i) _prog_i
      ) (CFML.SepBase.SepBasicSetup.HS.repr (Int e) _prog_e)
    )
  ).

Parameter _length : CFML.Semantics.val.

Parameter _length_spec :
  forall _prog_a : loc,
  forall a : sequence int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _length (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_a) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (Dyn_array a) _prog_a) (
    fun _prog_l : int =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun l : int =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (Dyn_array a) _prog_a
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.HS.repr (Int l) _prog_l
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
            Coq.Init.Logic.eq l (length a)
          )
        )
      )
    )
  ).

Parameter _is_empty : CFML.Semantics.val.

Parameter _is_empty_spec :
  forall _prog_a : loc,
  forall a : sequence int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _is_empty (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_a) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (Dyn_array a) _prog_a) (
    fun _prog_b : bool =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Dyn_array a) _prog_a
    ) (
      CFML.SepBase.SepBasicSetup.HS.repr (Bool (Coq.Init.Logic.eq a empty)) _prog_b
    )
  ).

Parameter _find_last : CFML.Semantics.val.

Parameter _find_last_spec :
  forall _prog_a : loc,
  forall a : sequence int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _find_last (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_a) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (Dyn_array a) _prog_a) (
    fun _prog_r : option int =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun r : option int =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (Dyn_array a) _prog_a
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.HS.repr (Option r) _prog_r
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
            match r with
            | None => Coq.Init.Logic.and (Coq.Init.Logic.eq a empty) (
                Coq.Init.Logic.eq a empty
              )
              | Some r => Coq.Init.Logic.eq r (
                seq_get a (minus (length a) (1)%Z)
              )
              end
          )
        )
      )
    )
  ).

Parameter _copy : CFML.Semantics.val.

Parameter _copy_spec :
  forall _prog_a : loc,
  forall a : sequence int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _copy (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_a) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (Dyn_array a) _prog_a) (
    fun _prog_c : loc =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Dyn_array a) _prog_a
    ) (CFML.SepBase.SepBasicSetup.HS.repr (Dyn_array a) _prog_c)
  ).

Parameter _add_last : CFML.Semantics.val.

Parameter _add_last_spec :
  forall _prog_a : loc,
  forall a : sequence int,
  forall _prog_e : int,
  forall e : int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _add_last (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_a) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make int _ _prog_e) Coq.Lists.List.nil
      )
    )
  ) (
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Dyn_array a) _prog_a
    ) (CFML.SepBase.SepBasicSetup.HS.repr (Int e) _prog_e)
  ) (
    fun _ : Coq.Init.Datatypes.unit =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Dyn_array (app a (singleton e))) _prog_a
    ) (CFML.SepBase.SepBasicSetup.HS.repr (Int e) _prog_e)
  ).

Parameter _append : CFML.Semantics.val.

Parameter _append_spec :
  forall _prog_a1 : loc,
  forall a1 : sequence int,
  forall _prog_a2 : loc,
  forall a2 : sequence int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _append (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_a1) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_a2) Coq.Lists.List.nil
      )
    )
  ) (
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Dyn_array a1) _prog_a1
    ) (CFML.SepBase.SepBasicSetup.HS.repr (Dyn_array a2) _prog_a2)
  ) (
    fun _ : Coq.Init.Datatypes.unit =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Dyn_array (app a1 a2)) _prog_a1
    ) (CFML.SepBase.SepBasicSetup.HS.repr (Dyn_array a2) _prog_a2)
  ).

Parameter _pop_last_opt : CFML.Semantics.val.

Parameter _pop_last_opt_spec :
  forall _prog_a : loc,
  forall a : sequence int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _pop_last_opt (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_a) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (Dyn_array a) _prog_a) (
    fun _prog_r : option int =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun _a_ : sequence int =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
        fun r : option int =>
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.HS.repr (Dyn_array _a_) _prog_a
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
            CFML.SepBase.SepBasicSetup.HS.repr (Option r) _prog_r
          ) (
            CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
              match r with
              | None => Coq.Init.Logic.and (Coq.Init.Logic.eq _a_ empty) (
                  Coq.Init.Logic.eq a empty
                )
                | Some r => Coq.Init.Logic.eq (app _a_ (singleton r)) a
                end
            )
          )
        )
      )
    )
  ).

Parameter _remove_last : CFML.Semantics.val.

Parameter _remove_last_spec :
  forall _prog_a : loc,
  forall a : sequence int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _remove_last (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_a) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (Dyn_array a) _prog_a) (
    fun _ : Coq.Init.Datatypes.unit =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun _a_ : sequence int =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (Dyn_array _a_) _prog_a
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
            Coq.Init.Logic.eq a empty -> Coq.Init.Logic.eq _a_ empty
          )
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
            Coq.Init.Logic.not (Coq.Init.Logic.eq _a_ empty) ->
            Coq.Init.Logic.eq _a_ (seq_sub_r a (minus (length a) (1)%Z))
          )
        )
      )
    )
  ).

Parameter _truncate : CFML.Semantics.val.

Parameter _truncate_spec :
  forall _prog_a : loc,
  forall a : sequence int,
  forall _prog_n : int,
  forall n : int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _truncate (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_a) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make int _ _prog_n) Coq.Lists.List.nil
      )
    )
  ) (
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Dyn_array a) _prog_a
    ) (
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (Int n) _prog_n
      ) (CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (ge n (0)%Z))
    )
  ) (
    fun _ : Coq.Init.Datatypes.unit =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun _a_ : sequence int =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (Dyn_array _a_) _prog_a
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.HS.repr (Int n) _prog_n
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
            CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
              ge n (length _a_) -> Coq.Init.Logic.eq _a_ a
            )
          ) (
            CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
              lt n (length _a_) -> Coq.Init.Logic.eq _a_ (seq_sub_r a n)
            )
          )
        )
      )
    )
  ).

Parameter _clear : CFML.Semantics.val.

Parameter _clear_spec :
  forall _prog_a : loc,
  forall a : sequence int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _clear (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_a) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (Dyn_array a) _prog_a) (
    fun _ : Coq.Init.Datatypes.unit =>
    CFML.SepBase.SepBasicSetup.HS.repr (Dyn_array empty) _prog_a
  ).
