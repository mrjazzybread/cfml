Set Implicit Arguments.

Require Import gospelstdlib_verified.
Require Coq.ZArith.BinInt TLC.LibLogic TLC.LibRelation TLC.LibInt TLC.LibListZ.

Require Import CFML.SepBase CFML.SepLifted CFML.WPLib CFML.WPLifted CFML.WPRecord CFML.WPArray CFML.WPBuiltin.

Require CFML.Stdlib.Array_ml CFML.Stdlib.List_ml CFML.Stdlib.Sys_ml.

Require Import Coq.ZArith.BinIntDef CFML.Semantics CFML.WPHeader.

Delimit Scope Z_scope with Z.

Import Stdlib.

Import Gospelstdlib.

Parameter memory : Type -> Type.

Parameter __Enc_memory : forall a : Type, CFML.SepLifted.Enc (memory a).

Instance _Enc_memory : forall a : Type, CFML.SepLifted.Enc (memory a) :=
__Enc_memory.

Parameter Memory :
  forall a : Type,
  forall {Ea : OCamlType a},
  memory a ->
  memory a -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter extend :
  forall a : Type,
  forall {aIh : OCamlType a},
  memory a -> memory a -> Prop.

Parameter refl :
  forall a : Type,
  forall {aIh : OCamlType a},
  CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.himpl CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hempty (
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hforall (
      fun m : memory a =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (extend m m)
    )
  ).

Parameter tran :
  forall a : Type,
  forall {aIh : OCamlType a},
  CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.himpl CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hempty (
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hforall (
      fun m1 : memory a =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hforall (
        fun m2 : memory a =>
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hforall (
          fun m3 : memory a =>
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
            extend m1 m2 -> extend m2 m3 -> extend m1 m3
          )
        )
      )
    )
  ).

Parameter _create_mem : CFML.Semantics.val.

Parameter _create_mem_spec :
  forall a : Type,
  forall {aIh : Inhab a},
  forall {Ea : CFML.SepLifted.Enc a},
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _create_mem (
      Coq.Lists.List.cons (
        @CFML.SepLifted.dyn_make CFML.Semantics.val _ Coq.Init.Datatypes.tt
      ) Coq.Lists.List.nil
    )
  ) CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hempty (
    fun _res_ : memory a =>
    let '(result) := _res_ in
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hempty
  ).

Lemma Estack :
  forall a : Type,
  forall {aIh : OCamlType a},
  (memory a -> sequence a) ->
  loc -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.
Admitted.

Lemma estack_mon :
  forall a : Type,
  forall {aIh : OCamlType a},
  CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.himpl CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hempty (
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hforall (
      fun m : memory a =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hforall (
        fun m' : memory a =>
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hforall (
          fun _prog_e : loc =>
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hforall (
            fun e : memory a -> sequence a =>
            CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hwand (
              CFML.SepBase.SepBasicSetup.HS.repr (Estack e) _prog_e
            ) (
              CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
                CFML.SepBase.SepBasicSetup.HS.repr (Estack e) _prog_e
              ) (
                CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
                  extend m m' -> Coq.Init.Logic.eq (e m) (e m')
                )
              )
            )
          )
        )
      )
    )
  ).

Parameter _ecreate : CFML.Semantics.val.

Parameter _ecreate_spec :
  forall a : Type,
  forall {aIh : OCamlType a},
  forall m : memory a,
  forall x : a,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _ecreate (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make (memory a) _ m) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make a _ x) Coq.Lists.List.nil
      )
    )
  ) CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hempty (
    fun _res_ : loc =>
    let '(_prog_r) := _res_ in
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun r : memory a -> sequence a =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (Estack r) _prog_r
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
          Coq.Init.Logic.eq (r m) (@Sequence.empty a _G)
        )
      )
    )
  ).

Parameter _epush : CFML.Semantics.val.

Parameter _epush_spec :
  forall a : Type,
  forall {aIh : OCamlType a},
  forall {Ea : CFML.SepLifted.Enc a},
  forall m : memory a,
  forall _prog_s : loc,
  forall s : memory a -> sequence a,
  forall x : a,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _epush (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make (memory a) _ m) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_s) (
          Coq.Lists.List.cons (@CFML.SepLifted.dyn_make a _ x) Coq.Lists.List.nil
        )
      )
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (Estack s) _prog_s) (
    fun _res_ : Coq.Init.Datatypes.unit =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun _s_ : memory a -> sequence a =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (Estack _s_) _prog_s
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
          Coq.Init.Logic.eq (_s_ m) (Sequence.cons x (s m))
        )
      )
    )
  ).

Parameter _epop : CFML.Semantics.val.

Parameter _epop_spec :
  forall a : Type,
  forall {aIh : OCamlType a},
  forall {Ea : CFML.SepLifted.Enc a},
  forall m : memory a,
  forall _prog_s : loc,
  forall s : memory a -> sequence a,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _epop (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make (memory a) _ m) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_s) Coq.Lists.List.nil
      )
    )
  ) (
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Estack s) _prog_s
    ) (
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
        Coq.Init.Logic.not (Coq.Init.Logic.eq (s m) (@Sequence.empty a _G))
      )
    )
  ) (
    fun _res_ : a =>
    let '(r) := _res_ in
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun _s_ : memory a -> sequence a =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (Estack _s_) _prog_s
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
          Coq.Init.Logic.eq (s m) (Sequence.cons r (_s_ m))
        )
      )
    )
  ).

Record pstack (a : Type) : Type := _mk_pstack {
  internal : unit;
  pview : memory a -> sequence a
}.

Parameter Pstack :
  forall a : Type,
  forall {aIh : Inhab a},
  forall {Ea : CFML.SepLifted.Enc a},
  pstack a -> loc -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter pstack_mon :
  forall a : Type,
  forall {aIh : Inhab a},
  forall {Ea : CFML.SepLifted.Enc a},
  CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.himpl CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hempty (
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hforall (
      fun m : memory a =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hforall (
        fun m' : memory a =>
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hforall (
          fun _prog_p : loc =>
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hforall (
            fun p : pstack a =>
            CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hwand (
              CFML.SepBase.SepBasicSetup.HS.repr (Pstack p) _prog_p
            ) (
              CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
                CFML.SepBase.SepBasicSetup.HS.repr (Pstack p) _prog_p
              ) (
                CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
                  extend m m' -> Coq.Init.Logic.eq ((pview p) m) ((pview p) m')
                )
              )
            )
          )
        )
      )
    )
  ).

Parameter _pcreate : CFML.Semantics.val.

Parameter _pcreate_spec :
  forall a : Type,
  forall {aIh : Inhab a},
  forall {Ea : CFML.SepLifted.Enc a},
  forall m : memory a,
  forall x : a,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _pcreate (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make (memory a) _ m) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make a _ x) Coq.Lists.List.nil
      )
    )
  ) CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hempty (
    fun _res_ : Coq.Init.Datatypes.prod loc (memory a) =>
    let '(_prog_r, m') := _res_ in
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun r : pstack a =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (Pstack r) _prog_r
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
            Coq.Init.Logic.eq ((pview r) m') (@Sequence.empty a aIh)
          )
        ) (CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (extend m m'))
      )
    )
  ).

Parameter _ppush : CFML.Semantics.val.

Parameter _ppush_spec :
  forall a : Type,
  forall {aIh : Inhab a},
  forall {Ea : CFML.SepLifted.Enc a},
  forall m : memory a,
  forall _prog_s : loc,
  forall s : pstack a,
  forall x : a,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _ppush (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make (memory a) _ m) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_s) (
          Coq.Lists.List.cons (@CFML.SepLifted.dyn_make a _ x) Coq.Lists.List.nil
        )
      )
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (Pstack s) _prog_s) (
    fun _res_ : Coq.Init.Datatypes.prod loc (memory a) =>
    let '(_prog_r, m') := _res_ in
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun _s_ : pstack a =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
        fun r : pstack a =>
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.HS.repr (Pstack _s_) _prog_s
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
            CFML.SepBase.SepBasicSetup.HS.repr (Pstack r) _prog_r
          ) (
            CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
              CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
                Coq.Init.Logic.eq ((pview r) m') (
                  Sequence.cons x ((pview _s_) m)
                )
              )
            ) (
              CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (extend m m')
            )
          )
        )
      )
    )
  ).

Parameter _ppop : CFML.Semantics.val.

Parameter _ppop_spec :
  forall a : Type,
  forall {aIh : Inhab a},
  forall {Ea : CFML.SepLifted.Enc a},
  forall m : memory a,
  forall _prog_s : loc,
  forall s : pstack a,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _ppop (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make (memory a) _ m) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_s) Coq.Lists.List.nil
      )
    )
  ) (
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Pstack s) _prog_s
    ) (
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
        Coq.Init.Logic.not (
          Coq.Init.Logic.eq ((pview s) m) (@Sequence.empty a aIh)
        )
      )
    )
  ) (
    fun _res_ : Coq.Init.Datatypes.prod loc a =>
    let '(_prog_rs, res) := _res_ in
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun _s_ : pstack a =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
        fun rs : pstack a =>
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.HS.repr (Pstack _s_) _prog_s
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
            CFML.SepBase.SepBasicSetup.HS.repr (Pstack rs) _prog_rs
          ) (
            CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
              Coq.Init.Logic.eq ((pview _s_) m) (
                Sequence.cons res ((pview rs) m)
              )
            )
          )
        )
      )
    )
  ).

Parameter _pstack_to_estack : CFML.Semantics.val.

Parameter _pstack_to_estack_spec :
  forall a : Type,
  forall {aIh : Inhab a},
  forall {Ea : CFML.SepLifted.Enc a},
  forall m : memory a,
  forall _prog_ps : loc,
  forall ps : pstack a,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _pstack_to_estack (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make (memory a) _ m) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_ps) Coq.Lists.List.nil
      )
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (Pstack ps) _prog_ps) (
    fun _res_ : loc =>
    let '(_prog_re) := _res_ in
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun re : memory a -> sequence a =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (Pstack ps) _prog_ps
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.HS.repr (Estack re) _prog_re
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
            Coq.Init.Logic.eq (re m) ((pview ps) m)
          )
        )
      )
    )
  ).

Parameter _estack_to_pstack : CFML.Semantics.val.

Parameter _estack_to_pstack_spec :
  forall a : Type,
  forall {aIh : Inhab a},
  forall {Ea : CFML.SepLifted.Enc a},
  forall m : memory a,
  forall _prog_es : loc,
  forall es : memory a -> sequence a,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _estack_to_pstack (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make (memory a) _ m) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_es) Coq.Lists.List.nil
      )
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (Estack es) _prog_es) (
    fun _res_ : Coq.Init.Datatypes.prod loc (memory a) =>
    let '(_prog_rp, m') := _res_ in
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun rp : pstack a =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (Pstack rp) _prog_rp
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
            Coq.Init.Logic.eq ((pview rp) m') (es m)
          )
        ) (CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (extend m m'))
      )
    )
  ).


