Set Implicit Arguments.

Require Import Gospel.

Require Coq.ZArith.BinInt TLC.LibLogic TLC.LibRelation TLC.LibInt TLC.LibListZ.

Require Import CFML.SepBase CFML.SepLifted CFML.WPLib CFML.WPLifted CFML.WPRecord CFML.WPArray CFML.WPBuiltin.

Require CFML.Stdlib.Array_ml CFML.Stdlib.List_ml CFML.Stdlib.Sys_ml.

Require Import Coq.ZArith.BinIntDef CFML.Semantics CFML.WPHeader.

Delimit Scope Z_scope with Z.

Parameter T :
  (int -> Coq.Lists.List.list int) ->
  loc -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter create : CFML.Semantics.val.

Parameter _create_spec :
  forall _prog_n : int,
  forall n : int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps create (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make int _ _prog_n) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (Int n) _prog_n) (
    fun _prog_tbl : loc =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun tbl : int -> Coq.Lists.List.list int =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (Int n) _prog_n
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.HS.repr (T tbl) _prog_tbl
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
            Coq.Init.Logic.eq tbl (fun _ : int => Coq.Lists.List.nil)
          )
        )
      )
    )
  ).

Parameter clear : CFML.Semantics.val.

Parameter _clear_spec :
  forall _prog_tbl : loc,
  forall tbl : int -> Coq.Lists.List.list int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps clear (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_tbl) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (T tbl) _prog_tbl) (
    fun _ : Coq.Init.Datatypes.unit =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (T tbl) _prog_tbl
    ) (
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
        Coq.Init.Logic.eq tbl (fun _ : int => Coq.Lists.List.nil)
      )
    )
  ).

Parameter copy : CFML.Semantics.val.

Parameter _copy_spec :
  forall _prog_tbl : loc,
  forall tbl : int -> Coq.Lists.List.list int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps copy (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_tbl) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (T tbl) _prog_tbl) (
    fun _prog_c : loc =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun c : int -> Coq.Lists.List.list int =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (T tbl) _prog_tbl
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.HS.repr (T c) _prog_c
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
            forall k : int,
            Coq.Init.Logic.eq (tbl k) (c k)
          )
        )
      )
    )
  ).

Parameter add : CFML.Semantics.val.

Parameter _add_spec :
  forall _prog_tbl : loc,
  forall tbl : int -> Coq.Lists.List.list int,
  forall _prog_k : int,
  forall k : int,
  forall _prog_v : int,
  forall v : int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps add (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_tbl) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make int _ _prog_k) (
          Coq.Lists.List.cons (@CFML.SepLifted.dyn_make int _ _prog_v) Coq.Lists.List.nil
        )
      )
    )
  ) (
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (T tbl) _prog_tbl
    ) (
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (Int k) _prog_k
      ) (CFML.SepBase.SepBasicSetup.HS.repr (Int v) _prog_v)
    )
  ) (
    fun _ : Coq.Init.Datatypes.unit =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun _tbl' : int -> Coq.Lists.List.list int =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (T _tbl') _prog_tbl
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.HS.repr (Int k) _prog_k
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
            CFML.SepBase.SepBasicSetup.HS.repr (Int v) _prog_v
          ) (
            CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
              Coq.Init.Logic.eq _tbl' (
                Gospel.update tbl k (Coq.Lists.List.cons v (tbl k))
              )
            )
          )
        )
      )
    )
  ).

Parameter find_opt : CFML.Semantics.val.

Parameter _find_opt_spec :
  forall _prog_tbl : loc,
  forall tbl : int -> Coq.Lists.List.list int,
  forall _prog_k : int,
  forall k : int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps find_opt (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_tbl) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make int _ _prog_k) Coq.Lists.List.nil
      )
    )
  ) (
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (T tbl) _prog_tbl
    ) (CFML.SepBase.SepBasicSetup.HS.repr (Int k) _prog_k)
  ) (
    fun _prog_r : option int =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun r : option int =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (T tbl) _prog_tbl
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.HS.repr (Int k) _prog_k
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
            CFML.SepBase.SepBasicSetup.HS.repr (Option r) _prog_r
          ) (
            CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
              match r with
              | None => Coq.Init.Logic.eq (tbl k) Coq.Lists.List.nil
                | Some x => Coq.Init.Logic.eq (Gospel.hd (tbl k)) x
                end
            )
          )
        )
      )
    )
  ).

Parameter find_all : CFML.Semantics.val.

Parameter _find_all_spec :
  forall _prog_tbl : loc,
  forall tbl : int -> Coq.Lists.List.list int,
  forall _prog_k : int,
  forall k : int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps find_all (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_tbl) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make int _ _prog_k) Coq.Lists.List.nil
      )
    )
  ) (
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (T tbl) _prog_tbl
    ) (CFML.SepBase.SepBasicSetup.HS.repr (Int k) _prog_k)
  ) (
    fun _prog_l : list int =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun l : list int =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (T tbl) _prog_tbl
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.HS.repr (Int k) _prog_k
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
            CFML.SepBase.SepBasicSetup.HS.repr (List l) _prog_l
          ) (
            CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
              Coq.Init.Logic.eq l (tbl k)
            )
          )
        )
      )
    )
  ).

Parameter mem : CFML.Semantics.val.

Parameter _mem_spec :
  forall _prog_tbl : loc,
  forall tbl : int -> Coq.Lists.List.list int,
  forall _prog_k : int,
  forall k : int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps mem (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_tbl) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make int _ _prog_k) Coq.Lists.List.nil
      )
    )
  ) (
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (T tbl) _prog_tbl
    ) (CFML.SepBase.SepBasicSetup.HS.repr (Int k) _prog_k)
  ) (
    fun _prog_b : bool =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun b : Prop =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (T tbl) _prog_tbl
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.HS.repr (Int k) _prog_k
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
            CFML.SepBase.SepBasicSetup.HS.repr (Bool b) _prog_b
          ) (
            CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
              Coq.Init.Logic.iff b (
                Coq.Init.Logic.not (
                  Coq.Init.Logic.eq (tbl k) Coq.Lists.List.nil
                )
              )
            )
          )
        )
      )
    )
  ).

Parameter remove : CFML.Semantics.val.

Parameter _remove_spec :
  forall _prog_tbl : loc,
  forall tbl : int -> Coq.Lists.List.list int,
  forall _prog_k : int,
  forall k : int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps remove (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_tbl) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make int _ _prog_k) Coq.Lists.List.nil
      )
    )
  ) (
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (T tbl) _prog_tbl
    ) (CFML.SepBase.SepBasicSetup.HS.repr (Int k) _prog_k)
  ) (
    fun _ : Coq.Init.Datatypes.unit =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun _tbl' : int -> Coq.Lists.List.list int =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (T _tbl') _prog_tbl
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.HS.repr (Int k) _prog_k
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
            CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
              Coq.Init.Logic.eq (tbl k) Coq.Lists.List.nil ->
              Coq.Init.Logic.eq _tbl' tbl
            )
          ) (
            CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
              Coq.Init.Logic.not (
                Coq.Init.Logic.eq (_tbl' k) Coq.Lists.List.nil
              ) ->
              Coq.Init.Logic.eq _tbl' (Gospel.update tbl k (Gospel.tl (tbl k)))
            )
          )
        )
      )
    )
  ).

Parameter replace : CFML.Semantics.val.

Parameter _replace_spec :
  forall _prog_tbl : loc,
  forall tbl : int -> Coq.Lists.List.list int,
  forall _prog_k : int,
  forall k : int,
  forall _prog_v : int,
  forall v : int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps replace (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_tbl) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make int _ _prog_k) (
          Coq.Lists.List.cons (@CFML.SepLifted.dyn_make int _ _prog_v) Coq.Lists.List.nil
        )
      )
    )
  ) (
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (T tbl) _prog_tbl
    ) (
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (Int k) _prog_k
      ) (CFML.SepBase.SepBasicSetup.HS.repr (Int v) _prog_v)
    )
  ) (
    fun _ : Coq.Init.Datatypes.unit =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun _tbl' : int -> Coq.Lists.List.list int =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (T _tbl') _prog_tbl
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.HS.repr (Int k) _prog_k
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
            CFML.SepBase.SepBasicSetup.HS.repr (Int v) _prog_v
          ) (
            CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
              CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
                Coq.Init.Logic.eq (_tbl' k) Coq.Lists.List.nil ->
                Coq.Init.Logic.eq _tbl' (
                  Gospel.update _tbl' k (Gospel.singleton v)
                )
              )
            ) (
              CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
                Coq.Init.Logic.not (
                  Coq.Init.Logic.eq (_tbl' k) Coq.Lists.List.nil
                ) ->
                (
                  let '(tail) := Gospel.tl (tbl k) in
                  Coq.Init.Logic.eq _tbl' (
                    Gospel.update tbl k (Coq.Lists.List.cons v tail)
                  )
                )
              )
            )
          )
        )
      )
    )
  ).

Parameter length : CFML.Semantics.val.

Parameter _length_spec :
  forall _prog_tbl : loc,
  forall tbl : int -> Coq.Lists.List.list int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps length (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_tbl) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (T tbl) _prog_tbl) (
    fun _prog_n : int =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun n : int =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (T tbl) _prog_tbl
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.HS.repr (Int n) _prog_n
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
            Coq.Init.Logic.eq n (
              TLC.LibSet.card_impl (Gospel.domain Coq.Lists.List.nil tbl)
            )
          )
        )
      )
    )
  ).


