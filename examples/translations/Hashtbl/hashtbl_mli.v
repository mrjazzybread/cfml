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

Import Map.

Parameter Hashtbl :
  (int -> sequence int) ->
  loc -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter _create : CFML.Semantics.val.

Parameter _create_spec :
  forall n : int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _create (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make int _ n) Coq.Lists.List.nil
    )
  ) CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hempty (
    fun _res_ : loc =>
    let '(_prog_tbl) := _res_ in
    CFML.SepBase.SepBasicSetup.HS.repr (Hashtbl (fun _ : int => empty)) _prog_tbl
  ).

Parameter _clear : CFML.Semantics.val.

Parameter _clear_spec :
  forall _prog_tbl : loc,
  forall tbl : int -> sequence int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _clear (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_tbl) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (Hashtbl tbl) _prog_tbl) (
    fun _res_ : Coq.Init.Datatypes.unit =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Hashtbl tbl) _prog_tbl
    ) (
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
        Coq.Init.Logic.eq tbl (fun _ : int => empty)
      )
    )
  ).

Parameter _copy : CFML.Semantics.val.

Parameter _copy_spec :
  forall _prog_tbl : loc,
  forall tbl : int -> sequence int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _copy (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_tbl) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (Hashtbl tbl) _prog_tbl) (
    fun _res_ : loc =>
    let '(_prog_c) := _res_ in
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun c : int -> sequence int =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (Hashtbl tbl) _prog_tbl
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.HS.repr (Hashtbl c) _prog_c
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
            forall k : int,
            Coq.Init.Logic.eq (tbl k) (c k)
          )
        )
      )
    )
  ).

Parameter _add : CFML.Semantics.val.

Parameter _add_spec :
  forall _prog_tbl : loc,
  forall tbl : int -> sequence int,
  forall k : int,
  forall v : int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _add (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_tbl) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make int _ k) (
          Coq.Lists.List.cons (@CFML.SepLifted.dyn_make int _ v) Coq.Lists.List.nil
        )
      )
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (Hashtbl tbl) _prog_tbl) (
    fun _res_ : Coq.Init.Datatypes.unit =>
    CFML.SepBase.SepBasicSetup.HS.repr (
      Hashtbl (map_set tbl k (cons v (tbl k)))
    ) _prog_tbl
  ).

Parameter _find_opt : CFML.Semantics.val.

Parameter _find_opt_spec :
  forall _prog_tbl : loc,
  forall tbl : int -> sequence int,
  forall k : int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _find_opt (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_tbl) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make int _ k) Coq.Lists.List.nil
      )
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (Hashtbl tbl) _prog_tbl) (
    fun _res_ : option int =>
    let '(r) := _res_ in
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Hashtbl tbl) _prog_tbl
    ) (
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
        match r with
        | None => Coq.Init.Logic.eq (tbl k) empty
          | Some x => Coq.Init.Logic.eq (hd (tbl k)) x
          end
      )
    )
  ).

Parameter _find_all : CFML.Semantics.val.

Parameter _find_all_spec :
  forall _prog_tbl : loc,
  forall tbl : int -> sequence int,
  forall k : int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _find_all (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_tbl) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make int _ k) Coq.Lists.List.nil
      )
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (Hashtbl tbl) _prog_tbl) (
    fun _res_ : list int =>
    let '(l) := _res_ in
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Hashtbl tbl) _prog_tbl
    ) (
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
        Coq.Init.Logic.eq (of_list l) (tbl k)
      )
    )
  ).

Parameter _mem : CFML.Semantics.val.

Parameter _mem_spec :
  forall _prog_tbl : loc,
  forall tbl : int -> sequence int,
  forall k : int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _mem (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_tbl) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make int _ k) Coq.Lists.List.nil
      )
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (Hashtbl tbl) _prog_tbl) (
    fun _res_ : bool =>
    let '(b) := _res_ in
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Hashtbl tbl) _prog_tbl
    ) (
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
        Coq.Init.Logic.iff b (
          Coq.Init.Logic.not (Coq.Init.Logic.eq (tbl k) empty)
        )
      )
    )
  ).

Parameter _remove : CFML.Semantics.val.

Parameter _remove_spec :
  forall _prog_tbl : loc,
  forall tbl : int -> sequence int,
  forall k : int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _remove (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_tbl) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make int _ k) Coq.Lists.List.nil
      )
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (Hashtbl tbl) _prog_tbl) (
    fun _res_ : Coq.Init.Datatypes.unit =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun _tbl_ : int -> sequence int =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (Hashtbl _tbl_) _prog_tbl
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
            Coq.Init.Logic.eq (tbl k) empty -> Coq.Init.Logic.eq _tbl_ tbl
          )
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
            Coq.Init.Logic.not (Coq.Init.Logic.eq (_tbl_ k) empty) ->
            Coq.Init.Logic.eq _tbl_ (map_set tbl k (tl (tbl k)))
          )
        )
      )
    )
  ).

Parameter _replace : CFML.Semantics.val.

Parameter _replace_spec :
  forall _prog_tbl : loc,
  forall tbl : int -> sequence int,
  forall k : int,
  forall v : int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _replace (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_tbl) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make int _ k) (
          Coq.Lists.List.cons (@CFML.SepLifted.dyn_make int _ v) Coq.Lists.List.nil
        )
      )
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (Hashtbl tbl) _prog_tbl) (
    fun _res_ : Coq.Init.Datatypes.unit =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun _tbl_ : int -> sequence int =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (Hashtbl _tbl_) _prog_tbl
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
            Coq.Init.Logic.eq (_tbl_ k) empty ->
            Coq.Init.Logic.eq _tbl_ (map_set _tbl_ k (singleton v))
          )
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
            Coq.Init.Logic.not (Coq.Init.Logic.eq (_tbl_ k) empty) ->
            (
              let '(tail) := tl (tbl k) in
              Coq.Init.Logic.eq _tbl_ (map_set tbl k (cons v tail))
            )
          )
        )
      )
    )
  ).

Parameter _length : CFML.Semantics.val.

Parameter _length_spec :
  forall _prog_tbl : loc,
  forall tbl : int -> sequence int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps _length (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _prog_tbl) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (Hashtbl tbl) _prog_tbl) (
    fun _res_ : int =>
    let '(n) := _res_ in
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (Hashtbl tbl) _prog_tbl
    ) (
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
        Coq.Init.Logic.eq n (_Set.cardinal (domain empty tbl))
      )
    )
  ).


