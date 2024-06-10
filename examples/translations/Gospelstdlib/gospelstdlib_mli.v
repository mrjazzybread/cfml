Set Implicit Arguments.

Require Import Gospel.

Require Coq.ZArith.BinInt TLC.LibLogic TLC.LibRelation TLC.LibInt TLC.LibListZ.

Require Import CFML.SepBase CFML.SepLifted CFML.WPLib CFML.WPLifted CFML.WPRecord CFML.WPArray CFML.WPBuiltin.

Require CFML.Stdlib.Array_ml CFML.Stdlib.List_ml CFML.Stdlib.Sys_ml.

Require Import Coq.ZArith.BinIntDef CFML.Semantics CFML.WPHeader.

Delimit Scope Z_scope with Z.

Parameter sequence : Type -> Type.

Parameter Sequence :
  forall A : Type,
  forall AIh : Inhab Type,
  sequence A ->
  sequence A -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter bag : Type -> Type.

Parameter Bag :
  forall A : Type,
  forall AIh : Inhab Type,
  bag A -> bag A -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter set : Type -> Type.

Parameter _Set :
  forall A : Type,
  forall AIh : Inhab Type,
  set A -> set A -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter map : Type -> Type -> Type.

Parameter Map :
  forall A : Type,
  forall B : Type,
  forall AIh : Inhab Type,
  forall BIh : Inhab Type,
  map A B ->
  map A B -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter succ : Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z.

Parameter pred : Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z.

Parameter neg : Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z.

Parameter add :
  Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z.

Parameter minus :
  Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z.

Parameter mult :
  Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z.

Parameter div :
  Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z.

Parameter _mod :
  Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z.

Parameter pow :
  Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z.

Parameter abs : Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z.

Parameter min :
  Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z.

Parameter max :
  Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z.

Parameter gt : Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z -> Prop.

Parameter ge : Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z -> Prop.

Parameter lt : Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z -> Prop.

Parameter le : Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z -> Prop.

Parameter max_int : Coq.Numbers.BinNums.Z.

Parameter min_int : Coq.Numbers.BinNums.Z.

Parameter app :
  forall A : Type,
  forall AIh : Inhab Type,
  sequence A -> sequence A -> sequence A.

Parameter seq_get :
  forall A : Type,
  forall AIh : Inhab Type,
  sequence A -> Coq.Numbers.BinNums.Z -> A.

Parameter length :
  forall A : Type,
  forall AIh : Inhab Type,
  sequence A -> Coq.Numbers.BinNums.Z.

Parameter seq_sub :
  forall A : Type,
  forall AIh : Inhab Type,
  sequence A ->
  Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z -> sequence A.

Definition seq_sub_l  (A : Type) (AIh : Inhab Type) (s : sequence A) (
  i : Coq.Numbers.BinNums.Z
) : sequence A:=
seq_sub s i (length s).

Definition seq_sub_r  (A : Type) (AIh : Inhab Type) (s : sequence A) (
  i : Coq.Numbers.BinNums.Z
) : sequence A:=
seq_sub s (0)%Z i.

Definition map_set  (A : Type) (B : Type) (AIh : Inhab Type) (
  BIh : Inhab Type
) (f : A -> B) (x : A) (y : B) : A -> B:=
fun arg : A =>
if classicT (Coq.Init.Logic.eq arg x) then y else f x.

Module Sequence.

Parameter t : Type -> Type.

Parameter T :
  forall A : Type,
  forall AIh : Inhab Type,
  t A -> t A -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Definition in_range  (A : Type) (AIh : Inhab Type) (s : sequence A) (
  i : Coq.Numbers.BinNums.Z
) : Prop:=
Coq.Init.Logic.and (le (0)%Z i) (lt i (length s)).

Definition length  (A : Type) (AIh : Inhab Type) (s : sequence A) : Coq.Numbers.BinNums.Z:=
length s.

Parameter length_nonneg :
  forall A11 : Type,
  forall s : sequence A11,
  le (0)%Z (length s).

Parameter append_length :
  forall A17 : Type,
  forall s : sequence A17,
  forall s' : sequence A17,
  Coq.Init.Logic.eq (length (app s s')) (add (length s) (length s')).

Parameter append_elems_left :
  forall A26 : Type,
  forall s : sequence A26,
  forall s' : sequence A26,
  forall i : Coq.Numbers.BinNums.Z,
  Coq.Init.Logic.and (le i (0)%Z) (lt (0)%Z (length s)) ->
  Coq.Init.Logic.eq (seq_get (app s s') i) (seq_get s i).

Parameter append_elems_right :
  forall A37 : Type,
  forall s : sequence A37,
  forall s' : sequence A37,
  forall i : Coq.Numbers.BinNums.Z,
  Coq.Init.Logic.and (le (length s) i) (lt i (add (length s) (length s'))) ->
  Coq.Init.Logic.eq (seq_get (app s s') (add i (length s))) (seq_get s' i).

Parameter subseq :
  forall A45 : Type,
  forall s : sequence A45,
  forall i : Coq.Numbers.BinNums.Z,
  forall i1 : Coq.Numbers.BinNums.Z,
  forall i2 : Coq.Numbers.BinNums.Z,
  Coq.Init.Logic.and (le i1 i) (lt i i2) ->
  Coq.Init.Logic.eq (seq_get s i) (seq_get (seq_sub s i1 i2) (minus i i1)).

Parameter init :
  forall A : Type,
  forall AIh : Inhab Type,
  Coq.Numbers.BinNums.Z -> (Coq.Numbers.BinNums.Z -> A) -> sequence A.

Parameter init_length :
  forall A49 : Type,
  forall n : Coq.Numbers.BinNums.Z,
  forall f : Coq.Numbers.BinNums.Z -> A49,
  ge n (0)%Z -> Coq.Init.Logic.eq (length (init n f)) n.

Parameter init_elems :
  forall A57 : Type,
  forall n : Coq.Numbers.BinNums.Z,
  forall f : Coq.Numbers.BinNums.Z -> A57,
  forall i : Coq.Numbers.BinNums.Z,
  Coq.Init.Logic.and (le (0)%Z i) (lt i n) ->
  Coq.Init.Logic.eq (seq_get (init n f) i) (f i).

Parameter empty : forall A : Type, forall AIh : Inhab Type, sequence A.

Parameter empty_length : Coq.Init.Logic.eq (length empty) (0)%Z.

Definition singleton  (A : Type) (AIh : Inhab Type) (x : A) : sequence A:=
init (1)%Z (fun _ : Coq.Numbers.BinNums.Z => x).

Definition cons  (A : Type) (AIh : Inhab Type) (x : A) (s : sequence A) : sequence A:=
app (singleton x) s.

Definition snoc  (A : Type) (AIh : Inhab Type) (s : sequence A) (x : A) : sequence A:=
app s (singleton x).

Definition hd  (A : Type) (AIh : Inhab Type) (s : sequence A) : A:=
seq_get s (0)%Z.

Definition tl  (A : Type) (AIh : Inhab Type) (s : sequence A) : sequence A:=
seq_sub_l s (1)%Z.

Definition append  (A : Type) (AIh : Inhab Type) (s1 : sequence A) (
  s2 : sequence A
) : sequence A:=
app s1 s2.

Parameter multiplicity :
  forall A : Type,
  forall AIh : Inhab Type,
  A -> sequence A -> Coq.Numbers.BinNums.Z.

Parameter mult_empty :
  forall A73 : Type,
  forall x : A73,
  Coq.Init.Logic.eq (multiplicity x empty) (0)%Z.

Parameter mult_cons :
  forall A79 : Type,
  forall s : sequence A79,
  forall x : A79,
  Coq.Init.Logic.eq (add (1)%Z (multiplicity x s)) (
    multiplicity x (cons x s)
  ).

Parameter mult_cons_neutral :
  forall A87 : Type,
  forall s : sequence A87,
  forall x1 : A87,
  forall x2 : A87,
  Coq.Init.Logic.not (Coq.Init.Logic.eq x1 x2) ->
  Coq.Init.Logic.eq (multiplicity x1 s) (multiplicity x1 (cons x2 s)).

Parameter mult_length :
  forall A92 : Type,
  forall x : A92,
  forall s : sequence A92,
  Coq.Init.Logic.and (le (0)%Z (multiplicity x s)) (
    le (multiplicity x s) (length s)
  ).

Definition mem  (A : Type) (AIh : Inhab Type) (x : A) (s : sequence A) : Prop:=
gt (multiplicity x s) (0)%Z.

Parameter map :
  forall A : Type,
  forall B : Type,
  forall AIh : Inhab Type,
  forall BIh : Inhab Type,
  (A -> B) -> sequence A -> sequence B.

Parameter map_elems :
  forall A101 : Type,
  forall A103 : Type,
  forall i : Coq.Numbers.BinNums.Z,
  forall f : A101 -> A103,
  forall s : sequence A101,
  Coq.Init.Logic.and (le (0)%Z i) (lt i (length s)) ->
  Coq.Init.Logic.eq (seq_get (map f s) i) (f (seq_get s i)).

Parameter filter :
  forall A : Type,
  forall AIh : Inhab Type,
  (A -> Prop) -> sequence A -> sequence A.

Parameter filter_elems :
  forall A110 : Type,
  forall f : A110 -> bool,
  forall s : sequence A110,
  forall x : A110,
  mem x s -> f x -> mem x (filter f s).

Definition get  (A : Type) (AIh : Inhab Type) (s : sequence A) (
  i : Coq.Numbers.BinNums.Z
) : A:=
seq_get s i.

Parameter set :
  forall A : Type,
  forall AIh : Inhab Type,
  sequence A -> Coq.Numbers.BinNums.Z -> A -> sequence A.

Parameter set_elem :
  forall A118 : Type,
  forall s : sequence A118,
  forall i : Coq.Numbers.BinNums.Z,
  forall x : A118,
  Coq.Init.Logic.and (le (0)%Z i) (lt i (length s)) ->
  Coq.Init.Logic.eq (seq_get (set s i x) i) x.

Parameter set_elem_other :
  forall A129 : Type,
  forall s : sequence A129,
  forall i1 : Coq.Numbers.BinNums.Z,
  forall i2 : Coq.Numbers.BinNums.Z,
  forall x : A129,
  Coq.Init.Logic.not (Coq.Init.Logic.eq i1 i2) ->
  Coq.Init.Logic.and (le (0)%Z i1) (lt i1 (length s)) ->
  Coq.Init.Logic.and (le (0)%Z i2) (lt i2 (length s)) ->
  Coq.Init.Logic.eq (seq_get (set s i1 x) i2) (seq_get s i2).

Parameter of_list :
  forall A : Type,
  forall AIh : Inhab Type,
  list A -> sequence A.

Parameter rev :
  forall A : Type,
  forall AIh : Inhab Type,
  sequence A -> sequence A.

Parameter rev_length :
  forall A133 : Type,
  forall s : sequence A133,
  Coq.Init.Logic.eq (length s) (length (rev s)).

Parameter rev_elems :
  forall A142 : Type,
  forall i : Coq.Numbers.BinNums.Z,
  forall s : sequence A142,
  Coq.Init.Logic.and (le (0)%Z i) (lt i (length s)) ->
  Coq.Init.Logic.eq (seq_get (rev s) i) (
    seq_get s (minus (minus (length s) (1)%Z) i)
  ).

Parameter fold :
  forall A : Type,
  forall B : Type,
  forall AIh : Inhab Type,
  forall BIh : Inhab Type,
  (A -> B -> A) -> A -> sequence B -> A.

Parameter fold_empty :
  forall A147 : Type,
  forall A148 : Type,
  forall f : A148 -> A147 -> A148,
  forall acc : A148,
  Coq.Init.Logic.eq (fold f acc empty) acc.

Parameter fold_cons :
  forall A159 : Type,
  forall A160 : Type,
  forall f : A160 -> A159 -> A160,
  forall acc : A160,
  forall x : A159,
  forall l : sequence A159,
  Coq.Init.Logic.eq (fold f acc (cons x l)) (fold f (f acc x) l).

Parameter extensionality :
  forall A170 : Type,
  forall s1 : sequence A170,
  forall s2 : sequence A170,
  Coq.Init.Logic.eq (length s1) (length s2) ->
  (
    forall i : Coq.Numbers.BinNums.Z,
    Coq.Init.Logic.and (le (0)%Z i) (lt i (length s1)) ->
    Coq.Init.Logic.eq (seq_get s1 i) (seq_get s2 i)
  ) ->
  Coq.Init.Logic.eq s1 s2.

Parameter of_list :
  forall A : Type,
  forall AIh : Inhab Type,
  list A -> sequence A.

Parameter fold_left :
  forall A : Type,
  forall B : Type,
  forall AIh : Inhab Type,
  forall BIh : Inhab Type,
  (A -> B -> A) -> A -> sequence B -> A.

Parameter fold_right :
  forall A : Type,
  forall B : Type,
  forall AIh : Inhab Type,
  forall BIh : Inhab Type,
  (B -> A -> A) -> sequence B -> A -> A.

End Sequence.

Module Bag.

Parameter t : Type -> Type.

Parameter T :
  forall A : Type,
  forall AIh : Inhab Type,
  t A -> t A -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter multiplicity :
  forall A : Type,
  forall AIh : Inhab Type,
  A -> bag A -> Coq.Numbers.BinNums.Z.

Parameter well_formed :
  forall A174 : Type,
  forall b : A174,
  forall x : bag A174,
  ge (multiplicity b x) (0)%Z.

Parameter empty : forall A : Type, forall AIh : Inhab Type, bag A.

Parameter empty_mult :
  forall A177 : Type,
  forall x : A177,
  Coq.Init.Logic.eq (multiplicity x empty) (0)%Z.

Parameter init :
  forall A : Type,
  forall AIh : Inhab Type,
  (A -> Coq.Numbers.BinNums.Z) -> bag A.

Parameter init_axiom :
  forall A183 : Type,
  forall f : A183 -> Coq.Numbers.BinNums.Z,
  forall x : A183,
  Coq.Init.Logic.eq (min (0)%Z (f x)) (multiplicity x (init f)).

Parameter add :
  forall A : Type,
  forall AIh : Inhab Type,
  A -> bag A -> bag A.

Parameter add_mult_x :
  forall A189 : Type,
  forall b : bag A189,
  forall x : A189,
  Coq.Init.Logic.eq (multiplicity x (add x b)) (
    add (1)%Z (multiplicity x b)
  ).

Parameter add_mult_neg_x :
  forall A196 : Type,
  forall x : A196,
  forall y : A196,
  forall b : bag A196,
  Coq.Init.Logic.not (Coq.Init.Logic.eq x y) ->
  Coq.Init.Logic.eq (multiplicity y (add x b)) (0)%Z.

Definition singleton  (A : Type) (AIh : Inhab Type) (x : A) : bag A:=
add x empty.

Definition mem  (A : Type) (AIh : Inhab Type) (x : A) (b : bag A) : Prop:=
gt (multiplicity x b) (0)%Z.

Parameter remove :
  forall A : Type,
  forall AIh : Inhab Type,
  A -> bag A -> bag A.

Parameter add_mult_x :
  forall A205 : Type,
  forall b : bag A205,
  forall x : A205,
  Coq.Init.Logic.eq (multiplicity x (remove x b)) (
    minus (multiplicity x b) (1)%Z
  ).

Parameter add_mult_neg_x :
  forall A212 : Type,
  forall x : A212,
  forall y : A212,
  forall b : bag A212,
  Coq.Init.Logic.not (Coq.Init.Logic.eq x y) ->
  Coq.Init.Logic.eq (multiplicity y (remove x b)) (0)%Z.

Parameter union :
  forall A : Type,
  forall AIh : Inhab Type,
  bag A -> bag A -> bag A.

Parameter union_all :
  forall A220 : Type,
  forall b : bag A220,
  forall b' : bag A220,
  forall x : A220,
  Coq.Init.Logic.eq (max (multiplicity x b) (multiplicity x b')) (
    multiplicity x (union b b')
  ).

Parameter sum :
  forall A : Type,
  forall AIh : Inhab Type,
  bag A -> bag A -> bag A.

Parameter sum_all :
  forall A228 : Type,
  forall b : bag A228,
  forall b' : bag A228,
  forall x : A228,
  Coq.Init.Logic.eq (add (multiplicity x b) (multiplicity x b')) (
    multiplicity x (sum b b')
  ).

Parameter inter :
  forall A : Type,
  forall AIh : Inhab Type,
  bag A -> bag A -> bag A.

Parameter inter_all :
  forall A236 : Type,
  forall b : bag A236,
  forall b' : bag A236,
  forall x : A236,
  Coq.Init.Logic.eq (min (multiplicity x b) (multiplicity x b')) (
    multiplicity x (inter b b')
  ).

Parameter diff :
  forall A : Type,
  forall AIh : Inhab Type,
  bag A -> bag A -> bag A.

Parameter inter_all :
  forall A244 : Type,
  forall b : bag A244,
  forall b' : bag A244,
  forall x : A244,
  Coq.Init.Logic.eq (
    max (0)%Z (minus (multiplicity x b) (multiplicity x b'))
  ) (multiplicity x (diff b b')).

Definition disjoint  (A : Type) (AIh : Inhab Type) (b : bag A) (
  b' : bag A
) : Prop:=
forall A : Type,
forall x : A,
mem x b -> Coq.Init.Logic.not (mem x b').

Definition subset  (A : Type) (AIh : Inhab Type) (b : bag A) (
  b' : bag A
) : Prop:=
forall A : Type,
forall x : A,
le (multiplicity x b) (multiplicity x b').

Parameter filter :
  forall A : Type,
  forall AIh : Inhab Type,
  (A -> Prop) -> bag A -> bag A.

Parameter filter_mem :
  forall A258 : Type,
  forall b : bag A258,
  forall x : A258,
  forall f : A258 -> bool,
  f x ->
  Coq.Init.Logic.eq (multiplicity x (filter f b)) (multiplicity x b).

Parameter filter_mem_neg :
  forall A265 : Type,
  forall b : bag A265,
  forall x : A265,
  forall f : A265 -> bool,
  Coq.Init.Logic.not (f x) ->
  Coq.Init.Logic.eq (multiplicity x (filter f b)) (0)%Z.

Parameter cardinal :
  forall A : Type,
  forall AIh : Inhab Type,
  bag A -> Coq.Numbers.BinNums.Z.

Definition finite  (A : Type) (AIh : Inhab Type) (b : bag A) : Prop:=
forall A : Type,
Coq.Init.Logic.ex (
  fun s : sequence A =>
  forall x : A,
  mem x b -> mem x s
).

Parameter card_nonneg :
  forall A272 : Type,
  forall b : bag A272,
  ge (cardinal b) (0)%Z.

Parameter card_empty :
  forall A273 : Type,
  forall b : A273,
  Coq.Init.Logic.eq (cardinal empty) (0)%Z.

Parameter card_singleton :
  forall A279 : Type,
  forall x : A279,
  Coq.Init.Logic.eq (cardinal (singleton x)) (1)%Z.

Parameter card_union :
  forall A288 : Type,
  forall b1 : bag A288,
  forall b2 : bag A288,
  finite b1 ->
  finite b2 ->
  Coq.Init.Logic.eq (cardinal (union b1 b2)) (
    add (cardinal b1) (cardinal b2)
  ).

Parameter card_add :
  forall A295 : Type,
  forall x : bag (bag A295),
  forall b : bag A295,
  finite b ->
  Coq.Init.Logic.eq (cardinal (add b x)) (add (cardinal b) (1)%Z).

Parameter card_map :
  forall A302 : Type,
  forall f : A302 -> bool,
  forall b : bag A302,
  finite b -> le (cardinal (filter f b)) (cardinal b).

Parameter of_seq :
  forall A : Type,
  forall AIh : Inhab Type,
  sequence A -> bag A.

Parameter of_seq_multiplicity :
  forall A307 : Type,
  forall s : sequence A307,
  forall x : A307,
  Coq.Init.Logic.eq (multiplicity x s) (multiplicity x (of_seq s)).

End Bag.

Parameter mixfix {} : forall A : Type, forall AIh : Inhab Type, set A.

Module Set.

Parameter t : Type -> Type.

Parameter T :
  forall A : Type,
  forall AIh : Inhab Type,
  t A -> t A -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter mem :
  forall A : Type,
  forall AIh : Inhab Type,
  A -> set A -> Prop.

Parameter empty : forall A : Type, forall AIh : Inhab Type, set A.

Parameter empty_mem :
  forall A311 : Type,
  forall x : A311,
  Coq.Init.Logic.not (mem x empty).

Parameter add :
  forall A : Type,
  forall AIh : Inhab Type,
  A -> set A -> set A.

Parameter add_mem :
  forall A315 : Type,
  forall s : set A315,
  forall x : A315,
  mem x (add x s).

Parameter add_mem_neq :
  forall A322 : Type,
  forall s : set A322,
  forall x : A322,
  forall y : A322,
  Coq.Init.Logic.not (Coq.Init.Logic.eq x y) ->
  Coq.Init.Logic.iff (mem x s) (mem x (add y s)).

Definition singleton  (A : Type) (AIh : Inhab Type) (x : A) : set A:=
add x empty.

Parameter remove :
  forall A : Type,
  forall AIh : Inhab Type,
  A -> set A -> set A.

Parameter remove_mem :
  forall A328 : Type,
  forall s : set A328,
  forall x : A328,
  Coq.Init.Logic.not (mem x (add x s)).

Parameter remove_mem_neq :
  forall A335 : Type,
  forall s : set A335,
  forall x : A335,
  forall y : A335,
  Coq.Init.Logic.not (Coq.Init.Logic.eq x y) ->
  Coq.Init.Logic.iff (mem x s) (mem x (add y s)).

Parameter union :
  forall A : Type,
  forall AIh : Inhab Type,
  set A -> set A -> set A.

Parameter union_mem :
  forall A342 : Type,
  forall s : set A342,
  forall s' : set A342,
  forall x : A342,
  Coq.Init.Logic.or (mem x s) (mem x s') -> mem x (union s s').

Parameter union_mem_neg :
  forall A349 : Type,
  forall s : set A349,
  forall s' : set A349,
  forall x : A349,
  Coq.Init.Logic.not (mem x s) ->
  Coq.Init.Logic.not (mem x s') -> Coq.Init.Logic.not (mem x (union s s')).

Parameter inter :
  forall A : Type,
  forall AIh : Inhab Type,
  set A -> set A -> set A.

Parameter inter_mem :
  forall A356 : Type,
  forall s : set A356,
  forall s' : set A356,
  forall x : A356,
  mem x s -> mem x s' -> mem x (inter s s').

Parameter inter_mem_neq :
  forall A363 : Type,
  forall s : set A363,
  forall s' : set A363,
  forall x : A363,
  Coq.Init.Logic.not (Coq.Init.Logic.or (mem x s) (mem x s')) ->
  Coq.Init.Logic.not (mem x (union s s')).

Definition disjoint  (A : Type) (AIh : Inhab Type) (s : set A) (
  s' : set A
) : Prop:=
Coq.Init.Logic.eq (inter s s') empty.

Parameter diff :
  forall A : Type,
  forall AIh : Inhab Type,
  set A -> set A -> set A.

Parameter diff_mem :
  forall A372 : Type,
  forall s : set A372,
  forall s' : set A372,
  forall x : A372,
  mem x s' -> Coq.Init.Logic.not (mem x (diff s s')).

Parameter diff_mem_fst :
  forall A379 : Type,
  forall s : set A379,
  forall s' : set A379,
  forall x : A379,
  Coq.Init.Logic.not (mem x s') ->
  Coq.Init.Logic.iff (mem x s) (mem x (diff s s')).

Definition subset  (A : Type) (AIh : Inhab Type) (s : set A) (
  s' : set A
) : Prop:=
forall A : Type,
forall x : A,
mem x s -> mem x s'.

Parameter map :
  forall A : Type,
  forall B : Type,
  forall AIh : Inhab Type,
  forall BIh : Inhab Type,
  (A -> B) -> set A -> set B.

Parameter set_map :
  forall A392 : Type,
  forall f : A392 -> A392,
  forall s : set A392,
  forall x : A392,
  Coq.Init.Logic.iff (mem x (map f s)) (
    forall A392 : Type,
    Coq.Init.Logic.ex (
      fun y : A392 =>
      Coq.Init.Logic.and (Coq.Init.Logic.eq y (f x)) (mem y s)
    )
  ).

Parameter cardinal :
  forall A : Type,
  forall AIh : Inhab Type,
  set A -> Coq.Numbers.BinNums.Z.

Definition finite  (A : Type) (AIh : Inhab Type) (s : set A) : Prop:=
forall A : Type,
Coq.Init.Logic.ex (
  fun seq : sequence A =>
  forall x : A,
  mem x s -> mem x seq
).

Parameter cardinal_nonneg :
  forall A398 : Type,
  forall s : set A398,
  ge (cardinal s) (0)%Z.

Parameter cardinal_empty :
  forall A400 : Type,
  forall s : set A400,
  finite s -> Coq.Init.Logic.eq (cardinal empty) (0)%Z.

Parameter cardinal_remove :
  forall A414 : Type,
  forall s : set A414,
  forall x : A414,
  finite s ->
  (
    if classicT (mem x s) then
      Coq.Init.Logic.eq (cardinal (remove x s)) (minus (cardinal s) (1)%Z)
      else
    Coq.Init.Logic.eq (cardinal (remove x s)) (cardinal s)
  ).

Parameter cardinal_add :
  forall A426 : Type,
  forall s : set A426,
  forall x : A426,
  finite s ->
  (
    if classicT (mem x s) then
      Coq.Init.Logic.eq (cardinal (add x s)) (add (cardinal s) (1)%Z)
      else
    Coq.Init.Logic.eq (cardinal (add x s)) (cardinal s)
  ).

Parameter of_seq :
  forall A : Type,
  forall AIh : Inhab Type,
  sequence A -> set A.

Parameter of_seq_set :
  forall A432 : Type,
  forall x : A432,
  forall s : sequence A432,
  Coq.Init.Logic.iff (mem x s) (mem x (of_seq s)).

Parameter fold :
  forall A : Type,
  forall B : Type,
  forall AIh : Inhab Type,
  forall BIh : Inhab Type,
  (A -> B -> B) -> set A -> B -> B.

End Set.

Module Map.

Parameter t : Type -> Type -> Type.

Parameter T :
  forall A : Type,
  forall B : Type,
  forall AIh : Inhab Type,
  forall BIh : Inhab Type,
  t A B -> t A B -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter domain :
  forall A : Type,
  forall B : Type,
  forall AIh : Inhab Type,
  forall BIh : Inhab Type,
  B -> (A -> B) -> set A.

Parameter domain_mem :
  forall A439 : Type,
  forall A440 : Type,
  forall x : A440,
  forall m : A440 -> A439,
  forall default : A439,
  Coq.Init.Logic.not (Coq.Init.Logic.eq (m x) default) ->
  mem x (domain default m).

End Map.

Module Array.

Parameter get :
  forall A : Type,
  forall AIh : Inhab Type,
  array A -> Coq.Numbers.BinNums.Z -> A.

Parameter length :
  forall A : Type,
  forall AIh : Inhab Type,
  array A -> Coq.Numbers.BinNums.Z.

Parameter to_seq :
  forall A : Type,
  forall AIh : Inhab Type,
  array A -> sequence A.

Parameter permut :
  forall A : Type,
  forall AIh : Inhab Type,
  array A -> array A -> Prop.

Parameter permut_sub :
  forall A : Type,
  forall AIh : Inhab Type,
  array A ->
  array A -> Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z -> Prop.

End Array.

Module List.

Parameter fold_left :
  forall A : Type,
  forall B : Type,
  forall AIh : Inhab Type,
  forall BIh : Inhab Type,
  (B -> A -> B) -> B -> list A -> B.

Parameter _exists :
  forall A : Type,
  forall AIh : Inhab Type,
  (A -> Prop) -> list A -> Prop.

Parameter length :
  forall A : Type,
  forall AIh : Inhab Type,
  list A -> Coq.Numbers.BinNums.Z.

Parameter nth :
  forall A : Type,
  forall AIh : Inhab Type,
  list A -> Coq.Numbers.BinNums.Z -> A.

Parameter mem :
  forall A : Type,
  forall AIh : Inhab Type,
  A -> list A -> Prop.

Parameter map :
  forall A : Type,
  forall B : Type,
  forall AIh : Inhab Type,
  forall BIh : Inhab Type,
  (A -> B) -> list A -> list B.

End List.

Module Order.

Parameter is_pre_order :
  forall A : Type,
  forall AIh : Inhab Type,
  (A -> A -> int) -> Prop.

End Order.

Parameter ref : Type -> Type.

Parameter Ref :
  forall A : Type,
  forall AIh : Inhab Type,
  ref A -> ref A -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter prefix ! :
  forall A : Type,
  forall AIh : Inhab Type,
  ref A -> A.

Parameter logand :
  Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z.

Parameter integer_of_int : int -> Coq.Numbers.BinNums.Z.


