Set Implicit Arguments.

Require Coq.ZArith.BinInt TLC.LibLogic TLC.LibRelation TLC.LibInt TLC.LibListZ.

Require Import CFML.SepBase CFML.SepLifted CFML.WPLib CFML.WPLifted CFML.WPRecord CFML.WPArray CFML.WPBuiltin.

Require CFML.Stdlib.Array_ml CFML.Stdlib.List_ml CFML.Stdlib.Sys_ml.

Require Import Coq.ZArith.BinIntDef CFML.Semantics CFML.WPHeader.

Delimit Scope Z_scope with Z.

Module Type Stdlib.

Parameter sequence : Type -> Type.

Parameter bag : Type -> Type.

Parameter set : Type -> Type.

Parameter option : Type -> Type.

Parameter Some :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  A -> option A.

Parameter None : forall {A : Type}, forall {Ih_A : Inhab A}, option A.

Definition map  (A : Type) (B : Type) : Type:= A -> B.

Parameter succ : Z -> Z.

Parameter pred : Z -> Z.

Parameter neg : Z -> Z.

Parameter _mod : Z -> Z -> Z.

Parameter pow : Z -> Z -> Z.

Parameter abs : Z -> Z.

Parameter min : Z -> Z -> Z.

Parameter max : Z -> Z -> Z.

Parameter app :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  sequence A -> sequence A -> sequence A.

Parameter seq_get :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  sequence A -> Z -> A.

Parameter seq_sub :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  sequence A -> Z -> Z -> sequence A.

Parameter seq_sub_l :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  sequence A -> Z -> sequence A.

Parameter seq_sub_r :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  sequence A -> Z -> sequence A.

Parameter monoid :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  (A -> A -> A) -> A -> Prop.

Axiom monoid_def :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall f : A -> A -> A,
  forall neutral : A,
  (
    monoid f neutral <-> (
      forall x : A,
      ((f neutral x = f x neutral) /\ (f x neutral = x)) /\ forall x : A,
      forall y : A,
      forall z : A,
      (f x (f y z) = f (f x y) z)
    )
  ).

Parameter comm_monoid :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  (A -> A -> A) -> A -> Prop.

Axiom comm_monoid_def :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall f : A -> A -> A,
  forall neutral : A,
  (
    comm_monoid f neutral <-> (
      monoid f neutral /\ forall x : A,
      forall y : A,
      (f x y = f y x)
    )
  ).

Module Sequence.

Definition t  (A : Type) : Type:= sequence A.

Parameter length : forall {A : Type}, forall {Ih_A : Inhab A}, t A -> Z.

Parameter in_range :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  t A -> Z -> Prop.

Axiom in_range_def :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s : sequence A,
  forall i : Z,
  (in_range s i <-> (((0)%Z <= i) /\ (i < length s))).

Axiom length_nonneg :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s : sequence A,
  ((0)%Z <= length s).

Axiom subseq_l :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s : sequence A,
  forall i : Z,
  in_range s i -> (seq_sub_l s i = seq_sub s i (length s)).

Axiom subseq_r :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s : sequence A,
  forall i : Z,
  in_range s i -> (seq_sub_r s i = seq_sub s (0)%Z i).

Axiom subseq :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s : sequence A,
  forall i : Z,
  forall i1 : Z,
  forall i2 : Z,
  (((0)%Z <= i1) /\ ((i1 <= i) /\ ((i < i2) /\ (i2 <= length s)))) ->
  (seq_get s i = seq_get (seq_sub s i1 i2) ((i - i1))).

Axiom subseq_len :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s : sequence A,
  forall i1 : Z,
  forall i2 : Z,
  (((0)%Z <= i1) /\ ((i1 <= i2) /\ (i2 < length s))) ->
  (length (seq_sub s i1 i2) = (i2 - i1)).

Parameter empty : forall {A : Type}, forall {Ih_A : Inhab A}, t A.

Axiom empty_length :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  (@length A Ih_A empty = (0)%Z).

Parameter init :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  Z -> (Z -> A) -> t A.

Axiom init_length :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall n : Z,
  forall f : Z -> A,
  (n >= (0)%Z) -> (length (init n f) = n).

Axiom init_elems :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall n : Z,
  forall f : Z -> A,
  forall i : Z,
  (((0)%Z <= i) /\ (i < n)) -> (seq_get (init n f) i = f i).

Parameter singleton :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  A -> t A.

Axiom singleton_def :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall x : A,
  forall f : Z -> A,
  (f (0)%Z = x) -> (singleton x = init (1)%Z f).

Parameter cons :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  A -> t A -> t A.

Axiom cons_def :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall x : A,
  forall s : sequence A,
  (cons x s = app (singleton x) s).

Parameter snoc :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  t A -> A -> t A.

Axiom snoc_def :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s : sequence A,
  forall x : A,
  (snoc s x = app s (singleton x)).

Parameter hd : forall {A : Type}, forall {Ih_A : Inhab A}, t A -> A.

Axiom hd_def :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s : sequence A,
  (hd s = seq_get s (0)%Z).

Parameter tl : forall {A : Type}, forall {Ih_A : Inhab A}, t A -> t A.

Axiom tl_def :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s : sequence A,
  (tl s = seq_sub_l s (1)%Z).

Parameter append :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  t A -> t A -> t A.

Axiom append_def :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s1 : sequence A,
  forall s2 : sequence A,
  (append s1 s2 = app s1 s2).

Axiom append_length :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s : sequence A,
  forall s' : sequence A,
  (length (app s s') = (length s + length s')).

Axiom append_elems_left :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s : sequence A,
  forall s' : sequence A,
  forall i : Z,
  in_range s i -> (seq_get (app s s') i = seq_get s i).

Axiom append_elems_right :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s : sequence A,
  forall s' : sequence A,
  forall i : Z,
  ((length s <= i) /\ (i < (length s + length s'))) ->
  (seq_get (app s s') i = seq_get s' ((i - length s))).

Parameter multiplicity :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  A -> t A -> Z.

Axiom mult_empty :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall x : A,
  (multiplicity x empty = (0)%Z).

Axiom mult_cons :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s : sequence A,
  forall x : A,
  (((1)%Z + multiplicity x s) = multiplicity x (cons x s)).

Axiom mult_cons_neutral :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s : sequence A,
  forall x1 : A,
  forall x2 : A,
  (x1 <> x2) -> (multiplicity x1 s = multiplicity x1 (cons x2 s)).

Axiom mult_length :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall x : A,
  forall s : sequence A,
  (((0)%Z <= multiplicity x s) /\ (multiplicity x s <= length s)).

Parameter mem :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  A -> t A -> Prop.

Axiom mem_def :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s : sequence A,
  forall x : A,
  (mem x s <-> (multiplicity x s > (0)%Z)).

Parameter _forall :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  (A -> Prop) -> sequence A -> Prop.

Axiom forall_def :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall p : A -> Prop,
  forall s : sequence A,
  (_forall p s <-> forall x : A, mem x s -> p x).

Parameter _exists :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  (A -> Prop) -> sequence A -> Prop.

Axiom _exists_def :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall p : A -> Prop,
  forall s : sequence A,
  (_exists p s <-> Coq.Init.Logic.ex (fun x : A => (mem x s /\ p x))).

Parameter map :
  forall {A : Type},
  forall {B : Type},
  forall {Ih_A : Inhab A},
  forall {Ih_B : Inhab B},
  (A -> B) -> t A -> t B.

Axiom map_elems :
  forall {B : Type},
  forall {A : Type},
  forall {Ih_B : Inhab B},
  forall {Ih_A : Inhab A},
  forall i : Z,
  forall f : B -> A,
  forall s : sequence B,
  in_range s i -> (seq_get (map f s) i = f (seq_get s i)).

Parameter filter :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  (A -> Prop) -> t A -> t A.

Axiom filter_elems :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall f : A -> Prop,
  forall s : sequence A,
  forall x : A,
  mem x s -> f x -> mem x (filter f s).

Parameter filter_map :
  forall {A : Type},
  forall {B : Type},
  forall {Ih_A : Inhab A},
  forall {Ih_B : Inhab B},
  (A -> option B) -> t A -> t B.

Axiom filter_map_elems :
  forall {B : Type},
  forall {A : Type},
  forall {Ih_B : Inhab B},
  forall {Ih_A : Inhab A},
  forall f : B -> option A,
  forall s : sequence B,
  forall y : A,
  (
    Coq.Init.Logic.ex (fun x : B => ((f x = Some y) /\ mem x s)) <-> mem y (
      filter_map f s
    )
  ).

Parameter get :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  t A -> Z -> A.

Axiom get_def :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s : sequence A,
  forall i : Z,
  (get s i = seq_get s i).

Parameter set :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  t A -> Z -> A -> t A.

Axiom set_elem :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s : sequence A,
  forall i : Z,
  forall x : A,
  in_range s i -> (seq_get (set s i x) i = x).

Axiom set_elem_other :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s : sequence A,
  forall i1 : Z,
  forall i2 : Z,
  forall x : A,
  (i1 <> i2) ->
  in_range s i1 ->
  in_range s i2 -> (seq_get (set s i1 x) i2 = seq_get s i2).

Parameter rev : forall {A : Type}, forall {Ih_A : Inhab A}, t A -> t A.

Axiom rev_length :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s : sequence A,
  (length s = length (rev s)).

Axiom rev_elems :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall i : Z,
  forall s : sequence A,
  in_range s i ->
  (seq_get (rev s) i = seq_get s (((length s - (1)%Z) - i))).

Axiom extensionality :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s1 : sequence A,
  forall s2 : sequence A,
  (length s1 = length s2) ->
  (forall i : Z, in_range s1 i -> (seq_get s1 i = seq_get s2 i)) ->
  (s1 = s2).

Parameter fold_left :
  forall {A : Type},
  forall {B : Type},
  forall {Ih_A : Inhab A},
  forall {Ih_B : Inhab B},
  (A -> B -> A) -> A -> t B -> A.

Axiom fold_left_empty :
  forall {B : Type},
  forall {A : Type},
  forall {Ih_B : Inhab B},
  forall {Ih_A : Inhab A},
  forall f : A -> B -> A,
  forall acc : A,
  (fold_left f acc empty = acc).

Axiom fold_left_cons :
  forall {B : Type},
  forall {A : Type},
  forall {Ih_B : Inhab B},
  forall {Ih_A : Inhab A},
  forall f : A -> B -> A,
  forall acc : A,
  forall x : B,
  forall l : sequence B,
  (fold_left f acc (cons x l) = fold_left f (f acc x) l).

Parameter fold_right :
  forall {A : Type},
  forall {B : Type},
  forall {Ih_A : Inhab A},
  forall {Ih_B : Inhab B},
  (A -> B -> B) -> t A -> B -> B.

Axiom fold_right_empty :
  forall {B : Type},
  forall {A : Type},
  forall {Ih_B : Inhab B},
  forall {Ih_A : Inhab A},
  forall acc : A,
  forall f : B -> A -> A,
  (fold_right f empty acc = acc).

Axiom fold_right_cons :
  forall {B : Type},
  forall {A : Type},
  forall {Ih_B : Inhab B},
  forall {Ih_A : Inhab A},
  forall acc : A,
  forall f : B -> A -> A,
  forall x : B,
  forall l : sequence B,
  (fold_right f (cons x l) acc = f x (fold_right f l acc)).

Parameter permut :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  t A -> t A -> Prop.

Axiom permut_mem :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s1 : sequence A,
  forall s2 : sequence A,
  permut s1 s2 -> (forall x : A, (mem x s1 <-> mem x s2)).

Parameter permut_sub :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  t A -> t A -> Z -> Z -> Prop.

Axiom permut_sub_def :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s1 : sequence A,
  forall s2 : sequence A,
  forall i : Z,
  forall j : Z,
  permut (seq_sub s1 i j) (seq_sub s2 i j) ->
  (seq_sub_r s1 i = seq_sub_r s2 i) ->
  (seq_sub_l s1 j = seq_sub_l s2 j) -> permut_sub s1 s2 i j.

End Sequence.

Module Bag.

Definition t  (A : Type) : Type:= bag A.

Parameter multiplicity :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  A -> t A -> Z.

Axiom well_formed :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall b : bag A,
  forall x : A,
  (multiplicity x b >= (0)%Z).

Parameter empty : forall {A : Type}, forall {Ih_A : Inhab A}, t A.

Axiom empty_mult :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall x : A,
  (multiplicity x empty = (0)%Z).

Parameter init :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  (A -> Z) -> t A.

Axiom init_axiom :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall f : A -> Z,
  forall x : A,
  (max (0)%Z (f x) = multiplicity x (init f)).

Parameter mem :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  A -> t A -> Prop.

Axiom mem_def :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall x : A,
  forall b : bag A,
  (mem x b <-> (multiplicity x b > (0)%Z)).

Parameter add :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  A -> t A -> t A.

Axiom add_mult_x :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall b : bag A,
  forall x : A,
  (multiplicity x (add x b) = ((1)%Z + multiplicity x b)).

Axiom add_mult_neg_x :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall x : A,
  forall y : A,
  forall b : bag A,
  (x <> y) -> (multiplicity y (add x b) = multiplicity y b).

Parameter singleton :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  A -> t A.

Axiom singleton_def :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall x : A,
  (singleton x = add x empty).

Parameter remove :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  A -> t A -> t A.

Axiom remove_mult_x :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall b : bag A,
  forall x : A,
  (multiplicity x (remove x b) = max (0)%Z ((multiplicity x b - (1)%Z))).

Axiom remove_mult_neg_x :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall x : A,
  forall y : A,
  forall b : bag A,
  (x <> y) -> (multiplicity y (remove x b) = multiplicity y b).

Parameter union :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  t A -> t A -> t A.

Axiom union_all :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall b : bag A,
  forall b' : bag A,
  forall x : A,
  (
    max (multiplicity x b) (multiplicity x b') = multiplicity x (union b b')
  ).

Parameter sum :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  t A -> t A -> t A.

Axiom sum_all :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall b : bag A,
  forall b' : bag A,
  forall x : A,
  ((multiplicity x b + multiplicity x b') = multiplicity x (sum b b')).

Parameter inter :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  t A -> t A -> t A.

Axiom inter_all :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall b : bag A,
  forall b' : bag A,
  forall x : A,
  (
    min (multiplicity x b) (multiplicity x b') = multiplicity x (inter b b')
  ).

Parameter disjoint :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  t A -> t A -> Prop.

Axiom disjoint_def :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall b : bag A,
  forall b' : bag A,
  (disjoint b b' <-> forall x : A, mem x b -> not (mem x b')).

Parameter diff :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  t A -> t A -> t A.

Axiom diff_all :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall b : bag A,
  forall b' : bag A,
  forall x : A,
  (
    max (0)%Z ((multiplicity x b - multiplicity x b')) = multiplicity x (
      diff b b'
    )
  ).

Parameter subset :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  t A -> t A -> Prop.

Axiom subset_def :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall b : bag A,
  forall b' : bag A,
  (subset b b' <-> forall x : A, (multiplicity x b <= multiplicity x b')).

Parameter filter :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  (A -> Prop) -> t A -> t A.

Axiom filter_mem :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall b : bag A,
  forall x : A,
  forall f : A -> Prop,
  f x -> (multiplicity x (filter f b) = multiplicity x b).

Axiom filter_mem_neg :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall b : bag A,
  forall x : A,
  forall f : A -> Prop,
  not (f x) -> (multiplicity x (filter f b) = (0)%Z).

Parameter cardinal :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  t A -> Z.

Parameter finite :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  t A -> Prop.

Axiom finite_def :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall b : bag A,
  (
    finite b <-> Coq.Init.Logic.ex (
      fun s : sequence A =>
      forall x : A,
      mem x b -> Sequence.mem x s
    )
  ).

Axiom card_nonneg :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall b : bag A,
  (cardinal b >= (0)%Z).

Axiom card_empty :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  (@cardinal A Ih_A empty = (0)%Z).

Axiom card_singleton :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall x : A,
  (cardinal (singleton x) = (1)%Z).

Axiom card_union :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall b1 : bag A,
  forall b2 : bag A,
  finite b1 ->
  finite b2 -> (cardinal (union b1 b2) = (cardinal b1 + cardinal b2)).

Axiom card_add :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall x : A,
  forall b : bag A,
  finite b -> (cardinal (add x b) = (cardinal b + (1)%Z)).

Axiom card_map :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall f : A -> Prop,
  forall b : bag A,
  finite b -> (cardinal (filter f b) <= cardinal b).

Parameter of_seq :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  Sequence.t A -> t A.

Axiom of_seq_multiplicity :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s : sequence A,
  forall x : A,
  (Sequence.multiplicity x s = multiplicity x (of_seq s)).

End Bag.

Module _Set.

Definition t  (A : Type) : Type:= set A.

Parameter empty : forall {A : Type}, forall {Ih_A : Inhab A}, t A.

Parameter mem :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  A -> t A -> Prop.

Axiom empty_mem :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall x : A,
  not (mem x empty).

Parameter add :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  A -> t A -> t A.

Axiom add_mem :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s : set A,
  forall x : A,
  mem x (add x s).

Axiom add_mem_neq :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s : set A,
  forall x : A,
  forall y : A,
  (x <> y) -> (mem x s <-> mem x (add y s)).

Parameter singleton :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  A -> t A.

Parameter remove :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  A -> t A -> t A.

Axiom remove_mem :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s : set A,
  forall x : A,
  not (mem x (remove x s)).

Axiom remove_mem_neq :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s : set A,
  forall x : A,
  forall y : A,
  (x <> y) -> (mem x s <-> mem x (remove y s)).

Parameter union :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  t A -> t A -> t A.

Axiom union_mem :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s : set A,
  forall s' : set A,
  forall x : A,
  (mem x s \/ mem x s') -> mem x (union s s').

Axiom union_mem_neg :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s : set A,
  forall s' : set A,
  forall x : A,
  not (mem x s) -> not (mem x s') -> not (mem x (union s s')).

Parameter inter :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  t A -> t A -> t A.

Axiom inter_mem :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s : set A,
  forall s' : set A,
  forall x : A,
  mem x s -> mem x s' -> mem x (inter s s').

Axiom inter_mem_neq :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s : set A,
  forall s' : set A,
  forall x : A,
  not ((mem x s \/ mem x s')) -> not (mem x (inter s s')).

Parameter disjoint :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  t A -> t A -> Prop.

Axiom disjoint_def :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s : set A,
  forall s' : set A,
  (disjoint s s' <-> (inter s s' = empty)).

Parameter diff :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  t A -> t A -> t A.

Axiom diff_mem :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s : set A,
  forall s' : set A,
  forall x : A,
  mem x s' -> not (mem x (diff s s')).

Axiom diff_mem_fst :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s : set A,
  forall s' : set A,
  forall x : A,
  not (mem x s') -> (mem x s <-> mem x (diff s s')).

Parameter subset :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  t A -> t A -> Prop.

Axiom subset_def :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s : set A,
  forall s' : set A,
  (subset s s' <-> forall x : A, mem x s -> mem x s').

Parameter map :
  forall {A : Type},
  forall {B : Type},
  forall {Ih_A : Inhab A},
  forall {Ih_B : Inhab B},
  (A -> B) -> t A -> t B.

Axiom set_map :
  forall {A : Type},
  forall {B : Type},
  forall {Ih_A : Inhab A},
  forall {Ih_B : Inhab B},
  forall f : B -> A,
  forall s : set B,
  forall x : A,
  (
    mem x (map f s) <-> Coq.Init.Logic.ex (
      fun y : B =>
      ((f y = x) /\ mem y s)
    )
  ).

Parameter partition :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  (A -> Prop) -> t A -> Coq.Init.Datatypes.prod (t A) (t A).

Axiom partition_l_mem :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall f : A -> Prop,
  forall s : set A,
  forall x : A,
  forall p1 : set A,
  forall p2 : set A,
  mem x s -> f x -> (partition f s = (p1, p2)) -> mem x p1.

Axiom partition_r_mem :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall f : A -> Prop,
  forall s : set A,
  forall x : A,
  forall p1 : set A,
  forall p2 : set A,
  mem x s -> not (f x) -> (partition f s = (p1, p2)) -> mem x p2.

Parameter cardinal :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  t A -> Z.

Parameter finite :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  t A -> Prop.

Axiom finite_def :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s : set A,
  (
    finite s <-> Coq.Init.Logic.ex (
      fun seq : sequence A =>
      forall x : A,
      mem x s -> Sequence.mem x seq
    )
  ).

Axiom cardinal_nonneg :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s : set A,
  (cardinal s >= (0)%Z).

Axiom cardinal_empty :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  (@cardinal A Ih_A empty = (0)%Z).

Axiom cardinal_remove :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s : set A,
  forall x : A,
  finite s ->
  (
    if classicT (mem x s) then
      (cardinal (remove x s) = (cardinal s - (1)%Z))
      else
    (cardinal (remove x s) = cardinal s)
  ).

Axiom cardinal_add :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s : set A,
  forall x : A,
  finite s ->
  (
    if classicT (mem x s) then
      (cardinal (add x s) = cardinal s)
      else
    (cardinal (add x s) = (cardinal s + (1)%Z))
  ).

Parameter of_seq :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  Sequence.t A -> t A.

Axiom of_seq_mem :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s : sequence A,
  forall x : A,
  (mem x (of_seq s) <-> Sequence.mem x s).

Parameter to_seq :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  t A -> Sequence.t A.

Axiom to_seq_mem :
  forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s : set A,
  finite s ->
  (
    forall x : A,
    (mem x s <-> (Sequence.multiplicity x (to_seq s) = (1)%Z))
  ).

Parameter fold :
  forall {A : Type},
  forall {B : Type},
  forall {Ih_A : Inhab A},
  forall {Ih_B : Inhab B},
  (A -> B) -> (B -> B -> B) -> t A -> B -> B.

Axiom fold_def :
  forall {A : Type},
  forall {B : Type},
  forall {Ih_A : Inhab A},
  forall {Ih_B : Inhab B},
  forall f : A -> B,
  forall m : B -> B -> B,
  forall s : set A,
  forall acc : B,
  finite s ->
  comm_monoid m acc ->
  (
    fold f m s acc = Sequence.fold_right (
      fun x : A =>
      fun acc : B =>
      m (f x) acc
    ) (to_seq s) acc
  ).

End _Set.

Parameter map_set :
  forall {A : Type},
  forall {B : Type},
  forall {Ih_A : Inhab A},
  forall {Ih_B : Inhab B},
  (A -> B) -> A -> B -> A -> B.

Axiom map_set_def :
  forall {A : Type},
  forall {B : Type},
  forall {Ih_A : Inhab A},
  forall {Ih_B : Inhab B},
  forall f : A -> B,
  forall x : A,
  forall y : B,
  (map_set f x y = fun arg : A => if classicT ((arg = x)) then y else f x).

Module Map.

Definition t  (A : Type) (B : Type) : Type:= map A B.

Parameter domain :
  forall {A : Type},
  forall {B : Type},
  forall {Ih_A : Inhab A},
  forall {Ih_B : Inhab B},
  B -> t A B -> _Set.t A.

Axiom domain_mem :
  forall {B : Type},
  forall {A : Type},
  forall {Ih_B : Inhab B},
  forall {Ih_A : Inhab A},
  forall x : A,
  forall m : A -> B,
  forall default : B,
  (m x <> default) -> _Set.mem x (domain default m).

End Map.

End Stdlib.
