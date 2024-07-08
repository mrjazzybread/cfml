Set Implicit Arguments.

Require Import Gospel.

Require Import CFML.SepBase CFML.SepLifted CFML.WPLib CFML.WPLifted CFML.WPRecord CFML.WPArray CFML.WPBuiltin.

Require CFML.Stdlib.Array_ml CFML.Stdlib.List_ml CFML.Stdlib.Sys_ml.

Require Import Coq.ZArith.BinIntDef CFML.Semantics CFML.WPHeader.

Require Import TLC.LibLogic TLC.LibRelation TLC.LibInt Coq.ZArith.BinInt.

Require TLC.LibMultiset.

Delimit Scope Z_scope with Z.

Require gospelstdlib_mli.

Module Stdlib_proof : gospelstdlib_mli.Stdlib.

  Definition sequence A := list A.

  Parameter Sequence :
  forall a : Type,
  forall {aIh : Inhab a},
  sequence a ->
  sequence a -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

  Definition bag A := LibMultiset.multiset A.

  
Parameter Bag :
  forall a : Type,
  forall {aIh : Inhab a},
  bag a -> bag a -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.
  
Definition set A := A -> Prop.

Parameter _Set :
  forall a : Type,
  forall {aIh : Inhab a},
  set a -> set a -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Definition map A B := A -> B.
Parameter Map :
  forall a : Type,
  forall b : Type,
  forall {aIh : Inhab a},
  forall {bIh : Inhab b},
  map a b ->
  map a b -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

  Definition succ := Z.succ.

  Definition pred := Z.pred.
  Definition neg := Z.opp.
  Definition plus := Z.add.
  Definition minus := Z.sub.
  Definition mult := Z.mul.
  Definition div  := Z.div.
  Definition _mod := Z.modulo.
  Definition pow := Z.pow.
  Definition abs := Z.abs.
  Definition min := Z.min.
  Definition max := Z.max.
  Definition gt := Z.gt.
  Definition ge := Z.ge.
  Definition lt := Z.lt.
  Definition le := Z.le.
  Parameter max_int : Z.
  Parameter min_int : Z.
  Definition app A {Ih:Inhab A} := @app A.

  Definition seq_get
    {A} {Ih:Inhab A} (s : sequence A) (n : int) : A :=
    If n < 0
    then arbitrary
    else nth (Z.to_nat n) s.

  Lemma seq_get_pos :
    forall A (Ih : Inhab A) (s : sequence A) i,
      i >= 0 -> seq_get s i = nth (Z.to_nat i) s.
  Proof.
    intros A Ihn s i H1.
    unfold seq_get.
    rewrite If_r. auto. math.
  Qed.
  

Definition map_set  (A : Type) (B : Type) {Ih : Inhab A} {Ih : Inhab B} (f : A -> B) (x : A) (y : B) : A ->
B:=
fun arg : A =>
if classicT (Coq.Init.Logic.eq arg x) then y else f x.

Module Sequence.

Parameter t : Type -> Type.

Parameter T :
  forall a : Type,
  forall {aIh : Inhab a},
  t a -> t a -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

  
Definition in_range  (A : Type) {Ih : Inhab A} (s : sequence A) (
  i : Coq.Numbers.BinNums.Z
) : Prop:=
Coq.Init.Logic.and (le (0)%Z i) (lt i (length s)).

  Definition length {A} {Ih : Inhab A} (s : sequence A) : Z :=
    length s.

  Fixpoint seq_sub_aux {A} (s : sequence A) (i1 : nat) (i2 : nat) : sequence A :=
    match s with
    |nil => nil
    |cons x t =>
       match i1 with
       |S i1' => seq_sub_aux t i1' i2
       |O => match i2 with
             |S i2' => cons x (seq_sub_aux t O i2')
             |O => nil
             end
       end
    end.
  
  Definition seq_sub {A} {Ih : Inhab A} (s : sequence A) (i1 : Z) (i2 : Z) : sequence A :=
    if (i1 <? 0) || (i1 >? i2) || (i2 >? length s)
    then arbitrary
    else
      let i1 := Z.to_nat i1 in
      let i2 := Z.to_nat i2 in
      seq_sub_aux s i1 i2.

  
Definition seq_sub_l  (A : Type) {Ih : Inhab A} (s : sequence A) (
  i : Coq.Numbers.BinNums.Z
) : sequence A:=
seq_sub s i (length s).

Definition seq_sub_r  (A : Type) {Ih : Inhab A} (s : sequence A) (
  i : Coq.Numbers.BinNums.Z
) : sequence A:=
seq_sub s (0)%Z i.


Lemma length_nonneg :
  forall A11 : Type,
  forall {Ih : Inhab A11},
  forall s : sequence A11,
    le (0)%Z (length s).
Proof.
  intros.
  unfold le.
  unfold length.
  math.
Qed.
Lemma append_length :
  forall A17 : Type,
  forall {Ih : Inhab A17},
  forall s : sequence A17,
  forall s' : sequence A17,
  Coq.Init.Logic.eq (length (app s s')) (plus (length s) (length s')).
Proof.
  intros.
  unfold plus.
  unfold length.
  unfold app.
  rew_list.
  math.
Qed.
  
Parameter append_elems_left :
  forall A26 : Type,
  forall {Ih : Inhab A26},
  forall s : sequence A26,
  forall s' : sequence A26,
  forall i : Coq.Numbers.BinNums.Z,
  Coq.Init.Logic.and (le 0 i %Z) (lt (i)%Z (length s)) ->
  Coq.Init.Logic.eq (seq_get (app s s') i) (seq_get s i).


Parameter append_elems_right :
  forall a36 : Type,
  forall {a36Ih : Inhab a36},
  forall s : sequence a36,
  forall s' : sequence a36,
  forall i : Coq.Numbers.BinNums.Z,
  Coq.Init.Logic.and (le (length s) i) (
    lt i (plus (length s) (length s'))
  ) ->
  Coq.Init.Logic.eq (seq_get (app s s') i) (
    seq_get s' (minus i (length s))
  ).

Parameter subseq :
  forall A45 : Type,
  forall {Ih : Inhab A45},
  forall s : sequence A45,
  forall i : Coq.Numbers.BinNums.Z,
  forall i1 : Coq.Numbers.BinNums.Z,
  forall i2 : Coq.Numbers.BinNums.Z,
  Coq.Init.Logic.and (le i1 i) (lt i i2) ->
  Coq.Init.Logic.eq (seq_get s i) (seq_get (seq_sub s i1 i2) (minus i i1)).


Fixpoint init_aux {A} (n : nat) (f : Z -> A) : sequence A :=
  match n with
  |O => nil
  |S n' =>  LibList.app (init_aux n' f) ((cons (f n') nil)) end.

Definition init {A} {Ih : Inhab A} (n : Z) (f : Z -> A) : sequence A :=
  If n < 0 then arbitrary else
    init_aux (Z.to_nat n) f.

Lemma init_pos :
  forall A {Ih : Inhab A} n (f : Z -> A),
    n >= 0 -> init n f = init_aux (Z.to_nat n) f.
Proof.
  intros A Ih n f H.
  unfold init. rewrite If_r. auto. math.
Qed.

Lemma init_aux_length :
  forall A n (f : Z -> A),
    LibList.length (init_aux n f) = n.
Proof.
  intros A n f.
  induction n as [|n' Ih].
  + simpl. rew_list. math.
  + simpl. rew_list.
    rewrite Ih. math.
Qed.
    
Lemma init_length :
  forall A49 : Type,
  forall {Ih : Inhab A49},
  forall n : Coq.Numbers.BinNums.Z,
  forall f : Coq.Numbers.BinNums.Z -> A49,
    ge n 0 -> Coq.Init.Logic.eq (length (init n f)) n.
Proof.
  intros A Ih n f H.
  unfold init. unfold ge in *.
  rewrite If_r.
  - unfold length. rewrite init_aux_length. math.
  - math.
Qed.

Lemma init_i :
  forall A (n : nat) (i : Z) (f : Z -> A),
    forall {Ih : Inhab A},
    0 <= i ->
    i < n ->
    nth (Z.to_nat i) (init_aux n f) = f i.
Proof.
  intros A n i f Inh H1 H2.
  induction n as [|n' Ih].
  - math.
  - simpl. rewrite nth_app.
    rewrite init_aux_length.
    assert (P : i < n' \/ ~ i < n').
    apply classic.
    destruct P as [P|P].
    + rewrite If_l. auto. math.
    + assert (N : Z.to_nat i = n'). { math. } assert (Q : i = n'). { math. } rewrite If_r.
      * rewrite N. rewrite Nat.sub_diag.
        rewrite Q. apply nth_zero.
      * math.
Qed.

Lemma init_elems :
  forall A57 : Type,
  forall {Ih : Inhab A57},
  forall n : Coq.Numbers.BinNums.Z,
  forall f : Coq.Numbers.BinNums.Z -> A57,
  forall i : Coq.Numbers.BinNums.Z,
  Coq.Init.Logic.and (le (0)%Z i) (lt i n) ->
  Coq.Init.Logic.eq (seq_get (init n f) i) (f i).
Proof.
  intros A Inh n f i [H1 H2].
  unfold seq_get.
  unfold init.
  unfold le in *.
  unfold lt in *.
  rewrite If_r; try math.
  rewrite If_r; try math.
  apply init_i; math.
Qed.

Definition empty {A} {Ih : Inhab A} := @nil A.
Lemma empty_length :
  forall A {Ih : Inhab A}, Coq.Init.Logic.eq (length (@empty A Ih)) (0)%Z.
Proof.
  intro A.
  unfold length. rew_list. auto.
Qed.

Definition singleton (A : Type) {Ih : Inhab A} (x : A) : sequence A:=
init (1)%Z (fun _ : Coq.Numbers.BinNums.Z => x).

Definition cons (A : Type) {Ih : Inhab A} (x : A) (s : sequence A) : sequence A:=
app (singleton x) s.

Lemma cons_std :
  forall A {Ih : Inhab A} (x : A) s,
    cons x s = List.cons x s.
Proof.
  intros.
  unfold cons.
  unfold singleton.
  unfold init.
  rewrite If_r; try math.
  simpl. rew_list. auto.
Qed.

Definition snoc (A : Type) {Ih : Inhab A}(s : sequence A) (x : A) : sequence A:=
app s (singleton x).

Definition hd (A : Type) {Ih : Inhab A} (s : sequence A) : A:= seq_get s (0)%Z.

Definition tl (A : Type){Ih : Inhab A} (s : sequence A) : sequence A:=
seq_sub_l s (1)%Z.

Definition append  (A : Type){Ih : Inhab A} (s1 : sequence A) (s2 : sequence A) : sequence A:=
app s1 s2.

Definition multiplicity {A}{Ih : Inhab A} (e : A) (s : sequence A) : Z :=
  count (fun x => x = e) s.

Lemma mult_empty :
  forall A73 : Type,
  forall {Ih : Inhab A73},
  forall x : A73,
  Coq.Init.Logic.eq (multiplicity x (@empty A73 Ih)) (0)%Z.
Proof.
  intros A Ih x.
  unfold multiplicity.
  rewrite count_nil. math.
Qed.

Lemma mult_cons :
  forall A79 : Type,
  forall {Ih : Inhab A79},
  forall s : sequence A79,
  forall x : A79,
  Coq.Init.Logic.eq (plus (1)%Z (multiplicity x s)) (
    multiplicity x (cons x s)
  ).
Proof.
  intros A Ih s x.
  unfold multiplicity.
  unfold plus.
  rewrite cons_std.
  rewrite count_cons.
  rewrite If_l; auto.
  math.
Qed.

Lemma mult_cons_neutral :
  forall A {Ih : Inhab A} s (x1 : A) x2,
    Coq.Init.Logic.not (Coq.Init.Logic.eq x1 x2) ->
    Coq.Init.Logic.eq (multiplicity x1 s) (multiplicity x1 (cons x2 s)).
Proof.
  intros A Ih s x1 x2 H1.
  unfold multiplicity.
  rewrite cons_std.
  rewrite count_cons.
  rewrite If_r; auto.
Qed.

Lemma mult_length :
  forall A92 : Type,
  forall {Ih: Inhab A92},
  forall x : A92,
  forall s : sequence A92,
  Coq.Init.Logic.and (le (0)%Z (multiplicity x s)) (
    le (multiplicity x s) (length s)
  ).
Proof.
  intros A I x s.
  unfold le.
  unfold multiplicity.
  unfold length.
  split.
  - math.
  - induction s as [|e s' Ih].
    + rew_list. rewrite count_nil. math.
    + rewrite count_cons. rew_list. simpl.
      assert (E : e = x \/ e <> x). apply classic.
      destruct E.
      * rewrite If_l; auto. math.
      * rewrite If_r; auto. math.
Qed.

Definition mem  (A : Type) {Ih : Inhab A} (x : A) (s : sequence A) : Prop:=
gt (multiplicity x s) (0)%Z.

Lemma tlc_mem :
  forall A {Ih : Inhab A} (x : A) s, mem x s <-> LibList.mem x s.
Proof.
  intros A Ih x s. split; intro H;
  unfold mem, gt, multiplicity in *.
  induction s as [|h s I].
  - inversion H.
  - assert (P: x = h \/ x <> h). { apply classic. }
    destruct P as [P | P]. rewrite mem_cons_eq.
    + left. auto.
    + right. rewrite count_cons in H. rewrite If_r in H.
      rewrite Nat.add_0_r in H; auto. auto.
  - induction s as [|h s I].
    + inversion H.
    + rewrite count_cons.
      assert (P: x = h \/ x <> h). { apply classic. }
      destruct P. subst. rewrite If_l; auto. math.
      rewrite If_r; auto. rewrite Nat.add_0_r.
      rewrite mem_cons_eq in H. destruct H.
      contradiction. auto.  
Qed.

Definition map {A} {B} {Ih:Inhab A} {Ih:Inhab B} := @LibList.map A B.

Lemma map_elems :
  forall A100 : Type,
  forall A102 : Type,
  forall {Ih : Inhab A100},
  forall {Ih : Inhab A102},
  forall i : Coq.Numbers.BinNums.Z,
  forall f : A100 -> A102,
  forall s : sequence A100,
  le 0 i /\ lt i (length s) -> Coq.Init.Logic.eq (seq_get (map f s) i) (f (seq_get s i)).
Proof.
  intros A B IhA IhB i f s [H1 H2].
  unfold seq_get.
  unfold le in *. unfold lt in *.
  repeat (rewrite If_r; try math).
  apply nth_map. unfold length in *. math.
Qed.

Definition filter {A} {Ih : Inhab A} := @LibList.filter A.

Lemma filter_elems :
  forall A113 : Type,
  forall {Ih : Inhab A113},
  forall f : A113 -> bool,
  forall s : sequence A113,
  forall x, mem x s -> f x -> mem x (filter f s).
Proof.
  intros A IhA f s x H1 H2.
  unfold mem in *. unfold multiplicity in *.
  unfold gt in *.
  unfold filter in *.
  induction s as [|e t IHt].
  - inversion H1.
  - rewrite filter_cons.
    destruct classicT.
    + rewrite count_cons.
      destruct classicT.
      * math.
      * rewrite Nat.add_0_r. apply IHt.
        rewrite count_cons in H1.
        rewrite If_r in H1; auto. rewrite Nat.add_0_r in H1. auto.
    + apply IHt.
      assert (E: e = x \/ e <> x). apply classic.
      destruct E.
      subst. contradiction.
      rewrite count_cons in H1. rewrite If_r in H1. rewrite Nat.add_0_r in H1. auto. auto.
Qed.

Fixpoint set_aux {A} (s : sequence A) (n : nat) (x : A) : sequence A :=
  match s, n with
  |nil, _ => arbitrary
  |_ :: t, O => x :: t
  |e :: t, S n' => e :: set_aux t n' x
  end.

Definition set {A} {Ih : Inhab A} (s : sequence A) (n : Z) (x : A) : sequence A :=
  If n < 0 then arbitrary else set_aux s (Z.to_nat n) x.

Lemma set_aux_elem :
  forall A {IhA : Inhab A} s (i : nat) (x : A),
    0 <= i < LibList.length s ->
    nth i (set_aux s i x) = x.
Proof.
  induction s as [|e t Ih]; intros i x [H1 H2].
  - rew_list in H2. math.
  - simpl. destruct i as [|i].
    + apply nth_zero.
    + rewrite nth_cons. apply Ih. split. math. rew_list in H2. math.
Qed.
  
Lemma set_elem :
  forall A121 : Type,
  forall {Ih : Inhab A121},
  forall s : sequence A121,
  forall i : Coq.Numbers.BinNums.Z,
  forall x : A121,
  Coq.Init.Logic.and (le (0)%Z i) (lt i (length s)) ->
  Coq.Init.Logic.eq (seq_get (set s i x) i) x.
Proof.
  intros A IHA s i x [H1 H2].
  unfold le in *. unfold lt in *. unfold seq_get in *. unfold length in *.
  rewrite If_r; try math.
  unfold set. rewrite If_r; try math.
  apply set_aux_elem.
  split; math.
Qed.

Lemma set_aux_elem_other :
  forall A {Ih :Inhab A} s (i1 : nat) i2 (x : A),
    i1 <> i2 ->
    i1 < LibList.length s ->
    i2 < LibList.length s ->
    nth i2 (set_aux s i1 x) = nth i2 s.
Proof.
  intros A IhA s.
  induction s as [|e s Ih]; intros i1 i2 x H1 H2 H3.
  - rew_list in *. math.
  - simpl. destruct i1 as [|i1].
    + destruct i2 as [|i2].
      * contradiction.
      * repeat (rewrite nth_cons). auto.
    + destruct i2 as [|i2].
      * repeat (rewrite nth_cons). auto.
      * repeat (rewrite nth_cons).
        rew_list in H2.
        rew_list in H3.
        rewrite Ih; try math.
        auto.
Qed.

Lemma set_elem_other :
  forall A130 : Type,
  forall {Ih : Inhab A130},
  forall s : sequence A130,
  forall i1 : Coq.Numbers.BinNums.Z,
  forall i2 : Coq.Numbers.BinNums.Z,
  forall x : A130,
    Coq.Init.Logic.not (Coq.Init.Logic.eq i1 i2) ->
    Coq.Init.Logic.and (le (0)%Z i1) (lt i1 (length s)) ->
    Coq.Init.Logic.and (le (0)%Z i2) (lt i2 (length s)) ->
    Coq.Init.Logic.eq (seq_get (set s i1 x) i2) (seq_get s i2).
Proof.
  intros A IhA s i1 i2 x H1 H2 H3.
  unfold le in *. unfold lt in *. unfold length in *.
  unfold seq_get. unfold set. repeat (rewrite If_r; try math).
  apply set_aux_elem_other; math.
Qed.

Definition rev {A} {Ih : Inhab A} := @LibList.rev A .

Lemma rev_length :
  forall A134 : Type,
  forall {Ih: Inhab A134},
  forall s : sequence A134,
    Coq.Init.Logic.eq (length s) (length (rev s)).
Proof.
  intros A Ih s. unfold length. unfold rev. rew_list. auto.
Qed.

Lemma rev_elems :
  forall A143 : Type,
  forall {Ih : Inhab A143},
  forall i : Coq.Numbers.BinNums.Z,
  forall s : sequence A143,
  Coq.Init.Logic.and (le (0)%Z i) (lt i (length s)) ->
  Coq.Init.Logic.eq (seq_get (rev s) i) (
    seq_get s (minus (minus (length s) 1) (i)%Z)
    ).
Proof.
  intros A Ih i s [H1 H2].
  unfold le in *. unfold lt in *.
  unfold minus in *.
  unfold seq_get. repeat (rewrite If_r; try math).
  unfold length in *.
  rewrite Z2Nat.inj_sub; try math.
  rewrite Z2Nat.inj_sub; try math.
  simpl. unfold Pos.to_nat. simpl.
  unfold length. rewrite to_nat_nat.
  apply nth_rev.
  math.
Qed.

Definition fold A B {IhA : Inhab A} {IhB : Inhab B} (f : A -> B -> A) (x : A) (s : sequence B) : A  :=
  LibList.fold_left (fun x y => f y x) x s.

Lemma fold_empty :
  forall A148 : Type,
  forall A149 : Type,
  forall {Ih1 : Inhab A148},
  forall {Ih2 : Inhab A149},
  forall f : A149 -> A148 -> A149,
  forall acc : A149,
    Coq.Init.Logic.eq (fold f acc (@empty A148 Ih1)) acc.
Proof.
  intros A1 A2 Ih1 Ih2 f acc.
  unfold fold.
  apply fold_left_nil.
Qed.

Lemma fold_cons :
  forall a158 : Type,
  forall a159 : Type,
  forall {a158Ih : Inhab a158},
  forall {a159Ih : Inhab a159},
  forall f : a159 -> a158 -> a159,
  forall acc : a159,
  forall x : a158,
  forall l : sequence a158,
  Coq.Init.Logic.eq (fold f acc (cons x l)) (fold f (f acc x) l).
Proof.
  intros A B IhA IhB f acc x l.
  unfold fold.
  rewrite cons_std.
  rewrite fold_left_cons.
  reflexivity.
Qed.

Lemma extensionality :
  forall A171 : Type,
  forall {Ih : Inhab A171},
  forall s1 : sequence A171,
  forall s2 : sequence A171,
  Coq.Init.Logic.eq (length s1) (length s2) ->
  (
    forall i : Coq.Numbers.BinNums.Z,
    Coq.Init.Logic.and (le (0)%Z i) (lt i (length s1)) ->
    Coq.Init.Logic.eq (seq_get s1 i) (seq_get s2 i)
  ) -> s1 = s2.
Proof.
  intros A IhA s1 s2 H1 H2.
  unfold le in *. unfold lt in *. unfold length in *.
  unfold seq_get in *.
  apply eq_nat_of_eq_int in H1.
  apply eq_of_extens with IhA.
  auto.
  intros. specialize H2 with (Z.of_nat n).
  repeat (rewrite If_r in H2; try math).
  rewrite to_nat_nat in H2.
  apply H2. math.
Qed.
  
Parameter fold_left :
  forall A : Type,
  forall B : Type,
  forall {Ih : Inhab A},
  forall {Ih : Inhab B},
  (A -> B -> A) -> A -> sequence B -> A.

Parameter of_list :
  forall a : Type,
  forall {aIh : Inhab a},
  list a -> sequence a.

Parameter fold_right :
  forall A : Type,
  forall B : Type,
  forall {Ih : Inhab A},
  forall {Ih : Inhab B},
  (B -> A -> A) -> sequence B -> A -> A.

Definition get {A} {Ih : Inhab A} := @seq_get A Ih.

End Sequence.

Module Bag.

Parameter t : Type -> Type.

Parameter T :
  forall a : Type,
  forall {aIh : Inhab a},
  t a -> t a -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter multiplicity :
  forall a : Type,
  forall {aIh : Inhab a},
  a -> bag a -> Coq.Numbers.BinNums.Z.

Parameter well_formed :
  forall a173 : Type,
  forall {a173Ih : Inhab a173},
  forall b : a173,
  forall x : bag a173,
  ge (multiplicity b x) (0)%Z.

Parameter empty : forall a : Type, forall {aIh : Inhab a}, bag a.

Parameter empty_mult :
  forall a176 : Type,
  forall {a176Ih : Inhab a176},
  forall x : a176,
  Coq.Init.Logic.eq (multiplicity x (@empty a176 a176Ih)) (0)%Z.

Parameter init :
  forall a : Type,
  forall {aIh : Inhab a},
  (a -> Coq.Numbers.BinNums.Z) -> bag a.

Parameter init_axiom :
  forall a182 : Type,
  forall {a182Ih : Inhab a182},
  forall f : a182 -> Coq.Numbers.BinNums.Z,
  forall x : a182,
  Coq.Init.Logic.eq (max (0)%Z (f x)) (multiplicity x (init f)).

Parameter add :
  forall a : Type,
  forall {aIh : Inhab a},
  a -> bag a -> bag a.

Parameter add_mult_x :
  forall a188 : Type,
  forall {a188Ih : Inhab a188},
  forall b : bag a188,
  forall x : a188,
  Coq.Init.Logic.eq (multiplicity x (add x b)) (
    plus (1)%Z (multiplicity x b)
  ).

Parameter add_mult_neg_x :
  forall a196 : Type,
  forall {a196Ih : Inhab a196},
  forall x : a196,
  forall y : a196,
  forall b : bag a196,
  Coq.Init.Logic.not (Coq.Init.Logic.eq x y) ->
  Coq.Init.Logic.eq (multiplicity y (add x b)) (multiplicity y b).

Definition singleton  (a : Type) { aIh : Inhab a } (x : a) : bag a:=
add x (@empty a aIh).

Definition mem  (a : Type) { aIh : Inhab a } (x : a) (b : bag a) : Prop:=
gt (multiplicity x b) (0)%Z.

Parameter remove :
  forall a : Type,
  forall {aIh : Inhab a},
  a -> bag a -> bag a.

Parameter remove_mult_x :
  forall a205 : Type,
  forall {a205Ih : Inhab a205},
  forall b : bag a205,
  forall x : a205,
  Coq.Init.Logic.eq (multiplicity x (remove x b)) (
    max (0)%Z (minus (multiplicity x b) (1)%Z)
  ).

Parameter remove_mult_neg_x :
  forall a213 : Type,
  forall {a213Ih : Inhab a213},
  forall x : a213,
  forall y : a213,
  forall b : bag a213,
  Coq.Init.Logic.not (Coq.Init.Logic.eq x y) ->
  Coq.Init.Logic.eq (multiplicity y (remove x b)) (multiplicity y b).

Parameter union :
  forall a : Type,
  forall {aIh : Inhab a},
  bag a -> bag a -> bag a.

Parameter union_all :
  forall a221 : Type,
  forall {a221Ih : Inhab a221},
  forall b : bag a221,
  forall b' : bag a221,
  forall x : a221,
  Coq.Init.Logic.eq (max (multiplicity x b) (multiplicity x b')) (
    multiplicity x (union b b')
  ).

Parameter sum :
  forall a : Type,
  forall {aIh : Inhab a},
  bag a -> bag a -> bag a.

Parameter sum_all :
  forall a229 : Type,
  forall {a229Ih : Inhab a229},
  forall b : bag a229,
  forall b' : bag a229,
  forall x : a229,
  Coq.Init.Logic.eq (plus (multiplicity x b) (multiplicity x b')) (
    multiplicity x (sum b b')
  ).

Parameter inter :
  forall a : Type,
  forall {aIh : Inhab a},
  bag a -> bag a -> bag a.

Parameter inter_all :
  forall a237 : Type,
  forall {a237Ih : Inhab a237},
  forall b : bag a237,
  forall b' : bag a237,
  forall x : a237,
  Coq.Init.Logic.eq (min (multiplicity x b) (multiplicity x b')) (
    multiplicity x (inter b b')
  ).

Parameter diff :
  forall a : Type,
  forall {aIh : Inhab a},
  bag a -> bag a -> bag a.

Parameter diff_all :
  forall a245 : Type,
  forall {a245Ih : Inhab a245},
  forall b : bag a245,
  forall b' : bag a245,
  forall x : a245,
  Coq.Init.Logic.eq (
    max (0)%Z (minus (multiplicity x b) (multiplicity x b'))
  ) (multiplicity x (diff b b')).

Definition disjoint  (a : Type) { aIh : Inhab a } (b : bag a) (
  b' : bag a
) : Prop:=
forall x : a,
mem x b -> Coq.Init.Logic.not (mem x b').

Definition subset  (a : Type) { aIh : Inhab a } (b : bag a) (b' : bag a) : Prop:=
forall x : a,
le (multiplicity x b) (multiplicity x b').

Parameter filter :
  forall a : Type,
  forall {aIh : Inhab a},
  (a -> Prop) -> bag a -> bag a.

Parameter filter_mem :
  forall a259 : Type,
  forall {a259Ih : Inhab a259},
  forall b : bag a259,
  forall x : a259,
  forall f : a259 -> bool,
  f x ->
  Coq.Init.Logic.eq (multiplicity x (filter f b)) (multiplicity x b).

Parameter filter_mem_neg :
  forall a266 : Type,
  forall {a266Ih : Inhab a266},
  forall b : bag a266,
  forall x : a266,
  forall f : a266 -> bool,
  Coq.Init.Logic.not (f x) ->
  Coq.Init.Logic.eq (multiplicity x (filter f b)) (0)%Z.

Parameter cardinal :
  forall a : Type,
  forall {aIh : Inhab a},
  bag a -> Coq.Numbers.BinNums.Z.

Definition finite  (a : Type) { aIh : Inhab a } (b : bag a) : Prop:=
Coq.Init.Logic.ex (
  fun s : sequence a =>
  forall x : a,
  mem x b -> Sequence.mem x s
).

Parameter card_nonneg :
  forall a273 : Type,
  forall {a273Ih : Inhab a273},
  forall b : bag a273,
  ge (cardinal b) (0)%Z.

Parameter card_empty :
  forall a276 : Type,
  forall a274 : Type,
  forall {a276Ih : Inhab a276},
  forall {a274Ih : Inhab a274},
  forall b : a274,
  Coq.Init.Logic.eq (cardinal (@empty a276 a276Ih)) (0)%Z.

Parameter card_singleton :
  forall a280 : Type,
  forall {a280Ih : Inhab a280},
  forall x : a280,
  Coq.Init.Logic.eq (cardinal (singleton x)) (1)%Z.

Parameter card_union :
  forall a289 : Type,
  forall {a289Ih : Inhab a289},
  forall b1 : bag a289,
  forall b2 : bag a289,
  finite b1 ->
  finite b2 ->
  Coq.Init.Logic.eq (cardinal (union b1 b2)) (
    plus (cardinal b1) (cardinal b2)
  ).

Parameter card_add :
  forall a296 : Type,
  forall {a296Ih : Inhab a296},
  forall x : a296,
  forall b : bag a296,
  finite b ->
  Coq.Init.Logic.eq (cardinal (add x b)) (plus (cardinal b) (1)%Z).

Parameter card_map :
  forall a303 : Type,
  forall {a303Ih : Inhab a303},
  forall f : a303 -> bool,
  forall b : bag a303,
  finite b -> le (cardinal (filter f b)) (cardinal b).

Parameter of_seq :
  forall a : Type,
  forall {aIh : Inhab a},
  sequence a -> bag a.

Parameter of_seq_multiplicity :
  forall a308 : Type,
  forall {a308Ih : Inhab a308},
  forall s : sequence a308,
  forall x : a308,
  Coq.Init.Logic.eq (Sequence.multiplicity x s) (
    multiplicity x (of_seq s)
  ).

End Bag.

Definition set_create {A} {Ih : Inhab A} := fun (_:A) => False.

Module _Set.
  Definition t := set.
  
Parameter T :
  forall a : Type,
  forall {aIh : Inhab a},
  t a -> t a -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Import TLC.LibSet.

  Definition mem {A} {Ih : Inhab A} (x : A) (s : set A) : Prop := is_in x s.
  Definition empty {A} {Ih : Inhab A} : set A := empty.
  Lemma empty_mem :
    forall A {Ih : Inhab A} x,
      ~ mem x (@empty A Ih).
    intros. unfold empty. auto.
  Qed.
  Definition add {A} {Ih : Inhab A} (x : A) (s : set A) : set A := s \u (single x).
  Lemma add_mem :
    forall A {Ih : Inhab A} s (x : A), mem x (add x s).
    intros. unfold mem. unfold add. rewrite set_in_union_eq.
    right. rewrite in_single_eq. auto. 
  Qed.
  
  Lemma add_mem_neq :
    forall a323 : Type,
    forall {a323Ih : Inhab a323},
    forall s : set a323,
    forall x : a323,
    forall y : a323,
      Coq.Init.Logic.not (Coq.Init.Logic.eq x y) ->
      Coq.Init.Logic.iff (mem x s) (mem x (add y s)).
  Proof.
    intros A Ih s x y Neq.
    split; intro H; unfold add in *; unfold mem in *.
    - rewrite set_in_union_eq. auto.
    - rewrite set_in_union_eq in H. destruct H.
      + auto.
      + rewrite in_single_eq in H. contradiction.
  Qed.

  Definition singleton  (a : Type) { aIh : Inhab a } (x : a) : set a:=
    add x (@empty a aIh).

  Definition remove {A} {Ih : Inhab A} (x : A) (s : set A) : set A :=
    s \-- x.

  Lemma remove_mem :
    forall a329 : Type,
    forall {a329Ih : Inhab a329},
    forall s : set a329,
    forall x : a329,
      Coq.Init.Logic.not (mem x (remove x s)).
  Proof.
    intros A Ih s x.
    unfold remove, mem, singleton, empty, add.
    rewrite set_in_remove_eq.
    unfold not. intros [H1 H2].
    destruct H2. rewrite set_in_single_eq. auto.
  Qed.
  
Lemma remove_mem_neq :
  forall a336 : Type,
  forall {a336Ih : Inhab a336},
  forall s : set a336,
  forall x : a336,
  forall y : a336,
  Coq.Init.Logic.not (Coq.Init.Logic.eq x y) ->
  Coq.Init.Logic.iff (mem x s) (mem x (remove y s)).
  intros A Ih s x y Neq. split; intro H;
  unfold mem, remove, singleton, add, empty in *;
    rewrite set_in_remove_eq in *.
    split. auto. unfold not. intros H1. contradiction.
  - destruct H. auto.
Qed.

Definition union {A} {Ih : Inhab A} (s1 : set A) (s2 : set A) : set A :=
  s1 \u s2.

Lemma union_mem :
  forall a343 : Type,
  forall {a343Ih : Inhab a343},
  forall s : set a343,
  forall s' : set a343,
  forall x : a343,
  Coq.Init.Logic.or (mem x s) (mem x s') -> mem x (union s s').
Proof.
  intros A Ih s s' x [H | H]; unfold mem, union in *;
  rewrite set_in_union_eq; [left | right]; auto.
Qed.


Lemma union_mem_neg :
  forall a350 : Type,
  forall {a350Ih : Inhab a350},
  forall s : set a350,
  forall s' : set a350,
  forall x : a350,
  Coq.Init.Logic.not (mem x s) ->
  Coq.Init.Logic.not (mem x s') -> Coq.Init.Logic.not (mem x (union s s')).
Proof.
  intros A Ih s s' x H1 H2.
  unfold mem, union in *.
  unfold not. intros H3.
  rewrite set_in_union_eq in H3.
  destruct H3 as [H3 | H3]; contradiction.
Qed.

Definition inter {A} {Ih : Inhab A} (s1 : set A) (s2 : set A) : set A := s1 \n s2.

Lemma inter_mem :
  forall a357 : Type,
  forall {a357Ih : Inhab a357},
  forall s : set a357,
  forall s' : set a357,
  forall x : a357,
  mem x s -> mem x s' -> mem x (inter s s').
Proof.
  intros A Ih s s' x H1 H2.
  unfold mem, inter in *.
  rewrite set_in_inter_eq. split; auto.
Qed.


Lemma inter_mem_neq :
  forall a364 : Type,
  forall {a364Ih : Inhab a364},
  forall s : set a364,
  forall s' : set a364,
  forall x : a364,
  Coq.Init.Logic.not (Coq.Init.Logic.or (mem x s) (mem x s')) ->
  Coq.Init.Logic.not (mem x (inter s s')).
Proof.
  intros a Ih s s' x H1.
  unfold mem, inter in *.
  rewrite set_in_inter_eq.
  unfold not in *. intros [H2 H3].
  destruct H1. auto.
Qed.


Definition disjoint  (a : Type) { aIh : Inhab a } (s : set a) (
  s' : set a
) : Prop:=
Coq.Init.Logic.eq (inter s s') (@empty a aIh).

Definition diff {A} {Ih : Inhab A} (s1 : set A) (s2 : set A) : set A :=
  LibContainer.remove s1 s2.

Lemma diff_mem :
  forall a373 : Type,
  forall {a373Ih : Inhab a373},
  forall s : set a373,
  forall s' : set a373,
  forall x : a373,
  mem x s' -> Coq.Init.Logic.not (mem x (diff s s')).
Proof.
  intros A Ih s s' x H1.
  unfold mem, diff in *.
  rewrite set_in_remove_eq. unfold not.
  intros [H2 H3]. contradiction.
Qed.

Lemma diff_mem_fst :
  forall a380 : Type,
  forall {a380Ih : Inhab a380},
  forall s : set a380,
  forall s' : set a380,
  forall x : a380,
  Coq.Init.Logic.not (mem x s') ->
  Coq.Init.Logic.iff (mem x s) (mem x (diff s s')).
Proof.
  intros A Ih s s' x H1.
  unfold mem, diff in *.
  split; intro H2; rewrite set_in_remove_eq in *.
    split; auto.
  - destruct H2 as [H2 H3]. auto.
Qed.

Definition subset  (a : Type) { aIh : Inhab a } (s : set a) (s' : set a) : Prop:=
  forall x : a,
    mem x s -> mem x s'.


Definition map {A} {B} {Iha : Inhab A} {Ihb : Inhab B} (f : A -> B) (s : set A) : set B :=
  fun (x : B) => exists (y : A), f y = x /\ (y \in s).


Lemma set_map :
  forall a394 : Type,    
  forall a393 : Type,
  forall {a394Ih : Inhab a394},    
  forall {a393Ih : Inhab a393},
  forall f : a393 -> a394,
  forall s : set a393,
  forall x : a394,
  Coq.Init.Logic.iff (mem x (map f s)) (
    Coq.Init.Logic.ex (
      fun y : a393 =>
      Coq.Init.Logic.and (Coq.Init.Logic.eq (f y) x) (mem y s)
    )
  ).
Proof.
  intros A IhA B IhB f s x. unfold mem, map in *. split; auto. 
Qed.

Definition cardinal {A} {Ih : Inhab A} (s : set A) : Z := Z.of_nat (card s).

Definition finite  (a : Type) { aIh : Inhab a } (s : set a) : Prop:=
Coq.Init.Logic.ex (
  fun seq : sequence a =>
  forall x : a,
  mem x s -> Sequence.mem x seq
).

Lemma finite_trans :
  forall A {AIh : Inhab A} (s : set A),
    finite s -> LibSet.finite s.
  intros A Ih s H.
  unfold finite in H.
  destruct H as [seq H].
  apply finite_of_list_covers with seq.
  unfold list_covers. unfold mem in H.
  intros x H2. specialize H with x. apply Sequence.tlc_mem in H; auto.
Qed.

Lemma cardinal_nonneg :
  forall a399 : Type,
  forall {a399Ih : Inhab a399},
  forall s : set a399,
  ge (cardinal s) (0)%Z.
Proof.
  intros A Ih s.
  unfold ge, cardinal.
  math.
Qed.


Lemma cardinal_empty :
  forall a403 : Type,
  forall {a403Ih : Inhab a403},
    Coq.Init.Logic.eq (cardinal (@empty a403 a403Ih)) (0)%Z.
Proof.
  intros A IhA.
  unfold cardinal, empty.
  rewrite <- Nat2Z.inj_0.
  f_equal.
  apply card_empty.
Qed.


Lemma cardinal_remove :
  forall a415 : Type,
  forall {a415Ih : Inhab a415},
  forall s : set a415,
  forall x : a415,
  finite s ->
  (
    if classicT (mem x s) then
      Coq.Init.Logic.eq (cardinal (remove x s)) (minus (cardinal s) (1)%Z)
      else
    Coq.Init.Logic.eq (cardinal (remove x s)) (cardinal s)
  ).
Proof.
  intros A Ih s x H.
  unfold mem, cardinal, minus, remove, singleton, empty, add.
  apply (@finite_trans A Ih) in H.
  assert (P : x \in s \/ ~ x \in s).
  { apply classic. }
  destruct P.
  - rewrite If_l; auto.
    rewrite card_diff_single; auto.
    + assert (Q: 1%nat <= card s).
      { apply card_ge_one with x; auto. }
      { math. }
  - rewrite If_r; auto.
    f_equal.
    f_equal.
    rewrite set_in_extens_eq.
    intros y. split; intros H1;
      rewrite set_in_remove_eq in *.
      destruct H1 as [H1 H2]. auto.
    + split. auto. unfold not. intro H2.
      rewrite set_in_single_eq in H2.
      subst. contradiction.
Qed.


Lemma cardinal_add :
  forall a427 : Type,
  forall {a427Ih : Inhab a427},
  forall s : set a427,
  forall x : a427,
  finite s ->
  (
    if classicT (mem x s) then
      Coq.Init.Logic.eq (cardinal (add x s)) (cardinal s)
      else
    Coq.Init.Logic.eq (cardinal (add x s)) (plus (cardinal s) (1)%Z)
  ).
Proof.
  intros A Ih s x H.
  unfold plus, cardinal, add in *.
  apply finite_trans in H.
  unfold mem. assert (P : x \in s \/ ~ x \in s). {apply classic. }
  destruct P.
  - rewrite If_l; auto. f_equal. f_equal. rewrite set_in_extens_eq.
    intro y.
    assert (Q:y = x \/ y <> x). { apply classic. }
    split; intro H1; rewrite set_in_union_eq in *.
    + destruct Q. subst. auto.
      destruct H1. auto. contradiction.
    + left. auto.
  - rewrite If_r; auto. rewrite card_disjoint_union_single; auto.
    math.
Qed.
        
Definition of_seq {A} {Ih : Inhab A} (s: sequence A) : set A :=
  fun x => LibList.mem x s.


Lemma of_seq_set :
  forall a433 : Type,
  forall {a433Ih : Inhab a433},
  forall x : a433,
  forall s : sequence a433,
  Coq.Init.Logic.iff (Sequence.mem x s) (mem x (of_seq s)).
Proof.
  intros A Ih x s.
  unfold mem.
  unfold of_seq.
  split; intros H.
  - apply Sequence.tlc_mem in H.    
    auto.
  - apply Sequence.tlc_mem. auto.
Qed.


Parameter fold :
  forall a : Type,
  forall b : Type,
  forall {aIh : Inhab a},
  forall {bIh : Inhab b},
  (a -> b -> b) -> set a -> b -> b.

End _Set.

End Stdlib_proof.


(* Module Bag. *)
(*   Definition t (A : Type) := A -> nat. *)

(*   Parameter T : *)
(*     forall a : Type, *)
(*     forall {aIh : Inhab a}, *)
(*       t a -> t a -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop. *)

(*   Definition multiplicity (a : Type) {aIh : Inhab a} (x : a) (b : bag a) : Z := *)
(*     b x. *)

(*   Lemma well_formed : *)
(*     forall a173 : Type, *)
(*     forall {a173Ih : Inhab a173}, *)
(*     forall b : a173, *)
(*     forall x : bag a173, *)
(*       ge (multiplicity b x) (0)%Z. *)
(*   Proof. *)
(*     intros A Ih b x. *)
(*     unfold multiplicity. unfold ge. math. *)
(*   Qed. *)

(*  Import TLC.LibMultiset. *)

(*  Open Scope container_scope. *)
 
(*  Definition empty (A : Type) (Ih : Inhab A) : bag A := empty. *)
   
(*  Lemma empty_mult : *)
(*   forall a176 : Type, *)
(*   forall {a176Ih : Inhab a176}, *)
(*   forall x : a176, *)
(*   Coq.Init.Logic.eq (multiplicity x (@empty a176 a176Ih)) (0)%Z. *)
(*  Proof. auto. Qed. *)
 
(*  Definition init {A} {aIh : Inhab A} (f : A -> Z) (x : A) : nat := *)
(*    Z.to_nat (f x). *)

(*  Lemma init_axiom : *)
(*   forall a182 : Type, *)
(*   forall {a182Ih : Inhab a182}, *)
(*   forall f : a182 -> Coq.Numbers.BinNums.Z, *)
(*   forall x : a182, *)
(*   Coq.Init.Logic.eq (max (0)%Z (f x)) (multiplicity x (init f)). *)
(*  Proof. *)
(*    intros A Ih f x. *)
(*    unfold min. unfold multiplicity. unfold init. unfold max. *)
(*    destruct (f x); math. *)
(*  Qed. *)

(*  Definition add {A} {aIh : Inhab A} (x : A) (b : bag A) : bag A := *)
(*    \{x} \u b. *)

(*  Lemma single : *)
(*    forall A {Ih : Inhab A} (x : A), *)
(*      multiplicity x \{x} = 1. *)
(*  Proof. *)
(*  Admitted. *)
   
(*  Lemma add_mult_x : *)
(*     forall a188 : Type, *)
(*     forall {a188Ih : Inhab a188}, *)
(*     forall b : bag a188, *)
(*     forall x : a188, *)
(*       Coq.Init.Logic.eq (multiplicity x (add x b)) ( *)
(*           plus (1)%Z (multiplicity x b) *)
(*         ). *)
(*    intros A Ih b x. *)
(*    unfold multiplicity. unfold add. unfold plus. *)
   
(*  Admitted. *)
 
(*  Lemma add_mult_neg_x : *)
(*   forall a195 : Type, *)
(*   forall {a195Ih : Inhab a195}, *)
(*   forall x : a195, *)
(*   forall y : a195, *)
(*   forall b : bag a195, *)
(*     Coq.Init.Logic.not (Coq.Init.Logic.eq x y) -> *)
(*     Coq.Init.Logic.eq (multiplicity y (add x b)) (multiplicity y b)%Z. *)
(*  Proof. *)
(*    intros A Ih x y b H. *)
(*    unfold multiplicity. unfold add. *)
(*    rewrite If_r; auto. *)
(*  Qed. *)

(*  Definition singleton  (a : Type) { aIh : Inhab a } (x : a) : bag a:= *)
(*    add x (@empty a aIh). *)

(*  Definition mem  (a : Type) { aIh : Inhab a } (x : a) (b : bag a) : Prop:= *)
(*    gt (multiplicity x b) (0)%Z. *)

(*  Definition remove {A} {Ih : Inhab A} (x : A) (b : bag A) : bag A := *)
   
   
(* End Bag. *)
(* End Stdlib_proof. *)
