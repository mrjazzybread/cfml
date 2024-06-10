Set Implicit Arguments.

Require Import Gospel.

Require Import CFML.SepBase CFML.SepLifted CFML.WPLib CFML.WPLifted CFML.WPRecord CFML.WPArray CFML.WPBuiltin.

Require CFML.Stdlib.Array_ml CFML.Stdlib.List_ml CFML.Stdlib.Sys_ml.

Require Import Coq.ZArith.BinIntDef CFML.Semantics CFML.WPHeader.

Require Import TLC.LibLogic TLC.LibRelation TLC.LibInt Coq.ZArith.BinInt.

Delimit Scope Z_scope with Z.
Require Import gospelstdlib_mli.

Module Stdlib_proof : Stdlib.

  Definition sequence A := list A.
  Definition bag A := A -> Z.
  Definition set A := A -> Prop.
  Definition map A B := A -> B.
  Definition succ := Z.succ.
  Definition pred := Z.pred.
  Definition neg := Z.opp.
  Definition add := Z.add.
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
  Definition app := app.
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
  
  Definition length {A} (s : sequence A) : Z :=
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
  
  Definition seq_sub {A} (s : sequence A) (i1 : Z) (i2 : Z) : sequence A :=
    if (i1 <? 0) || (i1 >? i2) || (i2 >? length s)
    then arbitrary
    else
      let i1 := Z.to_nat i1 in
      let i2 := Z.to_nat i2 in
      seq_sub_aux s i1 i2.

  
Definition seq_sub_l  (A : Type) (s : sequence A) (
  i : Coq.Numbers.BinNums.Z
) : sequence A:=
seq_sub s i (length s).

Definition seq_sub_r  (A : Type) (s : sequence A) (
  i : Coq.Numbers.BinNums.Z
) : sequence A:=
seq_sub s (0)%Z i.

Definition map_set  (A : Type) (B : Type) (f : A -> B) (x : A) (y : B) : A ->
B:=
fun arg : A =>
if classicT (Coq.Init.Logic.eq arg x) then y else f x.

Module Sequence.

  
Definition in_range  (A : Type) (s : sequence A) (
  i : Coq.Numbers.BinNums.Z
) : Prop:=
Coq.Init.Logic.and (le (0)%Z i) (lt i (length s)).

Lemma length_nonneg :
  forall A11 : Type,
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
  forall s : sequence A17,
  forall s' : sequence A17,
  Coq.Init.Logic.eq (length (app s s')) (add (length s) (length s')).
Proof.
  intros.
  unfold add.
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
  Coq.Init.Logic.and (le i (0)%Z) (lt (0)%Z (length s)) ->
  Coq.Init.Logic.eq (seq_get (app s s') i) (seq_get s i).


Parameter append_elems_right :
  forall A37 : Type,
  forall {Ih : Inhab A37},
  forall s : sequence A37,
  forall s' : sequence A37,
  forall i : Coq.Numbers.BinNums.Z,
  Coq.Init.Logic.and (le (length s) i) (lt i (add (length s) (length s'))) ->
  Coq.Init.Logic.eq (seq_get (app s s') (add i (length s))) (seq_get s' i).

Parameter subseq :
  forall A45 : Type,
  forall {Ih : Inhab A45},
  forall s : sequence A45,
  forall i : Coq.Numbers.BinNums.Z,
  forall i1 : Coq.Numbers.BinNums.Z,
  forall i2 : Coq.Numbers.BinNums.Z,
  Coq.Init.Logic.and (le i1 i) (lt i i2) ->
  Coq.Init.Logic.eq (seq_get s i) (seq_get (seq_sub s i1 i2) (minus i i1)).

Locate "++".

Fixpoint init_aux {A} (n : nat) (f : Z -> A) : sequence A :=
  match n with
  |O => nil
  |S n' =>  LibList.app (init_aux n' f) ((cons (f n') nil)) end.

Definition init {A} (n : Z) (f : Z -> A) : sequence A :=
  If n < 0 then arbitrary else
    init_aux (Z.to_nat n) f.

Lemma init_pos :
  forall A n (f : Z -> A),
    n >= 0 -> init n f = init_aux (Z.to_nat n) f.
Proof.
  intros A n f H.
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
  forall n : Coq.Numbers.BinNums.Z,
  forall f : Coq.Numbers.BinNums.Z -> A49,
    n >= 0 -> Coq.Init.Logic.eq (length (init n f)) n.
Proof.
  intros A n f H.
  unfold init.
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

Definition empty {A} := @nil A.
Lemma empty_length :
  forall A, Coq.Init.Logic.eq (length (@empty A)) (0)%Z.
Proof.
  intro A.
  unfold length. rew_list. auto.
Qed.

Definition singleton  (A : Type) (x : A) : sequence A:=
init (1)%Z (fun _ : Coq.Numbers.BinNums.Z => x).

Definition cons  (A : Type) (x : A) (s : sequence A) : sequence A:=
app (singleton x) s.

Lemma cons_std :
  forall A (x : A) s,
    cons x s = List.cons x s.
Proof.
  intros.
  unfold cons.
  unfold singleton.
  unfold init.
  rewrite If_r; try math.
  simpl. rew_list. auto.
Qed.

Definition snoc  (A : Type) (s : sequence A) (x : A) : sequence A:=
app s (singleton x).

Definition hd (A : Type) {Ih : Inhab A} (s : sequence A) : A:= seq_get s (0)%Z.

Definition tl (A : Type) (s : sequence A) : sequence A:=
seq_sub_l s (1)%Z.

Definition append  (A : Type) (s1 : sequence A) (s2 : sequence A) : sequence A:=
app s1 s2.

Definition multiplicity {A} (e : A) (s : sequence A) : Z :=
  count (fun x => x = e) s.

Lemma mult_empty :
  forall A73 : Type,
  forall x : A73,
  Coq.Init.Logic.eq (multiplicity x (@empty A73)) (0)%Z.
Proof.
  intros A x.
  unfold multiplicity.
  rewrite count_nil. math.
Qed.

Lemma mult_cons :
  forall A79 : Type,
  forall s : sequence A79,
  forall x : A79,
  Coq.Init.Logic.eq (add (1)%Z (multiplicity x s)) (
    multiplicity x (cons x s)
  ).
Proof.
  intros A s x.
  unfold multiplicity.
  unfold add.
  rewrite cons_std.
  rewrite count_cons.
  rewrite If_l; auto.
  math.
Qed.

Lemma mult_cons_neutral :
  forall A s (x1 : A) x2,
    Coq.Init.Logic.not (Coq.Init.Logic.eq x1 x2) ->
    Coq.Init.Logic.eq (multiplicity x1 s) (multiplicity x1 (cons x2 s)).
Proof.
  intros A s x1 x2 H1.
  unfold multiplicity.
  rewrite cons_std.
  rewrite count_cons.
  rewrite If_r; auto.
Qed.

Lemma mult_length :
  forall A92 : Type,
  forall x : A92,
  forall s : sequence A92,
  Coq.Init.Logic.and (le (0)%Z (multiplicity x s)) (
    le (multiplicity x s) (length s)
  ).
Proof.
  intros A x s.
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

Definition mem  (A : Type) (x : A) (s : sequence A) : Prop:=
gt (multiplicity x s) (0)%Z.

Definition map := LibList.map.

Lemma map_elems :
  forall A100 : Type,
  forall A102 : Type,
  forall {Ih : Inhab A100},
  forall {Ih : Inhab A102},
  forall i : Coq.Numbers.BinNums.Z,
  forall f : A100 -> A102,
  forall s : sequence A100,
  0 <= i < length s -> Coq.Init.Logic.eq (seq_get (map f s) i) (f (seq_get s i)).
Proof.
  intros A B IhA IhB i f s [H1 H2].
  unfold seq_get.
  repeat (rewrite If_r; try math).
  apply nth_map. math.
Qed.

Definition filter := LibList.filter.

Lemma filter_elems :
  forall A113 : Type,
  forall {Ih : Inhab A113},    
  forall f : A113 -> bool,
  forall s : sequence A113,
  forall i : Coq.Numbers.BinNums.Z,
  forall x, mem x s -> f x -> mem x (filter f s).
Proof.
  intros A IhA f s i x H1 H2.
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

Definition _set {A} (s : sequence A) (n : Z) (x : A) : sequence A :=
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
  Coq.Init.Logic.eq (seq_get (_set s i x) i) x.
Proof.
  intros A IHA s i x [H1 H2].
  unfold le in *. unfold lt in *. unfold seq_get in *. unfold length in *.
  rewrite If_r; try math.
  unfold _set. rewrite If_r; try math.
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
    Coq.Init.Logic.eq (seq_get (_set s i1 x) i2) (seq_get s i2).
Proof.
  intros A IhA s i1 i2 x H1 H2 H3.
  unfold le in *. unfold lt in *.
  unfold seq_get. unfold _set. repeat (rewrite If_r; try math).
  apply set_aux_elem_other; math.
Qed.  

Definition rev := LibList.rev.

Lemma rev_length :
  forall A134 : Type,
  forall s : sequence A134,
    Coq.Init.Logic.eq (length s) (length (rev s)).
Proof.
  intros A s. unfold length. rew_list. auto.
Qed.
Set Printing Coercions.
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
  rewrite Z2Nat.inj_sub; try math.
  rewrite Z2Nat.inj_sub; try math.
  simpl. unfold Pos.to_nat. simpl.
  unfold length. rewrite to_nat_nat.
  apply nth_rev.
  math.
Qed.

Definition fold A B (f : A -> B -> A) (x : A) (s : sequence B) : A  := 
  LibList.fold_left (fun x y => f y x) x s.

Lemma fold_empty :
  forall A148 : Type,
  forall A149 : Type,
  forall f : A149 -> A148 -> A149,
  forall acc : A149,
    Coq.Init.Logic.eq (fold f acc (@empty A148)) acc.
Proof.
  intros A1 A2 f acc.
  unfold fold.
  apply fold_left_nil.
Qed.

Lemma fold_cons :
  forall A161 : Type,
  forall f : A161 -> A161 -> A161,
  forall acc : A161,
  forall x : A161,
  forall l : sequence A161,
  Coq.Init.Logic.eq (fold f acc (cons x l)) (fold f (f acc x) l).
Proof.
  intros A f acc x l.
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
  (A -> B -> A) -> A -> sequence B -> A.

Parameter fold_right :
  forall A : Type,
  forall B : Type,
  (B -> A -> A) -> sequence B -> A -> A.


End Sequence.
End Stdlib_proof.
