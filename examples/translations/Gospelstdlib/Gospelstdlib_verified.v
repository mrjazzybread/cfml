Set Implicit Arguments.

From TLC Require Import LibString LibList LibCore LibListZ LibEpsilon LibSet.

Require Import Coq.ZArith.BinInt TLC.LibLogic TLC.LibRelation TLC.LibInt TLC.LibContainer.

Require Import Coq.ZArith.BinIntDef.

Delimit Scope Z_scope with Z.

Require Gospelstdlib_mli.

Module Gospelstdlib : Gospelstdlib_mli.Stdlib.

  Definition sequence A := list A.

  Definition bag A := A -> nat.

  Definition set A := A -> Prop.

  Definition option A := option A.
  Definition Some {A} {Ih_a : Inhab A} (x : A) := Some x.
  Definition None {A} {Ih_a : Inhab A} := @None A.

  Definition map A B := A -> B.

  Definition succ := Z.succ.
  Definition pred := Z.pred.
  Definition neg := Z.opp.
  Definition _mod := Z.modulo.
  Definition pow := Z.pow.
  Definition abs := Z.abs.
  Definition min := Z.min.
  Definition max := Z.max.
  Definition app A {Ih:Inhab A} := @app A.

  Definition seq_get
    {A} {Ih:Inhab A} (s : sequence A) (n : int) : A :=
    s[n].

  Ltac unfold_all :=
    unfold pred in *;
    unfold neg in * ;
    unfold _mod in *;
    unfold pow in * ;
    unfold abs in * ;
    unfold min in * ;
    unfold max in * ;
    unfold app in * ;
    unfold seq_get in *.

  Definition seq_sub {A} {Ih : Inhab A} (s : sequence A) (i1 : Z) (i2 : Z) : sequence A :=
    LibListZ.take (i2 - i1) (LibListZ.drop i1 s).

  Definition seq_sub_l  (A : Type) {Ih : Inhab A} (s : sequence A) (
      i : Coq.Numbers.BinNums.Z
    ) : sequence A:=
    seq_sub s i (length s).

  Definition seq_sub_r (A : Type) {Ih : Inhab A} (s : sequence A) (
      i : Coq.Numbers.BinNums.Z
    ) : sequence A:=
    seq_sub s (0)%Z i.

  Definition monoid {A} `{Inhab A} (f : A -> A -> A) (n : A) : Prop :=
    neutral_l f n /\ neutral_r f n /\ assoc f.

  Lemma monoid_def :
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
  Proof.
    intros A Ih f neutral.
    unfold monoid.
    unfold neutral_l, neutral_r, assoc.
    split.
    - intros [H1 [H2 H3]]. split.
      + rewrite H1. rewrite H2. auto.
      + auto.
    - intros H1.
      repeat split; intros x; specialize H1 with x;
        destruct H1 as [[H1 H2] H3].
      + rewrite H1. apply H2.
      + apply H2.
      + apply H3.
  Qed.

  Definition comm_monoid {A} `{Inhab A} (f : A -> A -> A) (n : A) : Prop :=
    monoid f n /\ comm f.

  Lemma comm_monoid_def :
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
  Proof.
    intros A Ih f neutral.
    unfold comm_monoid, monoid, comm.
    tauto.
  Qed.

  Module Sequence.

    Definition t  (A : Type) : Type:= sequence A.

    Definition in_range  (A : Type) {Ih : Inhab A} (s : sequence A) (
        i : Coq.Numbers.BinNums.Z
      ) : Prop:=
      (0 <= i) /\ (i < (length s)).

    Lemma in_range_def :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall s : sequence A,
      forall i : Z,
        (in_range s i <-> (((0)%Z <= i) /\ (i < length s))).
    Proof.
      unfold in_range.
      tauto.
    Qed.

    Definition length {A} {Ih : Inhab A} (s : sequence A) : Z :=
      LibListZ.length s.

    Lemma length_nonneg :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall s : sequence A,
        ((0)%Z <= length s).
    Proof.
      intros.
      unfold length.
      math.
    Qed.


    Lemma subseq_l :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall s : sequence A,
      forall i : Z,
        (in_range s i -> (seq_sub_l s i = seq_sub s i (length s))).
    Proof.
      auto.
    Qed.

    Lemma subseq_r :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall s : sequence A,
      forall i : Z,
        (in_range s i -> (seq_sub_r s i = seq_sub s (0)%Z i)).
    Proof.
      auto.
    Qed.

    Lemma subseq :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall s : sequence A,
      forall i : Z,
      forall i1 : Z,
      forall i2 : Z,
        (
          (((0)%Z <= i1) /\ ((i1 <= i) /\ ((i < i2) /\ (i2 <= length s)))) -> (
                                                                               seq_get s i = seq_get (seq_sub s i1 i2) ((i - i1))
                                                                             )
        ).
    Proof.
      unfold_all.
      unfold length.
      unfold seq_sub.
      intros A IhA s i i1 i2 [H1 [H2 [H3 H4]]].
      rewrite read_take; try (split; math).
      - rewrite read_drop; try (split; math).
        f_equal.
        math.
      - rewrite LibListZ.length_drop; math.
    Qed.

    Lemma subseq_len :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall s : sequence A,
      forall i1 : Z,
      forall i2 : Z,
        (
          (((0)%Z <= i1) /\ ((i1 <= i2) /\ (i2 < length s))) -> (
                                                                 length (seq_sub s i1 i2) = (i2 - i1)
                                                               )
        ).
    Proof.
      unfold length.
      unfold_all.
      intros A IhA s i1 i2 [H1 [H2 H3]].
      unfold seq_sub.
      rewrite LibListZ.length_take; try math.
      rewrite LibListZ.length_drop; try math.
    Qed.

    Definition empty {A} {Ih : Inhab A} := @nil A.

    Lemma empty_length :
      forall {A : Type},
      forall {Ih_A : Inhab A},
        (@length A Ih_A empty = (0)%Z).
    Proof.
      intro A.
      unfold length. rew_list. auto.
    Qed.

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
        LibListZ.length (init_aux n f) = n.
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
        (init_aux n f)[i] = f i.
    Proof.
      intros A n i f Inh H1 H2.
      induction n as [|n' Ih].
      - math.
      - simpl. rewrite read_app.
        rewrite init_aux_length.
        assert (P : i < n' \/ ~ i < n').
        apply classic.
        destruct P as [P|P].
        + rewrite If_l. auto. math.
        +  assert (Q : i = n'). { math. } rewrite If_r.
           * rewrite Q. rewrite Z.sub_diag. apply read_zero.
           * math.
    Qed.

    Lemma init_elems :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall n : Z,
      forall f : Z -> A,
      forall i : Z,
        ((((0)%Z <= i) /\ (i < n)) -> (seq_get (init n f) i = f i)).
    Proof.
      intros A Inh n f i [H1 H2].
      unfold seq_get.
      unfold init.
      rewrite If_r; try math.
      apply init_i; math.
    Qed.

    Definition singleton (A : Type) {Ih : Inhab A} (x : A) : sequence A:=
      init (1)%Z (fun _ : Coq.Numbers.BinNums.Z => x).

    Lemma singleton_def :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall x : A,
      forall f : Z -> A,
        ((f (0)%Z = x) -> (singleton x = init (1)%Z f)).
    Proof.
      intros A IhA x f H1.
      unfold singleton, init.
      repeat (rewrite If_r; try math;
              simpl; rew_list).
      f_equal.
      rewrite <- H1.
      auto.
    Qed.

    Definition cons (A : Type) {Ih : Inhab A} (x : A) (s : sequence A) : sequence A:=
      x :: s.

    Lemma cons_def :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall x : A,
      forall s : sequence A,
        (cons x s = app (singleton x) s).
    Proof.
      intros A Ih x s.
      unfold app, cons, singleton, init.
      rewrite If_r; try math.
      simpl. rew_list. auto.
    Qed.

    Definition snoc (A : Type) {Ih : Inhab A}(s : sequence A) (x : A) : sequence A:=
      app s (singleton x).

    Lemma snoc_def :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall s : sequence A,
      forall x : A,
        (snoc s x = app s (singleton x)).
    Proof.
      auto.
    Qed.

    Definition hd (A : Type) {Ih : Inhab A} (s : sequence A) : A:= seq_get s (0)%Z.

    Lemma hd_def :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall s : sequence A,
        (hd s = seq_get s (0)%Z).
    Proof.
      auto.
    Qed.

    Definition tl (A : Type){Ih : Inhab A} (s : sequence A) : sequence A:=
      seq_sub_l s (1)%Z.

    Lemma tl_def :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall s : sequence A,
        (tl s = seq_sub_l s (1)%Z).
    Proof.
      auto.
    Qed.

    Definition append  (A : Type){Ih : Inhab A} (s1 : sequence A) (s2 : sequence A) : sequence A:=
      app s1 s2.

    Lemma append_def :
      forall {A : Type},
  forall {Ih_A : Inhab A},
  forall s1 : sequence A,
  forall s2 : sequence A,
  (append s1 s2 = app s1 s2).
    Proof.
      auto.
    Qed.

    Lemma append_length :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall s : sequence A,
      forall s' : sequence A,
        (length (app s s') = (length s + length s')).
    Proof.
      intros.
      unfold length.
      unfold app.
      rew_list.
      math.
    Qed.

    Lemma append_elems_left :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall s : sequence A,
      forall s' : sequence A,
      forall i : Z,
        (in_range s i -> (seq_get (app s s') i = seq_get s i)).
    Proof.
      unfold in_range.
      intros.
      unfold app in *.
      unfold seq_get in *.
      rewrite read_app.
      rewrite If_l.
      + auto.
      + math.
    Qed.

    Lemma append_elems_right :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall s : sequence A,
      forall s' : sequence A,
      forall i : Z,
        (
          ((length s <= i) /\ (i < (length s + length s'))) -> (
                                                                seq_get (app s s') i = seq_get s' ((i - length s))
                                                              )
        ).
    Proof.
      unfold length.
      intros.
      unfold seq_get in *.
      unfold app in *.
      rewrite read_app.
      rewrite If_r.
      + auto.
      + math.
    Qed.

    Definition multiplicity {A}{Ih : Inhab A} (e : A) (s : sequence A) : Z :=
      LibListZ.count (fun x => x = e) s.

    Lemma mult_empty :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall x : A,
        (multiplicity x empty = (0)%Z).
    Proof.
      intros A Ih x.
      unfold multiplicity.
      rew_listx.
      auto.
    Qed.

    Lemma mult_cons :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall s : sequence A,
      forall x : A,
        (((1)%Z + multiplicity x s) = multiplicity x (cons x s)).
    Proof.
      intros A Ih s x.
      unfold multiplicity.
      unfold plus.
      unfold cons.
      rew_listx.
      rewrite If_l; auto.
      math.
    Qed.

    Lemma mult_cons_neutral :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall s : sequence A,
      forall x1 : A,
      forall x2 : A,
        ((x1 <> x2) -> (multiplicity x1 s = multiplicity x1 (cons x2 s))).
    Proof.
      intros A Ih s x1 x2 H1.
      unfold multiplicity.
      unfold cons.
      rew_listx.
      rewrite If_r.
      + math.
      + auto.
    Qed.

    Lemma mult_length :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall x : A,
      forall s : sequence A,
        (((0)%Z <= multiplicity x s) /\ (multiplicity x s <= length s)).
    Proof.
      intros A I x s.
      unfold multiplicity.
      unfold length.
      split.
      - apply count_nonneg.
      - induction s as [|e s' Ih].
        + rew_listx. math.
        + rew_listx.
          assert (E : e = x \/ e <> x). apply classic.
          destruct E;
            [rewrite If_l | rewrite If_r]; auto; math.
    Qed.

    Definition mem  (A : Type) {Ih : Inhab A} (x : A) (s : sequence A) : Prop:= LibList.mem x s.


    Lemma mem_def :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall s : sequence A,
      forall x : A,
        (mem x s <-> (multiplicity x s > (0)%Z)).
    Proof.
      intros A IhA s x.
      unfold_all.
      unfold multiplicity.
      unfold mem.
      split; intros H1.
      + change (LibListZ.count (= x) s > 0%nat).
        rewrite <- LibListZ.Exists_eq_count_pos.
        rewrite Exists_eq_exists_mem.
        exists x; auto.
      + change (LibListZ.count (= x) s > 0%nat) in H1.
        rewrite <- LibListZ.Exists_eq_count_pos in H1.
        rewrite Exists_eq_exists_mem in H1.
        destruct H1 as [y [H1 H2]].
        subst. auto.
    Qed.

    Definition _forall {A} `{Inhab A} (P : A -> Prop) (s : sequence A) :=
      Forall P s.

    Lemma forall_def :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall p : A -> Prop,
      forall s : sequence A,
        (_forall p s <-> forall x : A, (mem x s -> p x)).
    Proof.
      intros A Ih p s.
      unfold mem, _forall.
      rewrite Forall_eq_forall_mem. tauto.
    Qed.

    Definition _exists {A} `{Inhab A} (P : A -> Prop) (s : sequence A) :=
      Exists P s.

    Lemma _exists_def :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall p : A -> Prop,
      forall s : sequence A,
        (_exists p s <-> Coq.Init.Logic.ex (fun x : A => (mem x s /\ p x))).
    Proof.
      intros A Ih p s.
      unfold _exists, mem.
      rewrite Exists_eq_exists_mem.
      tauto.
    Qed.

    Definition map {A} {B} {Ih:Inhab A} {Ih:Inhab B} := @LibList.map A B.

    Lemma map_elems :
      forall {B : Type},
      forall {A : Type},
      forall {Ih_B : Inhab B},
      forall {Ih_A : Inhab A},
      forall i : Z,
      forall f : B -> A,
      forall s : sequence B,
        (in_range s i -> (seq_get (map f s) i = f (seq_get s i))).
    Proof.
      intros A B IhA IhB i f s [H1 H2].
      unfold seq_get.
      repeat (rewrite If_r; try math).
      unfold map.
      apply LibListZ.read_map. unfold length in *.
      rew_index. split; auto.
    Qed.

    Definition filter {A} {Ih : Inhab A} := @LibList.filter A.

    Lemma filter_elems :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall f : A -> Prop,
      forall s : sequence A,
      forall x : A,
        (mem x s -> (f x -> mem x (filter f s))).
    Proof.
      intros A IhA f s.
      unfold mem in *. unfold multiplicity in *.
      induction s as [|e t IHt]; intros x H1 H2.
      - inversion H1.
      - unfold filter. rew_listx.
        inversion H1; subst; auto.
    Qed.

    Definition filter_map
      {A} {B} {IhA : Inhab A} {IhB : Inhab B}
      (f : A -> option B) (s : sequence A) : sequence B :=
      let g :=
        fun x =>
          match f x with
          |Coq.Init.Datatypes.Some x => x
          |Coq.Init.Datatypes.None => arbitrary end in
      LibList.map g (LibList.filter (fun x => f x <> None) s).

    Lemma filter_map_elems :
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
    Proof.
      intros A B IhA IhB f s y.
      unfold filter_map.
      split; intros H1.
      - destruct H1 as [x [H1 H2]].
        apply mem_map' with x.
        + apply mem_filter; auto.
          rewrite H1. discriminate.
        + rewrite H1. auto.
      - apply LibList.mem_Nth
          with B (LibList.map (*very awkward :|*)
                    (fun x : A =>
                       match f x with
                       | Coq.Init.Datatypes.Some x0 => x0
                       | Coq.Init.Datatypes.None => arbitrary
                       end)
                    (LibList.filter
                       (fun x : A => f x <> None)
                       s)) y in H1.
        destruct H1 as [n H1].
        apply Nth_map_inv in H1.
        destruct H1 as [x [H1 H2]].
        exists x. apply Nth_mem in H2.
        rewrite mem_filter_eq in H2.
        destruct H2 as [H2 H3].
        split; auto.
        destruct (f x).
        + rewrite H1. auto.
        + contradiction.
    Qed.

    Definition get {A} {Ih : Inhab A} := @seq_get A Ih.

    Lemma get_def :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall s : sequence A,
      forall i : Z,
        (get s i = seq_get s i).
    Proof.
      auto.
    Qed.

    Fixpoint set_aux {A} (s : sequence A) (n : nat) (x : A) : sequence A :=
      match s, n with
      |nil, _ => arbitrary
      |_ :: t, O => x :: t
      |e :: t, S n' => e :: set_aux t n' x
      end.

    Definition set {A} {Ih : Inhab A} (s : sequence A) (n : Z) (x : A) : sequence A :=
      If n < 0 then arbitrary else set_aux s (Z.to_nat n) x.

    Lemma set_aux_len :
      forall A `{Inhab A} (s : sequence A) (i : nat) x,
        0 <= i < Z.to_nat (LibListZ.length s) ->
        LibListZ.length (set_aux s i x) =
          LibListZ.length s.
    Proof.
      intros A IhA s.
      induction s as [|h s Ih];
        intros i x H1;
        rew_listx in H1.
      + math.
      + simpl. rew_listx.
        destruct i; rew_listx; auto.
        rewrite Ih; math.
    Qed.

    Lemma set_aux_elem :
      forall A {IhA : Inhab A} s (i : Z) (x : A),
        0 <= i < Z.to_nat (LibListZ.length s) ->
        (set_aux s (to_nat i) x)[i] = x.
    Proof.
      induction s as [|e t Ih]; intros i x [H1 H2].
      - rew_list in H2. math.
      - simpl. remember (to_nat i) as n eqn:E.
        destruct n as [|n'].
        + assert (A1 : i = 0). { math. }
          rewrite A1. rew_listx. auto.
        + assert (A1 : n' = to_nat (i - 1)).
          { math. }
          rewrite read_cons_pos; try math.
          rewrite A1.
          rew_list in H2.
          rewrite Ih.
          * auto.
          * math.
    Qed.

    Lemma set_elem :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall s : sequence A,
      forall i : Z,
      forall x : A,
        (in_range s i -> (seq_get (set s i x) i = x)).
    Proof.
      intros A IHA s i x [H1 H2].
      unfold seq_get in *. unfold length in *.
      unfold set. rewrite If_r; try math.
      apply set_aux_elem.
      split; math.
    Qed.

    Lemma set_aux_elem_other :
      forall A {Ih :Inhab A} s i1 i2 (x : A),
        i1 <> i2 ->
        0 <= i1 < LibListZ.length s ->
        0 <= i2 < LibListZ.length s ->
        (set_aux s (Z.to_nat i1) x)[i2] = s[i2].
    Proof.
      intros A IhA s.
      induction s as [|e s Ih]; intros i1 i2 x H1 H2 H3;
        rew_list in *.
      - math.
      - simpl.
        remember (to_nat i1) as n1 eqn:E1.
        remember (to_nat i2) as n2 eqn:E2.
        destruct n1 as [|n1'].
        + destruct n2 as [|n2'].
          * math.
          * rewrite read_cons_pos; try math.
            rewrite read_cons_pos; try math.
            auto.
        + destruct n2 as [|n2'].
          * assert (A1 : i2 = 0). { math. }
            rewrite A1. rew_list. reflexivity.
          * rewrite read_cons_pos; try math.
            rewrite read_cons_pos; try math.
            assert (A1 : n1' = to_nat (i1 - 1)).
            { math. }
            rewrite A1.
            rewrite Ih; auto; math.
    Qed.

    Lemma set_elem_other :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall s : sequence A,
      forall i1 : Z,
      forall i2 : Z,
      forall x : A,
        (
          (i1 <> i2) -> (
                         in_range s i1 -> (
                                           in_range s i2 -> (seq_get (set s i1 x) i2 = seq_get s i2)
                                         )
                       )
        ).
    Proof.
      unfold in_range.
      intros A IhA s i1 i2 x H1 H2 H3.
      unfold length in *.
      unfold seq_get. unfold set. repeat (rewrite If_r; try math).
      apply set_aux_elem_other; math.
    Qed.

    Definition rev {A} {Ih : Inhab A} := @LibList.rev A .

    Lemma rev_length :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall s : sequence A,
        (length s = length (rev s)).
    Proof.
      intros A Ih s. unfold length. unfold rev. rew_list. auto.
    Qed.

    Lemma bah :
      forall A `{Inhab A} (s : sequence A) i,
        0 <= i < LibListZ.length s ->
        s[i] = LibList.nth (abs i) s.
    Proof.
      intros A IhA s i H1.
      remember (abs i) as n eqn:E.
      generalize dependent i.
      generalize dependent s.
      induction n as [|n' Ih]; intros s i H1 H2.
      + assert (A1 : i = 0). { math. } rewrite A1.
        destruct s.
        * rew_list in H1. math.
        * rew_list. rew_listx. auto.
      + destruct s; rew_list in H1.
        * math.
        * rew_listx.
          rewrite read_cons_pos; try math.
          rewrite Ih; auto; math.
    Qed.

    Lemma rev_elems :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall i : Z,
      forall s : sequence A,
        (
          in_range s i -> (
                           seq_get (rev s) i = seq_get s (((length s - (1)%Z) - i))
                         )
        ).
    Proof.
      unfold in_range.
      intros A IhA i s [H1 H2].
      unfold_all.
      unfold seq_get.
      unfold length in *.
      unfold rev.
      rewrite bah.
      rewrite bah.
      + remember (abs i) as n eqn:E1.
        assert
          (A1 : abs (LibListZ.length s - 1 - i) = (LibList.length s - 1 - n)%nat).
        { math. }
        rewrite A1.
        apply nth_rev. math.
      + math.
      + rew_list. math.
    Qed.

    Lemma extensionality :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall s1 : sequence A,
      forall s2 : sequence A,
        (length s1 = length s2) ->
        (forall i : Z, in_range s1 i -> (seq_get s1 i = seq_get s2 i)) ->
        (s1 = s2).
    Proof.
      unfold in_range.
      intros A IhA s1 s2 H1.
      unfold length in *.
      unfold seq_get in *.
      apply eq_of_extens_range.
      auto.
    Qed.

    Definition fold_left A B {IhA : Inhab A} {IhB : Inhab B} (f : A -> B -> A) (x : A) (s : sequence B) : A  :=
      LibList.fold_left (fun x y => f y x) x s.


    Lemma fold_left_empty :
      forall {B : Type},
      forall {A : Type},
      forall {Ih_B : Inhab B},
      forall {Ih_A : Inhab A},
      forall f : A -> B -> A,
      forall acc : A,
        (fold_left f acc empty = acc).
    Proof.
      intros A1 A2 Ih1 Ih2 f acc.
      unfold fold_left.
      rew_list.
      auto.
    Qed.

    Lemma fold_left_cons :
      forall {B : Type},
      forall {A : Type},
      forall {Ih_B : Inhab B},
      forall {Ih_A : Inhab A},
      forall f : A -> B -> A,
      forall acc : A,
      forall x : B,
      forall l : sequence B,
        (fold_left f acc (cons x l) = fold_left f (f acc x) l).
    Proof.
      intros A B IhA IhB f acc x l.
      unfold fold_left, cons.
      rew_listx.
      auto.
    Qed.

    Definition fold_right
      {A} {B} `{Inhab A} `{Inhab B}
      (f : A -> B -> B) s acc :=
      LibList.fold_right f acc s.

    Lemma fold_right_empty :
      forall {B : Type},
      forall {A : Type},
      forall {Ih_B : Inhab B},
      forall {Ih_A : Inhab A},
      forall acc : A,
      forall f : B -> A -> A,
        (fold_right f empty acc = acc).
    Proof.
      intros A B IhA IhB acc f.
      unfold fold_right.
      unfold empty.
      rew_list.
      auto.
    Qed.

    Lemma fold_right_cons :
      forall {B : Type},
      forall {A : Type},
      forall {Ih_B : Inhab B},
      forall {Ih_A : Inhab A},
      forall acc : A,
      forall f : B -> A -> A,
      forall x : B,
      forall l : sequence B,
        (fold_right f (cons x l) acc = f x (fold_right f l acc)).
    Proof.
      intros A B IhA IhB acc f x l.
      unfold fold_right, cons.
      rew_listx.
      auto.
    Qed.

    Definition permut {A} `{Inhab A} (s1 : sequence A) (s2 : sequence A) :=
      (forall x : A, Coq.Init.Logic.iff (mem x s1) (mem x s2)).

    Lemma permut_mem :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall s1 : sequence A,
      forall s2 : sequence A,
        permut s1 s2 -> (forall x : A, (mem x s1 <-> mem x s2)).
    Proof.
      tauto.
    Qed.

    Definition permut_sub {A} `{Inhab A}
      (s1 : sequence A) (s2 : sequence A) (i : Z) (j : Z) :=
      permut (seq_sub s1 i j) (seq_sub s2 i j) /\
        eq (seq_sub_r s1 i) (seq_sub_r s2 i) /\
        eq (seq_sub_l s1 j) (seq_sub_l s2 j).

    Lemma permut_sub_def :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall s1 : sequence A,
      forall s2 : sequence A,
      forall i : Z,
      forall j : Z,
        permut (seq_sub s1 i j) (seq_sub s2 i j) ->
        (seq_sub_r s1 i = seq_sub_r s2 i) ->
        (seq_sub_l s1 j = seq_sub_l s2 j) -> permut_sub s1 s2 i j.
    Proof.
      unfold permut_sub. tauto.
    Qed.

  End Sequence.

  Module Bag.

    Definition t  (A : Type) : Type:= bag A.

    Definition multiplicity {A} `{Inhab A} (x : A) (b : bag A) : Z :=
      b x.

    Lemma well_formed :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall b : bag A,
      forall x : A,
        (multiplicity x b >= (0)%Z).
    Proof.
      intros A Ih b x.
      unfold_all.
      unfold multiplicity.
      math.
    Qed.

    Definition empty {A} {aIh : Inhab A} := fun (_ : A) => 0%nat.

    Lemma empty_mult :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall x : A,
        (multiplicity x empty = (0)%Z).
    Proof.
      auto.
    Qed.

    Definition init {A} `{Inhab A} (f : A -> Z) : bag A :=
      fun x => Z.to_nat(f x).

    Lemma init_axiom :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall f : A -> Z,
      forall x : A,
        (max (0)%Z (f x) = multiplicity x (init f)).
    Proof.
      unfold_all.
      unfold multiplicity, init.
      math.
    Qed.

    Definition mem  (a : Type) { aIh : Inhab a } (x : a) (b : bag a) : Prop:=
      gt (multiplicity x b) (0)%Z.

    Lemma mem_def :
      forall {a251 : Type},
      forall {Ih_a251 : Inhab a251},
      forall x : a251,
      forall b : bag a251,
        Coq.Init.Logic.iff (mem x b) (gt (multiplicity x b) (0)%Z).
    Proof.
      tauto.
    Qed.

    Definition add {A} `{Inhab A} (x : A) b : bag A :=
      fun y => If y = x then (1 + b y)%nat else b y.

    Lemma add_mult_x :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall b : bag A,
      forall x : A,
        (multiplicity x (add x b) = ((1)%Z + multiplicity x b)).
    Proof.
      intros A IhA b x.
      unfold_all.
      unfold multiplicity, add.
      rewrite If_l; auto.
      math.
    Qed.

    Lemma add_mult_neg_x :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall x : A,
      forall y : A,
      forall b : bag A,
        (x <> y) -> (multiplicity y (add x b) = multiplicity y b).
    Proof.
      intros A IhA x y b H1.
      unfold multiplicity, add.
      rewrite If_r; auto.
    Qed.

    Definition singleton  (a : Type) { aIh : Inhab a } (x : a) : bag a:=
      add x (@empty a aIh).

    Lemma singleton_def :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall x : A,
        (singleton x = add x empty).
    Proof.
      auto.
    Qed.

    Definition remove {A} `{Inhab A} (x : A) b : bag A :=
      fun y => If y = x then Nat.pred (b y) else b y.

    Lemma remove_mult_x :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall b : bag A,
      forall x : A,
        (multiplicity x (remove x b) = max (0)%Z ((multiplicity x b - (1)%Z))).
    Proof.
      intros A IhA b x.
      unfold_all.
      unfold multiplicity, remove.
      rewrite If_l; auto.
      math.
    Qed.

    Lemma remove_mult_neg_x :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall x : A,
      forall y : A,
      forall b : bag A,
        (x <> y) -> (multiplicity y (remove x b) = multiplicity y b).
    Proof.
      intros A IhA x y b H1.
      unfold multiplicity, remove.
      rewrite If_r; auto.
    Qed.

    Definition union {A} `{Inhab A} (b1 : bag A) b2 :=
      fun x => Nat.max (b1 x) (b2 x).

    Lemma union_all :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall b : bag A,
      forall b' : bag A,
      forall x : A,
        (
          max (multiplicity x b) (multiplicity x b') = multiplicity x (union b b')
        ).
    Proof.
      unfold_all.
      unfold union, multiplicity.
      math.
    Qed.

    Definition sum {A} `{Inhab A} (b1 : bag A) b2 :=
      fun x => (b1 x + b2 x)%nat.

    Lemma sum_all :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall b : bag A,
      forall b' : bag A,
      forall x : A,
        ((multiplicity x b + multiplicity x b') = multiplicity x (sum b b')).
    Proof.
      unfold plus, multiplicity, sum.
      math.
    Qed.

    Definition inter {A} `{Inhab A} (b1 : bag A) b2 :=
      fun x => Nat.min (b1 x) (b2 x).

    Lemma inter_all :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall b : bag A,
      forall b' : bag A,
      forall x : A,
        (
          min (multiplicity x b) (multiplicity x b') = multiplicity x (inter b b')
        ).
    Proof.
      unfold min, multiplicity, inter.
      math.
    Qed.

    Definition disjoint  (a : Type) { aIh : Inhab a } (b : bag a) (
        b' : bag a
      ) : Prop:=
      forall x : a,
        mem x b -> Coq.Init.Logic.not (mem x b').

    Lemma disjoint_def :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall b : bag A,
      forall b' : bag A,
        (disjoint b b' <-> forall x : A, mem x b -> not (mem x b')).
    Proof.
      tauto.
    Qed.

    Definition diff {A} `{Inhab A} (b1 : bag A) b2 :=
      fun x => (b1 x - b2 x)%nat.

    Lemma diff_all :
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
    Proof.
      unfold multiplicity, max, minus, diff.
      math.
    Qed.

    Definition subset  (a : Type) { aIh : Inhab a } (b : bag a) (b' : bag a) : Prop:=
      forall x : a,
        le (multiplicity x b) (multiplicity x b').


    Lemma subset_def :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall b : bag A,
      forall b' : bag A,
        (subset b b' <-> forall x : A, (multiplicity x b <= multiplicity x b')).
    Proof.
      tauto.
    Qed.

    Definition filter {A} `{Inhab A} p (b : bag A) :=
      fun x => If p x then b x else 0%nat.

    Lemma filter_mem :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall b : bag A,
      forall x : A,
      forall f : A -> Prop,
        f x -> (multiplicity x (filter f b) = multiplicity x b).
    Proof.
      intros A IhA b x f H1.
      unfold multiplicity, filter.
      rewrite If_l; auto.
    Qed.

    Lemma filter_mem_neg :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall b : bag A,
      forall x : A,
      forall f : A -> Prop,
        not (f x) -> (multiplicity x (filter f b) = (0)%Z).
    Proof.
      intros A Ih b x f H1.
      unfold multiplicity, filter.
      rewrite If_r; auto.
    Qed.

    Definition cover {A} (b : bag A) l :=
      forall x, b x = LibList.count (fun y => y = x) l.

    Import LibEpsilon.

    Definition cardinal {A} `{Inhab A} (b : bag A) : Z :=
      epsilon (fun n : nat => exists l, cover b l /\ n = LibList.length l).

    Definition finite  (A : Type) { aIh : Inhab A } (b : bag A) : Prop:=
      exists l, forall x,
        mem x b -> Sequence.mem x l.


    Lemma finite_def :
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
    Proof.
      tauto.
    Qed.

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

  Definition set_create {A} {Ih : Inhab A} := fun (_:A) => False.

  Module _Set.
    Definition t := set.

    Import TLC.LibSet.

    Definition mem {A} {Ih : Inhab A} (x : A) (s : set A) : Prop := is_in x s.
    Definition empty {A} {Ih : Inhab A} : set A := empty.
    Lemma empty_mem :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall x : A,
        not (mem x empty).
      intros. unfold empty. auto.
    Qed.

    Definition add {A} {Ih : Inhab A} (x : A) (s : set A) : set A := s \u (single x).
    Lemma add_mem :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall s : set A,
      forall x : A,
        mem x (add x s).
      intros. unfold mem. unfold add. rewrite set_in_union_eq.
      right. rewrite in_single_eq. auto.
    Qed.

    Lemma add_mem_neq :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall s : set A,
      forall x : A,
      forall y : A,
        (x <> y) -> (mem x s <-> mem x (add y s)).
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
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall s : set A,
      forall x : A,
        not (mem x (remove x s)).
    Proof.
      intros A Ih s x.
      unfold remove, mem, singleton, empty, add.
      rewrite set_in_remove_eq.
      unfold not. intros [H1 H2].
      destruct H2. rewrite set_in_single_eq. auto.
    Qed.

    Lemma remove_mem_neq :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall s : set A,
      forall x : A,
      forall y : A,
        (x <> y) -> (mem x s <-> mem x (remove y s)).
    Proof.
      intros A Ih s x y Neq. split; intro H;
        unfold mem, remove, singleton, add, empty in *;
        rewrite set_in_remove_eq in *.
      split. auto. unfold not. intros H1. contradiction.
      - destruct H. auto.
    Qed.

    Definition union {A} {Ih : Inhab A} (s1 : set A) (s2 : set A) : set A :=
      s1 \u s2.

    Lemma union_mem :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall s : set A,
      forall s' : set A,
      forall x : A,
        (mem x s \/ mem x s') -> mem x (union s s').
    Proof.
      intros A Ih s s' x [H | H]; unfold mem, union in *;
        rewrite set_in_union_eq; [left | right]; auto.
    Qed.

    Lemma union_mem_neg :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall s : set A,
      forall s' : set A,
      forall x : A,
        not (mem x s) -> not (mem x s') -> not (mem x (union s s')).
    Proof.
      intros A Ih s s' x H1 H2.
      unfold mem, union in *.
      unfold not. intros H3.
      rewrite set_in_union_eq in H3.
      destruct H3 as [H3 | H3]; contradiction.
    Qed.

    Definition inter {A} {Ih : Inhab A} (s1 : set A) (s2 : set A) : set A := s1 \n s2.

    Lemma inter_mem :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall s : set A,
      forall s' : set A,
      forall x : A,
        mem x s -> mem x s' -> mem x (inter s s').
    Proof.
      intros A Ih s s' x H1 H2.
      unfold mem, inter in *.
      rewrite set_in_inter_eq. split; auto.
    Qed.

    Lemma inter_mem_neq :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall s : set A,
      forall s' : set A,
      forall x : A,
        not ((mem x s \/ mem x s')) -> not (mem x (inter s s')).
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

    Lemma disjoint_def :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall s : set A,
      forall s' : set A,
        (disjoint s s' <-> (inter s s' = empty)).
    Proof.
      tauto.
    Qed.

    Definition diff {A} {Ih : Inhab A} (s1 : set A) (s2 : set A) : set A :=
      LibContainer.remove s1 s2.

    Lemma diff_mem :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall s : set A,
      forall s' : set A,
      forall x : A,
        mem x s' -> not (mem x (diff s s')).
    Proof.
      intros A Ih s s' x H1.
      unfold mem, diff in *.
      rewrite set_in_remove_eq. unfold not.
      intros [H2 H3]. contradiction.
    Qed.

    Lemma diff_mem_fst :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall s : set A,
      forall s' : set A,
      forall x : A,
        not (mem x s') -> (mem x s <-> mem x (diff s s')).
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

    Lemma subset_def :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall s : set A,
      forall s' : set A,
        (subset s s' <-> forall x : A, mem x s -> mem x s').
    Proof.
      tauto.
    Qed.

    Definition map {A} {B} {Iha : Inhab A} {Ihb : Inhab B} (f : A -> B) (s : set A) : set B :=
      fun (x : B) => exists (y : A), f y = x /\ (y \in s).

    Lemma set_map :
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
    Proof.
      intros A IhA B IhB f s x.
      unfold mem, map in *. split; auto.
    Qed.

    Definition partition {A} `{Inhab A} p (s : set A) :=
      (set_st (fun x => p x /\ x \in s),
        set_st (fun x => ~p x /\ x \in s)).

    Lemma partition_l_mem :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall f : A -> Prop,
      forall s : set A,
      forall x : A,
      forall p1 : set A,
      forall p2 : set A,
        mem x s -> f x -> (partition f s = (p1, p2)) -> mem x p1.
    Proof.
      unfold mem, partition.
      intros A IhA f s x p1 p2 H1 H2 H3.
      injection H3.
      intros H4 H5.
      rewrite <- H5.
      rew_set.
      auto.
    Qed.

    Lemma partition_r_mem :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall f : A -> Prop,
      forall s : set A,
      forall x : A,
      forall p1 : set A,
      forall p2 : set A,
        mem x s -> not (f x) -> (partition f s = (p1, p2)) -> mem x p2.
    Proof.
      intros A IhA f s x p1 p2 H1 H2 H3.
      injection H3.
      intros H4 H5.
      rewrite <- H4.
      unfold mem.
      rew_set.
      auto.
    Qed.

    Definition cardinal {A} {Ih : Inhab A} (s : set A) : Z := Z.of_nat (card s).

    Definition finite  (a : Type) { aIh : Inhab a } (s : set a) : Prop :=
      LibSet.finite s.

    Lemma finite_def :
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
    Proof.
      tauto.
    Qed.

    Lemma cardinal_nonneg :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall s : set A,
        (cardinal s >= (0)%Z).
    Proof.
      intros A Ih s.
      unfold cardinal.
      math.
    Qed.

    Lemma cardinal_empty :
      forall {A : Type},
      forall {Ih_A : Inhab A},
        (@cardinal A Ih_A empty = (0)%Z).
    Proof.
      intros A IhA.
      unfold cardinal, empty.
      rewrite <- Nat2Z.inj_0.
      f_equal.
      apply card_empty.
    Qed.

    Lemma cardinal_remove :
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
    Proof.
      intros A Ih s x H.
      unfold mem, cardinal, minus, remove, singleton, empty, add.
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
    Proof.
      intros A Ih s x H.
      unfold plus, cardinal, add in *.
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

    Lemma of_seq_mem :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall s : sequence A,
      forall x : A,
        (mem x (of_seq s) <-> Sequence.mem x s).
    Proof.
      intros A Ih x s.
      unfold mem.
      unfold of_seq.
      split; intros H; auto.
    Qed.

    Definition to_seq {A} `{Inhab A} (s : set A) : sequence A :=
      LibSet.to_list s.

    Lemma count_no_dup :
      forall A (x : A) l,
        noduplicates l ->
        count (=x) l = 1 <-> LibList.mem x l.
    Proof.
      intros A x l H1.
      split; intros H2.
      - assert (A1 : count (=x) l > 0). { math. }
        apply exists_mem_of_count_pos in A1.
        destruct A1 as [y [H3 H4]]. subst. assumption.
      - induction H1 as [|h l Ih1 Ih2 Ih3].
        + inversion H2.
        + rew_listx in *.
          destruct H2 as [H2 | H2].
          * symmetry in H2. subst. rewrite If_l; auto.
            assert (A2 : ~ count (=x) l > 0).
            { intros H2. rewrite <- Exists_eq_count_pos in H2.
              rewrite Exists_eq_exists_mem in H2.
              destruct H2 as [y [H2 H3]]. subst. contradiction.
            }
            assert (A3 : ~ count (=x) l < 0).
            { unfold count. math. }
            math.
          * rewrite If_r.
            { rewrite Ih3. lia. assumption. }
            { intros H4. subst. contradiction. }
    Qed.

    Lemma to_seq_mem :
      forall {A : Type},
      forall {Ih_A : Inhab A},
      forall s : set A,
        finite s ->
        (
          forall x : A,
            (mem x s <-> (Sequence.multiplicity x (to_seq s) = (1)%Z))
        ).
    Proof.
      intros A Ih s F x.
      unfold to_seq, mem, Sequence.multiplicity, finite in *.
      remember (to_list s) as l eqn:E.
      apply eq_to_list_inv in E; auto.
      unfold list_repr in E.
      destruct E as [E1 E2].
      symmetry.
      rewrite count_no_dup; auto.
    Qed.

    Import LibMonoid.
    Definition fold {A} {B} `{Inhab A} `{Inhab B} (f : A -> B)
      (m : B -> B -> B) (s : set A) (acc : B) : B :=
      let monoid :=
        {|
          monoid_oper := m;
          monoid_neutral := acc;
        |} in
      LibContainer.fold monoid f s.

    Lemma fold_def :
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
    Proof.
      unfold comm_monoid. unfold monoid.
      intros A B IhA IhB f m s acc F [[H1 [H2 H3]] H4].
      unfold fold. unfold Sequence.fold_right.
      remember ({|
                   monoid_oper := m;
                   monoid_neutral := acc
                 |}) as op eqn:E.
      rewrite fold_eq_fold_list_repr with
        (A:=A) (B:=B) (m:=op) (f:=f) (E:=s) (L:=to_seq s).
      - induction (to_seq s) as [|h t Ih].
        + rew_listx. subst. auto.
        + rew_listx. rewrite Ih.
          subst. auto.
      - repeat split; rewrite E; auto.
      - unfold to_seq. apply list_repr_to_list_of_finite. auto.
    Qed.

  End _Set.

  Definition map_set (A : Type) (B : Type) {Ih : Inhab A} {Ih : Inhab B} (f : A -> B) (x : A) (y : B) : A -> B:=
    fun arg : A =>
      If (Coq.Init.Logic.eq arg x) then y else f x.

  Lemma map_set_def :
    forall {a : Type},
    forall {b : Type},
    forall {Ih_a : Inhab a},
    forall {Ih_b : Inhab b},
    forall f : a -> b,
    forall x : a,
    forall y : b,
      eq (map_set f x y) (
          fun arg : a =>
            if classicT (eq arg x) then y else f x
        ).
  Proof.
    tauto.
  Qed.

  Module Map.

    Definition t  (A : Type) (B : Type) : Type:= map A B.

    Definition domain :
      forall {a : Type},
      forall {b : Type},
      forall {_Ga : Inhab a},
      forall {_Gb : Inhab b},
        b -> (a -> b) -> set a.
    Proof.
      refine
        (fun A B G1 G2 d m =>
           set_st (fun x => m x <> d)
        ).
    Defined.

    Lemma domain_mem :
      forall {B : Type},
      forall {A : Type},
      forall {Ih_B : Inhab B},
      forall {Ih_A : Inhab A},
      forall x : A,
      forall m : A -> B,
      forall default : B,
        (m x <> default) -> _Set.mem x (domain default m).
    Proof.
      intros A B G1 G2 x m d H1.
      unfold _Set.mem.
      unfold domain.
      rewrite in_set_st_eq.
      auto.
    Qed.
  End Map.

End Gospelstdlib.
