Set Implicit Arguments.

From EXAMPLES Require Import Append_ml.

From CFML Require Import WPLib.
From CFML Require Import Stdlib.
From TLC Require Import LibListZ.

Fixpoint MList A (L:list A) (p:loc) : hprop :=
  \exists (v : contents_ A), p ~~> v \* match L with
  | nil => \[v = Nil]
  | x::L' => \exists p', \[v = Cons x p'] \* (p' ~> MList L')
  end.

Definition MList_contents A (v:contents_ A) (L:list A) : hprop :=
  match L with
  | nil => \[v = Nil]
  | x::L' => \exists p', \[v = Cons x p'] \* (p' ~> MList L')
  end.

Lemma MList_contents_iff : forall A  v (L:list A),
  (MList_contents v L) ==> (MList_contents v L) \* \[v = Nil <-> L = nil].
Proof using.
  intros. unfold MList_contents. destruct L; xsimpl; auto_false.
Qed.

Lemma MList_contents_cons : forall A x t (L: list A),
 (MList_contents (Cons x t) L) ==>
   \exists xs, \[L = x :: xs] \* t ~> MList xs.
Proof using.
  intros. xunfold MList_contents. destruct L;
  xsimpl; intros l H; injection H; intros; subst; auto.
  Unshelve. apply (@nil A).
Qed.

Lemma MList_cons : forall A (p : loc) p' (L : list A) x,
  p ~~> Cons x p' \* (p' ~> MList L) ==> p ~> MList (x :: L).
Proof.
  intros. xunfold MList. xsimpl; intros; eauto.
Qed.

Lemma MList_eq : forall (p:loc) A (L:list A),
  p ~> MList L = (\exists (v:contents_ A), p ~~> v \* MList_contents v L).
Proof using. intros. destruct L; auto. Qed.

Lemma append_spec :
    forall {A} `{Enc A} (L1 : list A) (L2 : list A) (p1 : loc) (p2 : loc),
    SPEC (Append_ml.append p1 p2)
    PRE (p1 ~> MList L1 \* p2 ~> MList L2)
    POSTUNIT (p1 ~> MList (L1 ++ L2)).
Proof using.
  intros A E L1. induction_wf IH: list_sub L1.
  intros L2 p1 p2.
  xcf. xchange (MList_eq p1) ;=> v1.
  xapp. xmatch.
  + xchange MList_eq ;=> v2. xapp. xapp.
    xchange (@MList_contents_iff A) ;=> [H1 H2].
    rewrite H1. 2: auto.
    rew_list. xchanges <- MList_eq p1.
    apply haffine_hpure.
  + xchanges MList_contents_cons.
    intros L1' H1. subst.
    xapp. 1: constructor.
    rew_list. xchange MList_cons.
    xsimpl.
Qed.
