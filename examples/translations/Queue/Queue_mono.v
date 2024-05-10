Set Implicit Arguments.
From CFML Require Import WPLib.
From CFML Require Import Stdlib.
From EXAMPLES Require Import MList_ml Queue_ml.
From EXAMPLES Require Import MList_proof.
From TLC Require Import LibListZ.
Import SpecMList.

Definition MQueue (L: list int) (q: loc) : hprop :=
  \exists (f r: loc) L1 L2, (q ~~~> `{ front' := f; rear' := r; size' := length L }) \*
                         (f ~> MList L1) \* (r ~> MList L2) \*
                         \[L1 = nil -> L2 = nil] \* \[L = L1 ++ rev L2].

Section Ops.

Implicit Types L : list int.

Lemma nil_rev_nil :
    (@nil int) = (@nil int) ++ rev (@nil int).
Proof using. auto. Qed.

Lemma Triple_queue_is_empty : forall L q,
    SPEC (is_empty q)
      PRE (MQueue L q)
      POST (fun b => MQueue L q \* \[b = isTrue (L = nil)]).
Proof using.
  xcf. unfold MQueue. xpull*. intros.
  xapp. xvals*. split.
  { apply length_zero_inv. }
  { intros Hnil. rewrite Hnil. auto. }
Qed.

Lemma Triple_push : forall L (x: int) (q: loc),
    SPEC (push x q)
      PRE (MQueue L q)
      POST (fun (_:unit) => MQueue (L & x) q).
Proof using.
  xcf. xapp* Triple_queue_is_empty ;=>.
  destruct L as [|x' L'].
  { rewrite <- LibListExec.is_nil_eq in H.
    simpl in *. subst.
    xif; intros; tryfalse *.
    { xapp. intros.
      xapp. unfold MQueue. xpull* ;=>.
      xapp. xapp. xapp. xsimpl*.
      { auto_false*. }
      { rew_list*. f_equal.
        apply nil_eq_app_inv in H1.
        destruct H1. auto. } } }
  { cuts * G : (~ x' :: L' = nil).
    { apply isTrue_eq_false in G.
      subst. xif; intros; tryfalse *.
      unfold MQueue. xpull ;=>.
      xapp. xapp. xapp. xapp. xsimpl*.
      { rew_list*. math. }
      { intros. assert (x2 = nil) by auto.
        apply H0 in H2. subst.
        rew_list* in *. }
      { rewrite H1. rew_list*. } }
    { auto_false. } }
Qed.

Lemma Triple_pop : forall L q,
    L <> nil ->
    SPEC (pop q)
      PRE (MQueue L q)
      POST (fun x => \exists L', \[L = x :: L'] \* MQueue L' q).
Proof using.
  xcf. unfold MQueue. xpull* ;=>.
  xapp. xchange* (MList_eq x) ;=> f.
  xapp. xmatch.
  { xchange MList_contents_iff ;=>.
    destruct H2. cuts G : (x1 = nil); auto.
    cuts G2 : (x2 = nil); auto. subst.
    rew_list in *. contradiction. }
  { unfold MList_contents. destruct x1; xpull* ;=>.
    inversion H2; subst. xchange* (MList_eq x4) ;=>.
    xchange* <- (MList_eq x4). xapp. xif ;=>.
    { subst. xapp. xapp ;=>. xapp. xapp ;=>.
      xapp. xval. xapp. xapp. xval.
      xsimpl*; rew_list*; try math. }
    { xapp. xchange* <- MList_cons. xapp ;=>.
      { auto_false*. }
      { inversion H3; subst. xapp. xapp. xval.
        xsimpl*; rew_list*; try math. } } }
Qed.

End Ops.
