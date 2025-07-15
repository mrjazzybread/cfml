From iris.algebra Require Import frac gmap auth.
From iris.base_logic Require Export invariants.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import par.
From iris.base_logic Require Import cancelable_invariants.
From iris.prelude Require Import options.
Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.Int.
From stdpp Require Import coGset.
From stdpp Require Import numbers.

Local Open Scope Z_scope.

Section spec.

Context `{!heapGS Σ}.
Notation iProp := (iProp Σ).
Implicit Types ℓ : loc.

Definition initial : val := #0.

Definition create : val :=
  λ: <>, ref initial.

Definition next : val :=
  λ:"x",
  ("x" <- !"x" + #1);;
  !"x".

Definition reset : val :=
  λ: <>, "x" <- #0.

Definition Gen' (v : val) (s : coGset Z) : Prop :=
  exists (n : Z),
    v = #n
    /\ n >= 0
    /\ (forall m, 0 < m <= n -> m ∈ s)
    /\ (forall m, m <= 0 \/ m > n -> m ∉ s).

Definition Gen (r : val) (s : coGset Z) : iProp :=
  ∃ (ℓ : loc) (v : val), ℓ ↦ v ∗ ⌜Gen' v s⌝ ∗ ⌜r = #ℓ⌝.

Lemma create_spec :
  {{{ True }}}
    create #()
  {{{ g, RET g; inv nroot (Gen g ∅)}}}.
Proof.
  iIntros (ϕ) "_ HΦ".
  wp_lam.
  wp_alloc l as "Hpt".
  iApply "HΦ".
  iMod (inv_alloc nroot _ (Gen #l ∅) with "[Hpt]")
    as "#I".
  {  iNext.
     iExists l, initial.
     iFrame.
     iUnfold Gen'.
     iSplit; try done.
     iExists 0. unfold initial. repeat iSplit; try done.
     iIntros (m H). lia. }
  done.
Qed.

Lemma next_spec :
  forall r g,
  {{{ Gen r g }}}
    next r
  {{{ v, RET v; ∃ x : Z, ⌜v = #x⌝ ∗ Gen r (g ∪ {[x]})}}}.
Proof.
  intros r g.
  iIntros (Q) "Gen Q".
  iDestruct "Gen" as (l v) "[H1 [H2 H3]]".
  iDestruct "H3" as "%Heq".
  rewrite Heq.
  wp_lam.
  wp_load.
  iUnfold Gen' in "H2".
  iDestruct "H2" as (n) "[H4 [H5 H6]]".
  iDestruct "H4" as "%Heq'".
  rewrite Heq'.
  wp_op.
  wp_store.
  wp_load.
  iApply "Q".
  iExists (n + 1).
  iFrame.
  iModIntro.
  repeat iSplit; try done.
  iExists (n+1).
  iDestruct "H5" as "%H1".
  iDestruct "H6" as "[%H2 %H3]".
  iPureIntro.
  repeat split; auto.
  - lia.
  - intros m H4.
    destruct H4 as [H5 H6].
    apply Zle_lt_or_eq in H6.
    destruct H6 as [H6 | H6].
    + apply elem_of_union_l.
      apply H2.
      lia.
    + set_solver.
  - intros m H4.
    apply not_elem_of_union.
    split.
    1: apply H3.
    2: apply not_elem_of_singleton.
    all: lia.
Qed.
End.
