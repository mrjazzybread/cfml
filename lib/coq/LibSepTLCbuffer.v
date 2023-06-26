(**

This file contains temporary definitions that will eventually
get merged into the various files from the TLC library.

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)


Set Implicit Arguments.
(*
From TLC Require Import LibTactics LibLogic LibList.
From TLC Require Import LibReflect.
From TLC Require LibListZ LibWf LibMultiset LibInt.
*)
From TLC Require Import LibTactics LibReflect.
From TLC Require Import LibInt.
Generalizable Variables A B.

Global Opaque Z.mul.
Global Opaque Z.add.



(*--------------------------------------------------------*)
(* LibRational *)

From Coq.QArith Require QArith_base.
From Coq Require Import Qcanon.

Definition Z2Qc (n:Z) : Qc :=
  Q2Qc (QArith_base.inject_Z n).

Lemma add_Z2Qc : forall n m,
  ((Z2Qc n) + (Z2Qc m))%Qc = (Z2Qc (n + m)%Z).
Proof. skip. (* TODO *) Qed.

Lemma sub_Z2Qc : forall n m,
  ((Z2Qc n) - (Z2Qc m))%Qc = (Z2Qc (n - m)%Z).
Proof. skip. (* TODO *) Qed.

Lemma neg_Z2Qc : forall n,
  (- (Z2Qc n))%Qc = (Z2Qc (- n)%Z).
Proof. skip. (* TODO *) Qed.

Lemma Qc_add_zero_l : forall (p:Qc),
  (0 + p)%Qc = p.
Proof. skip. (* TODO *) Qed.

Lemma Qc_add_zero_r : forall (p:Qc),
  (p + 0)%Qc = p.
Proof. skip. (* TODO *) Qed.

Hint Rewrite add_Z2Qc sub_Z2Qc neg_Z2Qc Qc_add_zero_l Qc_add_zero_r : rew_qc.

Tactic Notation "rew_qc" :=
  autorewrite with rew_qc.
Tactic Notation "rew_qc" "in" "*" :=
  autorewrite with rew_qc in *.
Tactic Notation "rew_qc" "in" hyp(H) :=
  autorewrite with rew_qc in H.

Tactic Notation "rew_qc" "~" :=
  rew_qc; auto_tilde.
Tactic Notation "rew_qc" "~" "in" "*" :=
  rew_qc in *; auto_tilde.
Tactic Notation "rew_qc" "~" "in" hyp(H) :=
  rew_qc in H; auto_tilde.

Tactic Notation "rew_qc" "*" :=
  rew_qc; auto_star.
Tactic Notation "rew_qc" "*" "in" "*" :=
  rew_qc in *; auto_star.
Tactic Notation "rew_qc" "*" "in" hyp(H) :=
  rew_qc in H; auto_star.



(*--------------------------------------------------------*)
(* LibListZ *)

From TLC Require Import LibListZ.

(* Hint *)

Hint Extern 1 (@index _ _ _ _ _) => rew_array; math.

(* A tactic to rewrite lists with reads
  ---- subsumed by a more powerful version implemented in the cfml-sek package *)

Hint Rewrite read_cons_case read_update_case : rew_list_cases.
Tactic Notation "rew_list_cases" :=
  autorewrite with rew_list_cases.
Tactic Notation "rew_list_cases" "*" := rew_list_cases; auto_star.

Tactic Notation "rew_list_cases" "in" "*"  :=
  (* TODO: why not? autorewrite_in_star_patch ltac:(fun tt => autorewrite with rew_list). *)
  autorewrite with rew_list_cases in *.
Tactic Notation "rew_list_cases" "*" "in" "*"  := rew_list_cases in *; auto_star.

Ltac list_cases_post tt :=
  repeat case_if; try math.

Tactic Notation "list_cases" :=
  rew_list_cases; list_cases_post tt.
Tactic Notation "list_cases" "*"  :=
  list_cases; auto_star.

Tactic Notation "list_cases" "in" "*"  :=
  rew_list_cases in *; list_cases_post tt.
Tactic Notation "list_cases" "*" "in" "*"  :=
  list_cases in *; auto_star.


(* TODO Move to TLC *)
Lemma list_same_length_inv_nil : forall A1 A2 (l1:list A1) (l2:list A2),
  length l1 = length l2 ->
  l1 = nil <-> l2 = nil.
Proof using. intros. destruct l1; destruct l2; auto_false*. Qed.

(*--------------------------------------------------------*)
(* LibLtac *)

Ltac fold_right f accu l :=
  match l with
  | nil => accu
  | ?a::?L =>
    let naccu := fold_right f accu l in
    f a naccu
  end.

Ltac fold_left f accu l :=
  match l with
  | nil => accu
  | ?a::?L =>
    let naccu := f accu a in
    fold_left f naccu L
  end.

Ltac list_rev A l :=
  let cons' x y := constr:(y::x) in
  fold_left cons' (@nil A) l.

Ltac list_snoc x l :=
  let cons x y := constr:(x::y) in
  fold_right cons x l.
