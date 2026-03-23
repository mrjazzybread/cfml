From EXAMPLES Require Import Transfer_ml.

Set Implicit Arguments.
From CFML Require Import WPLib.
From CFML Require Import Stdlib.
From TLC Require Import LibListZ.

From EXAMPLES Require Import Gen_sym_ml.

Lemma transfer_spec :
  forall (r1 : loc) (r2 : loc) (n1 : nat) (n2 : nat),
  SPEC(transfer r1 r2)
  PRE(r1 ~~> n1 \* r2 ~~> n2)
  POSTUNIT(r1 ~~> n2 \* r2 ~~> n2).
Proof.
  xcf. repeat xapp. xsimpl.
Qed.
