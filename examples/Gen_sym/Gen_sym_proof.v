Set Implicit Arguments.
From CFML Require Import WPLib.
From CFML Require Import Stdlib.
From TLC Require Import LibListZ.

From EXAMPLES Require Import Gen_sym_ml.

Require Import Gospelstdlib_verified.

Import Gospelstdlib.

Definition __ocaml_name := Z.
Definition name := Z.

Instance __Inhab_name : Inhab __ocaml_name := Inhab_int.

Instance __Enc_name : Enc __ocaml_name := Enc_int.

Definition Name (y : name) (x : val) : hprop := \[x = y].

Definition Gen (s : _Set.t name) (l : loc) : hprop :=
  \exists n,
    l ~~> n \*
      \[n >= 0] \*
      \[forall m, 0 < m <= n -> _Set.mem m s] \*
      \[forall m, m <= 0 \/ m > n -> ~ (_Set.mem m s)].

(* Definition Gen' s (v : val) := exists l, v = VLoc l /\ Gen s l. *)

Definition _create : val := create.

Lemma initial_spec : initial = 0.
Proof. xcf. Qed.

Lemma _create_spec :
  SPEC(_create v)
  PRE\[]
  POST(fun _prog_g : loc => (_prog_g ~> Gen _Set.empty)).
Proof using.
  unfold _create.
  xcf. xapp*.
  xunfold Gen. xsimpl; intros.
  1, 2: rewrite initial_spec in *; math.
  apply _Set.empty_mem.
Qed.

Definition _next : val := next.

Definition _next_spec :
  forall _prog_g : loc,
  forall g : _Set.t name,
  SPEC(_next _prog_g)
  PRE((_prog_g ~> Gen g))
  POST(
    fun _prog_n : name =>
    \exists n : name,
    ((_prog_g ~> Gen (_Set.add n g)) \* (_prog_n ~> Name n))
  ).
Proof using.
  unfold _next.
  xcf. xunfold Gen. xpull. intros x H1 H2 H3.
  xapp. xapp. xapp. xif. intros; math.
  intros H4. xval. xapp. xsimpl.
  Unshelve. 5: apply (x + 1).

  - math.
  - intros m H5.
    assert (A : m = x + 1 \/ m <> x + 1).
    { apply classic. }
    destruct A.
    + subst. apply _Set.add_mem.
    + apply _Set.add_mem_neq.
      auto. apply H2. math.
  - intros m H5. destruct H5;
    rewrite <- _Set.add_mem_neq.
    + auto.
    + math.
    + apply H3. right. math.
    + math.
  - xunfold Name. xsimpl. auto.
Qed.

Definition _reset : val := reset.

Lemma _reset_spec :
  forall _prog_g : loc,
  forall g : _Set.t name,
  SPEC(_reset _prog_g)
  PRE((_prog_g ~> Gen g))
  POST(fun _ : unit => (_prog_g ~> Gen _Set.empty)).
Proof.
  unfold _reset. xcf.
  xunfold Gen. xpull. intros x H1 H2 H3.
  xapp. xsimpl.
  2, 3: intros m H4.
  1, 2: rewrite initial_spec in *; math.
  apply _Set.empty_mem.
Qed.
