Set Implicit Arguments.
Require Import Gospel.CFML.base queue_ml queue_mli.

From EXAMPLES Require Primitives.

Local Open Scope comp_scope.

Require Import
  Stdlib.Floats.Floats
  Stdlib.ZArith.BinIntDef
  Stdlib.Strings.Ascii.

From CFML Require Import Stdlib.

From CFML Require Import WPLib.
From CFML Require Import Stdlib.

Module Proofs : Obligations.

  Import Declarations.

  Import queue_ml.

  Definition Cell A `{Enc A} (x : val) (next c : cell_ A) :=
    \exists (l: loc) (v : A),
      \[c = Cons l] \* \[x = ``v] \* l ~~~> `{ content' := v; next' := next }.

  Lemma Cell_eq :
    forall A (E : Enc A) l (c : A) (n :  cell_ A),
      l ~~~> `{ content' := c; next' := n } = Cons l ~> Cell ``c n.
  Proof.
    intros A E l c n.
    xunfold Cell. xsimpl l c. 1, 2: auto.
    intros x v [= H1] H2.
    subst. xsimpl. apply enc_inj in H2. auto.
  Qed.

  Fixpoint Cell_seg A `{Enc A} (l : list val) (e : cell_ A) (st : cell_ A) :=
    match l with
    |nil => \[st = e]
    |cons x l =>
       \exists n : cell_ A, st ~> Cell x n \* n ~> Cell_seg l e
    end.

  Lemma Cell_seg_nil : forall A (EA: Enc A) (to from: cell_ A),
      from ~> Cell_seg (@nil val) to = \[from = to].
  Proof using. auto. Qed.

  Definition single_seg :
    forall A `{Enc A} (x : val) cell,
      cell ~> Cell (A:=A) x Nil = Cell_seg (x :: nil) Nil cell.
  Proof.
    intros A H x cell.
    xpull.
    + xunfold Cell_seg. xsimpl. rewrite <- Cell_seg_nil.
    + xunfold Cell_seg. xpull.
      intros.

  Admitted.

  Import LibListZ.

  Definition Queue A `{Enc A} (l : list val) (q : loc) :=
    \exists (cf cl: cell_ A),
           (q ~~~> `{ length' := LibListZ.length l; first' := cf; last' := cl }) \*
             If l = nil then \[cf = Nil] \* \[cl = Nil]
  else
    \exists L x,
      \[l = L & x] \*
            cf ~> Cell_seg L cl \* cl ~> Cell_seg (x::nil) Nil.

  Definition Queue_if A `{Enc A} (l : list val) (q : loc) :=
    \exists (cf cl : cell_ A),
      (q ~~~> `{ length' := LibListZ.length l; first' := cf; last' := cl }) \*
      If cl = Nil then \[cl = Nil] \* \[l = nil]
  else
    \exists L x,
      \[l = L & x] \*
         cf ~> Cell_seg L cl \* cl ~> Cell_seg (x::nil) Nil.

  Lemma Queue_inv : forall A (E : Enc A) l q, q ~> @Queue A E l ==> q ~> @Queue_if A E l.
    intros A E l q.
    xunfold* Queue. xpull ;=> cf cl.
    case_if.
    + xsimpl ;=> -> ->.
      xunfold Queue_if. xsimpl. case_if; xsimpl; auto.
    + xsimpl ;=> x t H1. subst.
      xunfold Queue_if.
      xsimpl. case_if.
      - subst. xunfold Cell_seg. xunfold Cell. xsimpl.
      - xsimpl. auto.
  Qed.

  Global Instance _T_inst : _T_sig := {
      T := Queue
  }.

  Global Instance _create__inst : _create__sig :=
    { create_ := create }.

  #[refine] Global Instance _create__spec_inst : _create__spec_sig := { }.
  Proof.
    intros A Enc _.
    simpl.
    xcf.
    xapp.
    xunfold Queue.
    intros.
    rew_list.
    xsimpl.
    case_if.
    xsimpl; auto.
  Qed.

  Global Instance _add__inst : _add__sig :=
    { add_ := add }.

  Set Implicit Arguments.

  #[refine] Global Instance _add__spec_inst : _add__spec_sig := { }.
  Proof.
    simpl.
    intros A E _ x'' x q'' q.
    xcf. xunfold (@Primitives.Val A). xpull. intros. subst.
    xapp ;=> cell.
    xlet. subst.
    xchanges Queue_inv.
    xunfold Queue_if.
    xpull ;=> cf ce.
    destruct q; case_if.
    + xpull ;=> H1 _.
      xapp. xmatch. do 3 xapp.
      xsimpl*. rew_list.
      xsimpl. xchange Cell_eq. xchange single_seg.
      xunfold Queue. xsimpl (@Cons A cell) (@Cons A cell).
      case_if. xsimpl (@nil val) ``x''. rew_list. auto.
      xunfold Cell_seg. xsimpl*.
    + xpull ;=> L x H1. Search app.
      apply nil_eq_app_inv in H1 as [_ H2].
      inversion H2.
    + xpull.
    + xpull ;=> L x H1. xapp.
      xmatch. xapp. xapp.

   Admitted.

End Proofs.
