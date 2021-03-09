Set Implicit Arguments.
Require Import CFLib.
Require Import Pervasives_ml Pervasives_proof.
Require Export LibListZ.
Require Import List_ml.
Require Import CFTactics.

Generalizable Variables A.


Ltac auto_tilde ::= unfold measure; rew_list in *; try math; auto.
  (* Restored to default at the end of the file *)

(* TODO: find a nicer way to write [@TLC.LibList] *)

(************************************************************)
(** Functions treated directly by CFML *)

Lemma length_spec : forall A (l:list A),
  TRIPLE (length l)
    PRE \[]
    POST \[= (@TLC.LibListZ.length _) l].
Proof using.
  xcf. xfun_ind (@list_sub A) (fun f => forall (r:list A) n,
    app f [n r] \[] \[= n + LibListZ.length r]); xgo~.
Qed.

Hint Extern 1 (RegisterSpec length) => Provide length_spec.

(* Remark: details of the script for length:

  xcf. xfun_no_simpl (fun f => forall n (l:list A),
    app f [n l] \[] \[= n + LibListZ.length l]).
  intros n. induction_wf IH: (downto 0) n.
  intros. apply (proj2 Saux). clear Saux.
  { xmatch.
    { xrets~. }
    { xapp~. xsimpl~. } }
  { xapp~. }
*)

Lemma rev_append_spec : forall A (l1 l2:list A),
  TRIPLE (rev_append l1 l2)
    PRE \[]
    POST \[= LibList.rev l1 ++ l2].
Proof using.
  intros. gen l2. induction_wf IH: (@list_sub A) l1. xcf_go~.
Qed.

Hint Extern 1 (RegisterSpec rev_append) => Provide rev_append_spec.

Lemma rev_spec : forall A (l:list A),
  TRIPLE (rev l)
    PRE \[]
    POST \[= (@TLC.LibList.rev _) l].
Proof using. xcf_go~. Qed.

Hint Extern 1 (RegisterSpec rev) => Provide rev_spec.

Lemma append_spec : forall A (l1 l2:list A),
  TRIPLE (append l1 l2)
    PRE \[]
    POST \[= (@TLC.LibList.app _) l1 l2].
Proof using.
  xcf. xfun_ind (@list_sub A) (fun f => forall (r:list A),
    app f [r] \[] \[= r ++ l2]); xgo*.
Qed.

Hint Extern 1 (RegisterSpec append) => Provide append_spec.

Lemma infix_at_spec : forall A (l1 l2:list A),
  TRIPLE (infix_at__ l1 l2)
    PRE \[]
    POST \[= (@TLC.LibList.app _) l1 l2].
Proof using. xcf_go~. Qed.

Hint Extern 1 (RegisterSpec infix_at__) => Provide infix_at_spec.

Lemma concat_spec : forall A (l:list (list A)),
  TRIPLE (concat l)
    PRE \[]
    POST \[= (@TLC.LibList.concat _) l].
Proof using.
  intros. induction_wf IH: (@list_sub (list A)) l. xcf_go*.
Qed.

Hint Extern 1 (RegisterSpec concat) => Provide concat_spec.



(************************************************************)
(** Iterators *)

Lemma iter_spec : forall A (l:list A) (f:func),
  forall (I:list A->hprop),
  (forall x t r, (l = t++x::r) ->
     TRIPLE (f x) PRE (I t) POSTUNIT (I (t&x))) ->
  TRIPLE (iter f l)
    PRE (I nil)
    POSTUNIT (I l).
Proof using.
  =>> M. cuts G: (forall r t, l = t++r ->
    app iter [f r] (I t) (# I l)). { xapp~. }
  => r. induction_wf IH: (@LibList.length A) r. =>> E.
  xcf. xmatch; rew_list in E; inverts E; xgo~.
Qed.
(* details:
  { xrets~. }
  { xapp~. xapp~. }
  *)

Hint Extern 1 (RegisterSpec iter) => Provide iter_spec.

(** Alternative spec for [iter], with an invariant that
    depends on the remaining items, rather than depending
    on the processed items. *)

Lemma iter_spec_rest : forall A (l:list A) (f:func),
  forall (I:list A->hprop),
  (forall x t, TRIPLE (f x) PRE (I (x::t)) POSTUNIT (I t)) ->
  TRIPLE (iter f l) PRE (I l) POSTUNIT (I nil).
Proof using.
  =>> M. xapp~ (fun k => \exists r, \[l = k ++ r] \* I r).
  { =>> E. xpull ;=> r' E'. subst l.
    lets: app_cancel_l E'. subst r'.
    xapp. xsimpl~. }
  { xpull ;=>> E. rewrites (>> self_eq_app_l_inv E). xsimpl~. }
Qed. (* TODO: beautify this proof *)


(** Restore the default [auto_tilde] behavior *)

Ltac auto_tilde ::= auto_tilde_default.



(************************************************************)
(************************************************************)
(************************************************************)
(* FUTURE: ListOf

  Fixpoint List A a (T:A->a->hprop) (L:list A) (l:list a) : hprop :=
    match L,l with
    | nil, nil => \[l = nil]
    | X::L', x::l' => x ~> T X \* l' ~> List T L'
    | _,_=> \[False]
    end.

  Lemma focus_nil : forall A a (T:A->a->hprop),
    \[] ==> nil ~> List T nil.
  Proof. intros. simpl. hdata_simpl. hsimpl~. Qed.

  Lemma unfocus_nil : forall a (l:list a) A (T:A->a->hprop),
    l ~> List T nil ==> \[l = nil].
  Proof. intros. simpl. hdata_simpl. destruct l. auto. hsimpl. Qed.

  Lemma unfocus_nil' : forall A (L:list A) a (T:A->a->hprop),
    nil ~> List T L ==> \[L = nil].
  Proof.
    intros. destruct L.
    simpl. hdata_simpl. hsimpl~.
    simpl. hdata_simpl. hsimpl.
  Qed.

  Lemma focus_cons : forall a (l:list a) A (X:A) (L':list A) (T:A->a->hprop),
    (l ~> List T (X::L')) ==>
    Hexists x l', (x ~> T X) \* (l' ~> List T L') \* \[l = x::l'].
  Proof.
    intros. simpl. hdata_simpl. destruct l as [|x l'].
    hsimpl.
    hsimpl~ x l'.
  Qed.

  Lemma focus_cons' : forall a (x:a) (l:list a) A (L:list A) (T:A->a->hprop),
    (x::l) ~> List T L ==>
    Hexists X L', \[L = X::L'] \* (x ~> T X) \* (l ~> List T L').
  Proof. intros. destruct L; simpl; hdata_simpl; hsimpl~. Qed.

  Lemma unfocus_cons : forall a (x:a) (l:list a) A (X:A) (L:list A) (T:A->a->hprop),
    (x ~> T X) \* (l ~> List T L) ==>
    ((x::l) ~> List T (X::L)).
  Proof. intros. simpl. hdata_simpl. hsimpl. Qed.

  Global Opaque List.

*)