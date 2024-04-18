  (** See theories/ExampleStack.v for corresponding formalization in the deep embedding. *)

Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
Generalizable Variables A.

Implicit Types n m : int.
Implicit Types p q : loc.


Require Import Stack_ml.
Require stack_valid.

(* ********************************************************************** *)
(** ** Representation predicate *)

(** [p ~> Stack L] relates a pointer [p] with the list [L] made of
    the elements in the stack. *)
Module Stack : stack_valid.T.
Definition Stack (L:list int) (p:loc) : hprop :=
  p ~~> L.

Lemma Stack_eq : forall (p:loc) (L:list int),
  p ~> Stack L  =  p ~~> L.
Proof using. auto. Qed.


(* ********************************************************************** *)
(** ** Verification *)

Lemma create_spec : 
  SPEC (create tt)
    PRE \[]
    POST (fun p => (p ~> Stack nil)).
Proof using.
  xcf. xapp. xsimpl.
  (* TODO: how to avoid the Unshelve? *)
  Unshelve. xend. xend.
Qed.

Hint Extern 1 (RegisterSpec create) => Provide create_spec.

Lemma is_empty_spec : forall (p:loc) (L:list int),
  SPEC (is_empty p)
    PRE (p ~> Stack L)
    POST (fun (b:bool) => \[b = isTrue (L = nil)] \* p ~> Stack L).
Proof using.
  xcf. xunfold Stack. xapp.
  xapp. xpolymorphic_eq. xsimpl*.
Qed.

Hint Extern 1 (RegisterSpec is_empty) => Provide is_empty_spec.

Lemma push_spec : forall (p:loc) (x:int) (L:list int),
  SPEC (push p x)
    PRE (p ~> Stack L)
    POSTUNIT (p ~> Stack (x::L)).
Proof using.
  xcf. xunfold Stack. xapp. xapp. xsimpl.
Qed.

Hint Extern 1 (RegisterSpec push) => Provide push_spec.

Lemma pop_spec : forall (p:loc) (L:list int),
  L <> nil ->
  SPEC (pop p)
    PRE (p ~> Stack L)
    POST (fun (x:int) => \exists L', \[L = x::L'] \* (p ~> Stack L')).
Proof using.
  introv N. xcf. xunfold Stack. xmatch. { xapp. xvals*. }
Qed.

Hint Extern 1 (RegisterSpec pop) => Provide pop_spec.

Lemma clear_spec : forall (p:loc) (L:list int),
  SPEC (clear p)
    PRE (p ~> Stack L)
    POSTUNIT (p ~> Stack nil).
Proof using.
  xcf. xunfold Stack. xapp. xsimpl.
Qed.

Hint Extern 1 (RegisterSpec clear) => Provide clear_spec.

Lemma concat_spec : forall (p1 p2:loc) (L1 L2:list int),
  SPEC (concat p1 p2)
    PRE (p1 ~> Stack L1 \* p2 ~> Stack L2)
    POSTUNIT (p1 ~> Stack (L1 ++ L2) \* p2 ~> Stack nil).
Proof using.
  xcf. xunfold Stack. xapp. xapp. xapp.
  rewrite <- (Stack_eq p2). xapp. xsimpl.
Qed.

Hint Extern 1 (RegisterSpec concat) => Provide concat_spec.

Opaque Stack.

Lemma rev_append_spec : forall (p1 p2:loc) (L1 L2:list int),
  SPEC (rev_append p1 p2)
    PRE (p1 ~> Stack L1 \* p2 ~> Stack L2)
    POSTUNIT (p1 ~> Stack nil \* p2 ~> Stack (rev L1 ++ L2)).
Proof using.
intros. gen p1 p2 L2. induction_wf IH: list_sub L1. intros.
  xcf. xif; intros C.
  { (* case cons *)
    xapp~ ;=> x L1' E. xapp. xapp. { subst*. } xsimpl. subst. rew_list~. }
  { (* case nil *)
    xval. xsimpl~. subst. rew_list~. } 
Qed.


Hint Extern 1 (RegisterSpec rev_append) => Provide rev_append_spec.

Definition create : val := Stack_ml.create.
Definition is_empty := is_empty.
Definition push := push.
Definition pop := pop.
Definition clear := clear.
Definition concat := concat.
Definition rev_append := rev_append.


End Stack.
