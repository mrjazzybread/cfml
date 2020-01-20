(**

Separation Logic Foundations

Chapter: "Affine".

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From Sep Require Export SLFDirect.

Implicit Types f : var.
Implicit Types b : bool.
Implicit Types v : val.
Implicit Types h : heap.
Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Chapter in a rush *)

(** The Separation Logic framework that we have constructed is well-suited
    for a language with explicit deallocation, but cannot be used as such for
    a language equipped with a garbage collector. As we pointed out in the
    chapter [SLFBasic], there is no rule in Separation Logic that allows
    discarding a heap predicate from the precondition or the postcondition.

    In this chapter, we explain how to generalize the Separation Logic
    framework to support a "garbage collection rule", which one may invoke
    in the logic to discard predicates describing allocated data, thereby
    reflecting on the action of the garbage collector. The resulting
    framework is said to describe an "affine" logic, as opposed to a "linear"
    logic.

    This chapter is organized as follows:

    - first, we recall the example demonstrating the need for a new rule,
    - second, we present the statement of the "garbage collection rule",
    - third, we show how to refine the definition of Separation Logic
      triples, so as to accomodate the new rule.

    Although in the present course we consider a language for which it is
    desirable that any heap predicate can be discarded, we will present
    general definitions allowing to fine-tune which heap predicates can
    be discarded and which cannot be discarded by the user. We will argue
    why such a fine-tuning may be interesting. *)


(* ########################################################### *)
(** ** Motivation for the garbage collection rule *)

(** Let us recall the example of the function [succ_using_incr_attempt]
    from chapter [SLFBasic]. This function allocates a reference with
    contents [n], then increments that reference, and finally returning
    its contents, that is, [n+1]. Let us revisit this example, with
    this time the intention of establishing for it a postcondition that
    does not leak the existence of a left-over reference cell.

[[
    let succ_using_incr n =
      let p = ref n in
      incr p;
      !p
]]

*)

Definition succ_using_incr :=
  VFun 'n :=
    Let 'p := 'ref 'n in
    incr 'p ';
    '! 'p.

(** In the framework developed so far, the heap predicate describing the
    reference cell allocated by the function cannot be discarded by the
    user, because the code does not feature a deallocation operation.
    As a result, the user is forced to include in the postcondition the
    description of a left-over reference. *)

Lemma Triple_succ_using_incr : forall (n:int),
  TRIPLE (succ_using_incr n)
    PRE \[]
    POST (fun r => \[r = n+1] \* \exists p, (p ~~> (n+1))).
Proof using.
  xwp. xapp. intros p. xapp. xapp. xsimpl. { auto. }
Qed.

(** This situation is desirable in a programming language with explicit
    deallocation, because it ensures that the code written by the
    programmer is not missing any deallocation operation. However, it is
    ill-suited for a programming language equipped with a garbage collector
    that performs deallocation automatically.

    In this chapter, we present an "affine" version of Separation Logic,
    where the above function [succ_using_incr_attempt] admits the
    postcondition [fun r => \[r = n+1]], and needs not mention the
    left-over reference. *)


(* ########################################################### *)
(** ** Statement of the garbage collection rule *)

(** There are several ways to state a "garbage collection rule" and its
    corrolaries. We present them next. *)

(** The most direct presentation of the "garbage collection rule" allows
    one to freely discard any piece of state from the postcondition.

    More precisely, this rule, named [triple_hany_post], asserts that an
    arbitrary heap predicate [H'] can be dropped from the postcondition. *)

Parameter triple_hany_post : forall t H' Q,
  triple t H (Q \*+ H') ->
  triple t H Q.

(** A symmetric rule, named [triple_hany_pre], asserts that an arbitrary
    heap predicate [H'] can be dropped from the precondition. *)

Parameter triple_hany_pre : forall t H H' Q,
  triple t H Q ->
  triple t (H \* H') Q.

(** As we prove further on, the rule [triple_hany_pre] can be derived from
    [triple_hany_post] using the frame rule, but not vice-versa. Thus, we
    thereafter focus on the more general rule [triple_hany_post], which
    operates on the postcondition. *)

(** Let us show that, using this rule [triple_hany_post], we can derive
    the desired specification for the motivating example from the
    specification that mentions the left-over postcondition. *)

Lemma Triple_succ_using_incr' : forall (n:int),
  TRIPLE (succ_using_incr n)
    PRE \[]
    POST (fun r => \[r = n+1]).
Proof using.
  intros. applys triple_hany_post. applys Triple_succ_using_incr.
Qed.


(* ########################################################### *)
(** ** Fine-grained control on collectable predicates *)

(** As suggested in the introduction, it may be useful to constraint
    the garbage collection rule so that it can be used to discard
    only certain types of heap predicates, but not all. For example,
    even in a programming language featuring a garbage collector,
    it may be useful to ensure that every file handle opened eventually
    gets closed, or that every lock acquired eventually gets released.
    File handles and locks are example of resources that may be
    described in Separation Logic, yet should not be freely discarded.

    As another example, consider the extension of Separation Logic with
    "time credits", which are used for complexity analysis. In such a
    setting, it is desirable to throw away a positive number of credits
    to reflect for over-approximations, however it must be ruled out to
    throw away negative number of credits, as this would compromise
    the soundness of the framework. *)

(** To constraint the garbage collection rule and allow fine-tuning
    of which heap predicates may be thrown away, we introduce the notion
    of "affine predicates", captured by a judgment written [haffine H].
    The idea is that only predicates satisyfing [haffine] may get freely
    discarded. *)

Parameter haffine : hprop -> Prop.

Parameter triple_haffine_post : forall t H' Q,
  haffine H' ->
  triple t H (Q \*+ H') ->
  triple t H Q.

(** The variant of the garbage collection rule that operates on the
    precondition is constrained in a similar way. *)

Parameter triple_haffine_pre : forall t H H' Q,
  haffine H' ->
  triple t H Q ->
  triple t (H \* H') Q.

(** The definition of [haffine] should be set up in such a way that
    this predicate distributes in the expected way on each of the
    Separation Logic operators, as captured by the following lemma. *)

Parameter haffine_hempty :
  haffine \[].

Parameter haffine_hpure : forall P,
  haffine \[P].

Parameter haffine_hstar : forall H1 H2,
  haffine H1 ->
  haffine H2 ->
  haffine (H1 \* H2).

Parameter haffine_hexists : forall A (J:A->hprop),
  (forall x, haffine (J x)) ->
  haffine (\exists x, (J x)).

Parameter haffine_hforall : forall A `{Inhab A} (J:A->hprop),
  (forall x, haffine (J x)) ->
  haffine (\forall x, (J x)).

(** We will present further on a template for defining [haffine] in
    a way that guarantees by construction that all these properties
    indeed hold. *)


(* ########################################################### *)
(** ** The garbage collection heap predicate *)

(** We now introduce a new heap predicate that is very handy for
    describing "pieces of heap to be garbage collected". We will
    use it to reformulate the garbage collection rule is a more
    concise and more usable way.

    This heap predicate is named [hgc] and is written [\GC].
    We define it as "some heap predicate [H] that satisfies [haffine]",
    as formalized next. *)

Definition hgc : hprop :=
  \exists H, H \* \[haffine H].

Notation "\GC" := (hgc).

(** Using the predicate [\GC], we can reformulate the constrained
    garbage collection rule [triple_haffine_post] as follows. *)

Parameter triple_htop_post : forall t H Q,
  triple t H (Q \*+ \GC) ->
  triple t H Q.

(** Not only is this rule more concise, it also has the benefits
    that the piece of heap discarded, previously described by [H']
    no longer needs to be provided upfront at the moment of applying
    the rule. It may be provided later on in the reasoning, by
    instantiating the existential quantifier carried into the
    definition of the [\GC] predicate, a.k.a., [hgc]. This process
    of exploiting the [\GC] predicate is captured by the following
    lemma, which asserts that any affine heap predicate entails [\GC]. *)

Lemma himpl_hgc_r : forall H,
  haffine H ->
  H ==> \GC.
Proof using.
  introv M. unfold hgc. applys himpl_hexists_r H.
  applys* himpl_hstar_hpure_r.
Qed.

(** The tactic [xsimpl] is extended with specific support for the
    predicate [\GC]. In particular, [xsimpl] simplifies goals of the
    form [H ==> \GC] by turning them into [haffine H] using the above
    lemma. The tactic then tries to discharge [haffine H] by means that
    depend on the choice of the definition of [haffine]. *)


(* ########################################################### *)
(** ** Exploiting the garbage collection in proofs *)

(** In a verification proof, there are two ways to discard heap
    predicates that are no longer needed:

    - either by invoking [triple_haffine_pre] to remove a specific
      predicate from the current state, i.e., the precondition;
    - or by invoking [triple_htop_post] to add a [\GC] into the
      current postcondition and allow subsequent removal of any
      predicate that may be left-over in the final entailment
      justifying that the final state satisfies the postcondition.

    Eager removal of predicates from the current state is never
    necessary: one can be lazy and postpone the application of
    the garbage collection rule until the last step of reasoning.

    To that end, it suffices to anticipate, right from the beginning
    of the verification proof, the possibility of discarding heap
    predicates from the final state, when proving that it entails
    the postcondition. Concretely, it suffices to apply the rule
    [triple_htop_post] as very first step of the proof to extend
    the postcondition with a [\GC] predicate, which will be used
    to "capture" all the garbage left-over at the end of the proof.

    We implement this strategy once-and-forall by integrating directly
    the rule [triple_htop_post] into the tactic [xwp], which sets up
    the verification proof by computing the characteristic formula.
    To that end, we generalize the lemma [xwp_lemma], which the tactic
    [xwp] applies. Its original statement is as follows. *)

Parameter xwp_lemma : forall v1 v2 x t1 H Q,
  v1 = val_fun x t1 ->
  H ==> wpgen ((x,v2)::nil) t1 Q ->
  triple (trm_app v1 v2) H Q.

(** Its generalized form extends the postcondition to which the formula
    computed by [wpgen] is applied from [Q] to [Q \*+ \GC], as shown below. *)

Lemma xwp_lemma' : forall v1 v2 x t1 H Q,
  v1 = val_fun x t1 ->
  H ==> wpgen ((x,v2)::nil) t1 (Q \*+ \GC) ->
  triple (trm_app v1 v2) H Q.
Proof using. introv E M. applys triple_htop_post. applys* xwp_lemma. Qed.

(** Using the updated version of [xwp], the proof of [succ_using_incr]
    works out very smoothly, the left-over reference being automatically
    absorbed into the [\GC] predicate by [xsimpl]. *)

Lemma Triple_succ_using_incr : forall (n:int),
  TRIPLE (succ_using_incr n)
    PRE \[]
    POST (fun r => \[r = n+1]).
Proof using.
  xwp. xapp. intros p. xapp. xapp. xsimpl. { auto. }
Qed.


(* ########################################################### *)
(** ** Fully-affine and fully-linear instantiations *)

(** In the toy language that we consider, every predicate may be
    discarded, thus [haffine H] can be defined to be always true,
    using the following definition. In that case, [\GC] becomes
    equivalent to [htop], the predicate that holds of any heap. *)

Module FullyAffineLogic.

  Definition haffine (H:hprop) := True.

  Definition htop (h:heap) := True.

  Lemma hgc_eq_htop : \GC = htop.
  Proof using.
    unfold hgc, htop. applys himpl_antisym.
    { intros h. xsimpl. }
    { intros h. xsimpl (=h). }
  Qed.

End FullyAffineLogic.

(** On the contrary, one can stick to a "linear" Separation Logic
    and enforce that no heap predicate can be discarded simply
    by definining [haffine] to only be satisfied by the empty
    heap predicate. In that case, [\GC] becomes equivalent to [\[]]. *)

Module FullyLinearLogic.

  Definition haffine (H:hprop) := (H = \[]).

  Lemma hgc_eq_hempty : \GC = \[].
  Proof using.
    unfold hgc. applys himpl_antisym.
    { xsimpl. }
    { xsimpl. }
  Qed.

End FullyLinearLogic.

(** In what follows, we purposely leave the definition of [haffine]
    abstract for the sake of generality. *)


(* ########################################################### *)
(** ** Refined definition of Separation Logic triples *)

(** In what follows, we explain how to refine the notion of Separation
    Logic triple so as to accomodate the garbage collection rule.

    Recall the definition of triple for a linear logic.

[[
    Definition triple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
      forall (H':hprop), hoare t (H \* H') (Q \*+ H').
]]

    The garbage collection rule [triple_htop_post] asserts that
    postconditions may be freely extended with the [\GC] predicate.
    To support this rule, it suffices to modify the definition of
    [triple] to include the predicate [\GC] in the postcondition
    of the underlying Hoare triple, as follows. *)

Definition triple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall (H':hprop), hoare t (H \* H') (Q \*+ H' \*+ \GC).

(** Again, keep in mind that this definition of [triple] is strictly
    more general than the previous one. Indeed, as explained earlier on,
    by instantiating [haffine] as the predicate [fun (H:hprop) => \[]],
    the predicate [\GC] becomes equivalent to the empty predicate [\[]].
    In that case, [\GC] can be replaced with [\[]], which simplifies away;
    we thus recover exactly the previous definition of [triple]. *)

(** For the refined definition of [triple] using [\GC], one can prove that:

    - all the existing reasoning rules for linear triples remain sound;
    - the rule [triple_htop_post] is sound;
    - the rule [triple_haffine_hpost] and [triple_haffine_hpre] can
      be derived from [triple_htop_post] and the other structural rules.

    The proofs appear further on in this chapter.

    One fundamental property that appears necessary in many of the proof
    is the following lemma, which asserts that two occurences of [\GC]
    can always be merged into one. *)

Lemma hstar_hgc_hgc :
  \GC \* \GC = \GC.
Proof using.
  unfold hgc. applys himpl_antisym.
  { xsimpl. }
  { xpull. intros H1 H2. xsimpl (H1 \* H2). }
Qed.

(** Let us conclude this first part of the chapter with the proof of
    the garbage collection rule. *)

(* EX2! (triple_htop_post_proof) *)
(** Prove [triple_htop_post] with respect to the refined definition of
    [triple]. *)

Lemma triple_htop_post_proof : forall t H Q,
  triple t H (Q \*+ \GC) ->
  triple t H Q.
Proof using. (* ADMITTED *)
  introv M. unfold triple in *. intros H2.
  specializes M H2. applys_eq M 1.
  { applys qprop_eq. intros v. repeat rewrite hstar_assoc.
    rewrite (hstar_comm H2).
    rewrite <- (hstar_assoc \Top \Top).
    rewrite hstar_htop_htop. auto. }
Qed. (* /ADMITTED *)


(** The principle of the ramified-frame rule immediately generalizes
    to handle the consequence-frame-top rule, which is like the
    consequence-frame rule but with premise [Q1 \*+ H2 ===> Q \*+ \Top]. *)

Lemma triple_ramified_frame_top : forall H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* (Q \*+ \Top)) ->
  triple t H Q.
Proof using.
  introv M W. applys triple_conseq_frame_htop (Q1 \--* (Q \*+ \Top)) M.
  { applys W. } { applys qwand_cancel. }
Qed.


(* ########################################################### *)
(** ** Garbage collection rules in WP style *)

Lemma wp_ramified : forall Q1 Q2 t,
  (wp t Q1) \* (Q1 \--* Q2 \*+ \Top) ==> (wp t Q2).
Proof using.
  intros. unfold wp. xpull ;=> H M.
  xsimpl (H \* (Q1 \--* Q2 \*+ \Top)). intros H'.
  applys hoare_conseq M; xsimpl.
Qed.

Lemma wp_hany_pre : forall t H Q,
  (wp t Q) \* H ==> wp t Q.
Proof using. intros. applys himpl_trans_r wp_ramified. xsimpl. Qed.

Lemma wp_hany_post : forall t H Q ,
  wp t (Q \*+ H) ==> wp t Q.
Proof using. intros. applys himpl_trans_r wp_ramified. xsimpl. Qed.


Lemma wp_conseq_frame_htop : forall t H Q1 Q2,
  Q1 \*+ H ===> Q2 \*+ \Top ->
  (wp t Q1) \* H ==> (wp t Q2).
Proof using.
  introv M. rewrite <- wp_equiv.
  applys triple_conseq_frame_htop (wp t Q1) M.
  { rewrite wp_equiv. xsimpl. } { xsimpl. }
Qed.

(** The above statement asserts that:

    1. [wp t Q1] can absorb any heap predicate [H] with which it
      is starred, changing it to [wp t (Q1 \*+ H)].

    2. [wp t Q1] can be weakened to [wp t Q2] when [Q1 ===> Q2].

    3. [wp t (Q1 \*+ H)] can be simplified to [wp t Q1] if one
      wants to discard [H] from the postcondition. *)

(** The garbage collection in precondition for [wp] asserts that
    [wp] can absorb and discard any desired heap predicate [H]
    that sits next to it (i.e., that it is starred with). *)

Lemma wp_hany_pre : forall t H Q,
  (wp t Q) \* H ==> wp t Q.
Proof using.
  intros. rewrite <- wp_equiv.
  applys triple_hany_pre. rewrite* wp_equiv.
Qed.

(** The garbage collection in postconditions for [wp] asserts
    that [wp] can absorb and discard any desired heap predicate
    [H] that appears in its postcondition. *)

Lemma wp_hany_post : forall t H Q ,
  wp t (Q \*+ H) ==> wp t Q.
Proof using.
  intros. rewrite <- wp_equiv.
  applys triple_hany_post. rewrite* wp_equiv.
Qed.

(** Note, equivalently, the [H] from rules [wp_hany_pre] and
   [wp_hand_post] may be replaced with [\Top]. *)


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Additional contents *)


(* ########################################################### *)
(** ** Proof of derived rules *)

(* the rule [triple_haffine_hpost] and [triple_haffine_hpre] *)

(** Recall the lemma [triple_htop_post] from the previous chapter. *)

Parameter triple_htop_post : forall t H Q,
  triple t H (Q \*+ \Top) ->
  triple t H Q.

(* EX2! (triple_hany_post) *)
(** The following lemma provides an alternative presentation of the
    same result as [triple_htop_post]. Prove that it is derivable
    from [triple_htop_post] and [triple_conseq]. *)

Lemma triple_hany_post : forall t H H' Q,
  triple t H (Q \*+ H') ->
  triple t H Q.
Proof using.
(* SOLUTION *)
  introv M. applys* triple_htop_post. applys triple_conseq M.
  { applys himpl_refl. }
  { intros v. applys himpl_frame_r. applys himpl_htop_r. }
(* /SOLUTION *)
Qed.

(** Reciprocally, [triple_htop_post] is trivially derivable from
    [triple_hany_post], simply by instantiating [H'] as [\Top]. *)

Lemma triple_htop_post_derived_from_triple_hany_post : forall t H Q,
  triple t H (Q \*+ \Top) ->
  triple t H Q.
Proof using. intros. applys triple_hany_post \Top. auto. Qed.

(** The reason we prefer [triple_htop_post] to [triple_hany_post]
    is that it does not require providing [H'] at the time of applying
    the rule. The instantiation is postponed through the introduction
    of [\Top], which is equivalent to [\exists H', H']. Delaying the
    instantiation of [H'] using [\Top] rather than throught the
    introduction of an evar enables more robust proof scripts and
    tactic support. *)

(* EX2! (triple_htop_pre) *)
(** The rule [triple_htop_post] enables discarding pieces of
    heap from the postcondition. The symmetric rule [triple_htop_pre]
    enables discarding pieces of heap from the precondition.

    Prove that it is derivable from [triple_htop_post] and
    [triple_frame] (and, optionally, [triple_conseq]). *)

Lemma triple_htop_pre : forall t H Q,
  triple t H Q ->
  triple t (H \* \Top) Q.
Proof using.
(* SOLUTION *)
  introv M. applys triple_htop_post. applys triple_frame. auto.
(* /SOLUTION *)
Qed.

(* EX2! (triple_htop_pre) *)
(** The rule [triple_hany_pre] is a variant of [triple_htop_pre].
    Prove that it is derivable.
    You may exploit [triple_htop_pre], or [triple_hany_post],
    or [triple_htop_post], whichever you find simpler. *)

Lemma triple_hany_pre : forall t H H' Q,
  triple t H Q ->
  triple t (H \* H') Q.
Proof using.
(* SOLUTION *)
  dup 3.
  (* first proof, based on [triple_hany_post]: *)
  introv M. applys triple_hany_post. applys triple_frame. auto.
  (* second proof, based on [triple_htop_pre]: *)
  introv M. lets N: triple_htop_pre M. applys triple_conseq N.
  { applys himpl_frame_r. applys himpl_htop_r. }
  { applys qimpl_refl. }
  (* third proof, based on [triple_htop_post]: *)
  introv M. applys triple_htop_post.
  lets N: triple_frame H' M.
  applys triple_conseq N.
  { applys himpl_refl. }
  { intros v. applys himpl_frame_r. applys himpl_htop_r. }
(* /SOLUTION *)
Qed.

(** Here again, the reciprocal holds: [triple_hany_pre] is trivially
    derivable from [triple_htop_pre]. The variant of the rule that is
    most useful in practice is actually yet another presentation,
    which applies to any goal and enables specifying explicitly the
    piece of the precondition that one wishes to discard. *)

Lemma triple_hany_pre_trans : forall H1 H2 t H Q,
  triple t H1 Q ->
  H ==> H1 \* H2 ->
  triple t H Q.
Proof using.
  introv M WH. applys triple_conseq (H1 \* H2) Q.
  { applys triple_hany_pre. auto. }
  { applys WH. }
  { applys qimpl_refl. }
Qed.

(** Remark: the lemmas that enable discarding pieces of precondition
    (e.g., [triple_htop_pre]) are derivable from those that enable
    discarding pices of postconditions (e.g., [triple_htop_post]),
    but not the other way around.

    Advanced remark: the above remark can be mitigated. If we expose
    that [triple t H Q <-> triple t' H Q] holds whenever [t] and [t']
    are observationally equivalent with respect to the semantics
    defined by [eval], and if we are able to prove that [let x = t in x]
    is observationally equivalent to [t] for some fresh variable x,
    then it is possible to prove that [triple_htop_post] is derivable
    from [triple_htop_pre]. Indeed, the postcondition of [t] can be viewed
    as the precondition of the [x] occuring in the right-hand side of the
    term [let x = t in x]. Thus, discarding a heap predicate from the
    postcondition of [t] can be simulated by discarding a heap predicate
    from the precondition of [x]. *)

(** The "combined structural rule" generalizes the rule above
    by also integrating the garbage collection rule. *)

Lemma triple_conseq_frame_htop : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q \*+ \Top ->
  triple t H Q.

(* EX1! (triple_conseq_frame_htop) *)
(** Prove the combined structural rule.
    Hint: recall lemma [triple_htop_post]. *)

Proof using.
(* SOLUTION *)
  introv M WH WQ. applys triple_htop_post.
  applys~ triple_conseq_frame M WH WQ.
(* /SOLUTION *)
Qed.



(* ########################################################### *)
(** ** Construction template for [haffine] *)

Definition heap_affine (h:heap) := True.

Definition haffine (H : hprop) : Prop :=
  forall h, H h -> heap_affine h.

(** Properties of haffine *)

Parameter haffine_hempty :
  haffine \[].

Lemma haffine_hpure : forall P,
  haffine \[P].
Proof using.
  intros. applys* haffine_hexists. intros HP. applys* haffine_hempty.
Qed.

Parameter haffine_hstar : forall H1 H2,
  haffine H1 ->
  haffine H2 ->
  haffine (H1 \* H2).

(** Affinity for postconditions *)

Definition haffine_post (A:Type) (J:A->hprop) : Prop :=
  forall x, haffine (J x).


Parameter haffine_hexists : forall A (J:A->hprop),
  (forall x, haffine (J x)) ->
  haffine (\exists x, (J x)).

Parameter haffine_hforall : forall A `{Inhab A} (J:A->hprop),
  (forall x, haffine (J x)) ->
  haffine (\forall x, (J x)).

Lemma haffine_hexists : forall A (J:A->hprop),
  haffine_post J ->
  haffine (hexists J).
Proof using. introv F1 (x&Hx). applys* F1. Qed.

Lemma haffine_hforall : forall A `{Inhab A} (J:A->hprop),
  haffine_post J ->
  haffine (hforall J).
Proof using. introv IA F1 Hx. applys* F1 arbitrary. Qed.

(** *)

Lemma haffine_hgc :
  haffine \GC.
Proof using.
  applys haffine_hexists. intros H h Hh. rewrite hstar_hpure in Hh.
  destruct Hh as [M N]. applys* M.
Qed.



(* ########################################################### *)
(** ** Proof of the standard rules *)

(** *)
(* EX1! (triple_frame) *)
(** Prove the frame rule for the actual definition of [triple].
    Take inspiration from the proof of [SL_frame_rule]. *)

Lemma triple_frame' : forall t H Q H',
  triple t H Q ->
  triple t (H \* H') (Q \*+ H').
Proof using.
(* SOLUTION *)
  introv M. unfold triple in *. rename H' into H1. intros H2.
  specializes M (H1 \* H2). applys_eq M 1 2.
  { rewrite hstar_assoc. auto. }
  { applys qprop_eq. intros v.
    repeat rewrite hstar_assoc. auto. }
(* /SOLUTION *)
Qed.


Lemma triple_seq : forall t1 t2 H Q H1,
  triple t1 H (fun v => H1) ->
  triple t2 H1 Q ->
  triple (trm_seq t1 t2) H Q.
Proof using.
  (* 1. We unfold the definition of [triple] to reveal a [hoare] judgment. *)
  introv M1 M2. intros H'. (* optional: *) unfolds triple.
  (* 2. We invoke the reasoning rule [hoare_seq] that we have just established. *)
  applys hoare_seq.
  { (* 3. For the hypothesis on the first subterm [t1],
       we can invoke directly our first hypothesis. *)
    applys M1. }
    ...
  { (* 4. For the hypothesis on the first subterm [t2],
       we need a little more work to exploit our second hypothesis.
       Indeed, the precondition features an extra [\Top].
       To handle it, we need to instantiate [M2] with [H' \* \Top],
       then merge the two [\Top] that appear into a single one.
       We could begin the proof script with:
         [specializes M2 (H' \* \Top). rewrite <- hstar_assoc in M2.]
       However, it is simpler to directly invoke the consequence rule,
       and let [xsimpl] do all the tedious work for us. *)
    applys hoare_conseq. { applys M2. } { xsimpl. } { xsimpl. } }
Qed.




(* ########################################################### *)
(** ** Properties of [hgc] *)

Lemma hgc_of_heap_affine : forall h,
  heap_affine h ->
  \GC h.
Proof using.
  intros. rewrite hgc_eq. exists (=h).
  rewrite hstar_hpure. split~. { introv ->. auto. }
Qed.

Lemma himpl_hgc_r : forall H,
  haffine H ->
  H ==> \GC.
Proof using.
  introv M. rewrite hgc_eq. applys himpl_hexists_r H.
  applys~ himpl_hstar_hpure_r.
  (* low-level: [intros h K. applys hgc_of_heap_affine. applys M K. *)
Qed.

Lemma hempty_himpl_hgc :
  \[] ==> \GC.
Proof using. applys himpl_hgc_r. applys haffine_hempty. Qed.

Lemma himpl_same_hstar_hgc_r : forall H,  (* needed? *)
  H ==> H \* \GC.
Proof using.
  intros. (* himpl_frame_r *)
  rewrite hstar_comm. rewrite <- (hstar_hempty_l H) at 1.
  applys himpl_frame_l. applys himpl_hgc_r. applys haffine_hempty.
Qed.

Lemma himpl_hstar_hgc_r : forall H H', (* needed? *)
  H ==> H' ->
  H ==> H' \* \GC.
Proof using.
  introv M. applys himpl_trans (rm M). applys himpl_same_hstar_hgc_r.
Qed.


(* ******************************************************* *)
(** ** The [xsimpl] tactic *)

(** Finally, [xsimpl] provides support for eliminating [\Top] on the RHS.
    First, if the RHS includes several occurrences of [\Top], then they
    are replaced with a single one. *)

Lemma xsimpl_demo_rhs_htop_compact : forall H1 H2 H3 H4,
  H1 \* H2 ==> H3 \* \GC \* H4 \* \GC.
Proof using.
  intros. xsimpl.
Abort.

(** Second, if after cancellations the RHS consists of exactly
   [\Top] and nothing else, then the goal is discharged. *)

Lemma xsimpl_demo_rhs_htop : forall H1 H2 H3,
  H1 \* H2 \* H3 ==> H3 \* \GC \* H2 \* \GC.
Proof using.
  intros. xsimpl.
Abort.

Lemma himpl_example_3 : forall (p q:loc),
  p ~~~> 3 \* q ~~~> 3 ==>
  p ~~~> 3 \* \GC.
Proof using. xsimpl. Qed.



(* ******************************************************* *)
(** ** [mkstruct] and [xgc] tactic *)

(** [mkstruct] revisited *)

Definition mkstruct (F:formula) : formula :=
  fun Q => \exists Q', F Q' \* (Q' \--* (Q \*+ \Top)).

Lemma mkstruct_ramified : forall Q1 Q2 F,
  (mkstruct F Q1) \* (Q1 \--* Q2 \*+ \Top) ==> (mkstruct F Q2).
Proof using. unfold mkstruct. xsimpl. Qed.


(** [xtop_lemma] helps exploiting [mkstruct] to augment the postcondition
    with [\Top]. It proves the entailment:
[[
    H ==> mkstruct F (Q \*+ \Top) ->
    H ==> mkstruct F Q.
]]
*)

Lemma xtop_lemma : forall H Q F,
  H ==> mkstruct F (Q \*+ \Top) ->
  H ==> mkstruct F Q.
Proof using.
  introv M. xchange M.
  lets N: mkstruct_ramified (Q \*+ \Top) Q F. xchanges N.
Qed.

(** Other lemmas for structural rules, not shown here, can be similarly
    devised. *)



(** [xtop] involves [xtop_lemma], exploiting the leading [mkstruct]. *)

Tactic Notation "xtop" :=
  applys xtop_lemma.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Bonus contents (optional reading) *)


(* ########################################################### *)
(** ** Low-level definition of refined triples *)

(** Recall the final definition of [triple], as:
    [forall (H':hprop), hoare (H \* H') t (Q \*+ H' \*+ \GC)].

    This definition can also be reformulated directly in terms of union
    of heaps. All we need to do is introduce an additional piece of
    state to describe the part covered by new [\Top] predicate.

    In order to describe disjointness of the 3 pieces of heap that
    describe the final state, we first introduce an auxiliary definition:
    [Fmap.disjoint_3 h1 h2 h3] asserts that the three arguments denote
    pairwise disjoint heaps. *)

Definition fmap_disjoint_3 (h1 h2 h3:heap) : Prop :=
     Fmap.disjoint h1 h2
  /\ Fmap.disjoint h2 h3
  /\ Fmap.disjoint h1 h3.

(** We then generalize the result heap from [h1' \u h2] to
    [h1' \u h2 \u h3'], where [h3'] denotes the piece of the
    final state that is described by the [\GC] heap predicate
    that appears in the definition of [triple]. *)

Definition triple_lowlevel (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall h1 h2,
  Fmap.disjoint h1 h2 ->
  H h1 ->
  exists v h1' h3',
       fmap_disjoint_3 h1' h2 h3'
    /\ heap_affine h3'
    /\ eval (h1 \u h2) t (h1' \u h2 \u h3') v
    /\ Q v h1'.

(** One can prove the equivalence of [triple] and [triple_lowlevel]
    following a similar proof pattern as previously. The proof is a bit
    more technical and requires additional tactic support to deal with
    the tedious disjointness conditions, so we omit the details here. *)

Parameter triple_iff_triple_lowlevel : forall t H Q,
  triple t H Q <-> triple_lowlevel t H Q.




