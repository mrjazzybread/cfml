(**

Separation Logic Foundations

Chapter: "Himpl".

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From TLC Require Import LibCore.
From Sep Require Import Semantics.

(* TODO move *)
  Module CoercionsFromStrings.
  Coercion string_to_var (x:string) : var := x.
  End CoercionsFromStrings.
  Arguments fmap_single {A} {B}.
  Arguments fmap_union {A} {B}.
  Arguments fmap_disjoint {A} {B}.
  
  Arguments fmap_union_empty_l {A} {B}.
  Arguments fmap_union_comm_of_disjoint {A} {B}.
  Arguments fmap_union_assoc {A} {B}.
  Arguments fmap_disjoint_union_eq_l {A} {B}.
  Arguments fmap_disjoint_union_eq_r {A} {B}.

  Import NotationForVariables NotationForTerms CoercionsFromStrings.

Close Scope fmap_scope.

From Sep Require Import SLFHprop.

Implicit Types H : hprop.
Implicit Types Q : val->hprop.


(* ####################################################### *)
(** * The chapter in a rush *)

(* ******************************************************* *)
(** ** Definition of entailment *)

(** The "entailement relationship" [H1 ==> H2] asserts that any
    heap satisfying [H1] also satisfies [H2]. *)

Definition himpl (H1 H2:hprop) : Prop :=
  forall (h:heap), H1 h -> H2 h.

Notation "H1 ==> H2" := (himpl H1 H2) (at level 55).

(** [H1 ==> H2] captures the fact that [H1] is a stronger precondition
    than [H2], in the sense that it is more restrictive. *)

(** The entailment relation is trivially reflexive and transitive,
    (like implication is). *)

Lemma himpl_refl : forall H,
  H ==> H.
Proof using. intros h. hnf. auto. Qed.

Lemma himpl_trans : forall H2 H1 H3,
  (H1 ==> H2) ->
  (H2 ==> H3) ->
  (H1 ==> H3).
Proof using. introv M1 M2. intros h H1h. eauto. Qed.

(** Entailment applies to heap predicates, so they can be used to capture
    that a precondition is stronger than another one (i.e., that a 
    precondition entails another one). It is similarly interesting to 
    express that a postcondition is stronger than another one.

    For that purpose, we introduce [Q1 ===> Q2], which asserts that
    for any value [v], the heap predicate [Q1 v] entails [Q2 v]. 
 
    Equivalently, [Q1 ===> Q2] holds if for any value [v] and any heap [h],
    the proposition [Q1 v h] implies [Q2 v h]. *)

Definition qimpl (Q1 Q2:val->hprop) : Prop :=
  forall (v:val), Q1 v ==> Q2 v.

Notation "Q1 ===> Q2" := (qimpl Q1 Q2) (at level 55).

Lemma qimpl_refl : forall Q,
  Q ===> Q.
Proof using. intros Q v. applys himpl_refl. Qed.

Lemma qimpl_trans : forall Q2 Q1 Q3,
  (Q1 ===> Q2) ->
  (Q2 ===> Q3) ->
  (Q1 ===> Q3).
Proof using. introv M1 M2. intros v. applys himpl_trans; eauto. Qed.




(* ******************************************************* *)
(** ** Rule of consequence *)

(** A first use of the entailement relation is to state the
    consequence rule. We can prove the rule of consequence 
    directly with respect to the low level interpretation of
    Separation Logic triples. *)

Lemma triple_conseq : forall t H Q H' Q',
  triple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  triple t H Q.
Proof using.
  introv M WH WQ. rewrite triple_iff_triple_lowlevel in *.
  unfold triple_lowlevel in *. 
  intros h1 h2 D P1. lets P1': WH P1.
  lets M': M D P1'.
  destruct M' as (v&h1'&h3'&D'&R&HQ).
  exists v h1' h3'. splits~. applys WQ. auto.
Qed.


(* ******************************************************* *)
(** ** Extensionality for entailments *)

(** A second use of the entailment relation is to establish
    equalities between heap predicates. For example, we'd
    like to prove commutativity of separating conjunction:
    [(H1 \* H2) = (H2 \* H1)].

    As we are going to show next, to prove such an equality, 
    it suffices to prove that each side entails the other:
    [(H1 \* H2) ==> (H2 \* H1)] and [(H2 \* H1) ==> (H1 \* H2)].
    Note that this corresponds to the antisymmetry property 
    of entailment. *)

(** But wait a second, what does it mean to prove [H = H']
    where [H] and [H'] have type [hprop], that is, [heap->Prop]?
    We here wish to establish an equality between two predicates,
    by showing that each one implies the other. To that end, we
    need a reasoning principle that is not available by default
    in Coq, but can be safely added in the form of an axiom called
    "predicate extensionality". *)

Axiom predicate_extensionality : forall A (P Q:A->Prop),
  (forall x, P x <-> Q x) ->
  P = Q.

(* EX1! (himpl_antisym) *)
(** With this axiom, we can derive the antisymmetry of entailement. *)

Lemma himpl_antisym : forall H1 H2,
  (H1 ==> H2) ->
  (H2 ==> H1) ->
  H1 = H2.
Proof using.
(* SOLUTION *)
  introv M1 M2. applys predicate_extensionality.
  intros h. iff N. (* split *)
  { applys M1. auto. }
  { applys M2. auto. }
(* /SOLUTION *)
Qed.

(** Remark: heap entailment is reflexive, transitive, and
    antisymmetric. Thus, [==>] qualifies as an order relation. *)


(* ******************************************************* *)
(** ** Fundamental properties of Separation Logic operators *)

(** The fundamental properties of Separation Logic operators are
    described next. *)

(** (1) The star operator is associative. *)

Parameter hstar_assoc : forall H1 H2 H3,
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).

(** (2) The star operator is commutative. *)

Parameter hstar_comm : forall H1 H2,
   H1 \* H2 = H2 \* H1.

(** (3) The empty heap predicate is a neutral for the star.
    It is both a left and a right neutral, since star is commutative. *)

Parameter hstar_hempty_l : forall H,
  \[] \* H = H.

(** (4) Existentials can be "extruded" out of stars, that is:

      [(\exists x, H1) \* H2  =  \exists x, (H1 \* H2)].
      when [x] does not occur in [H2]. 

    The corresponding formal statement is as follows: *)

Parameter hstar_hexists : forall A (J:A->hprop) H,
  (hexists J) \* H = hexists (J \*+ H).

(** (5) Star is "regular" with respect to entailment. *)

Parameter himpl_frame_l : forall H2 H1 H1',
  H1 ==> H1' ->
  (H1 \* H2) ==> (H1' \* H2).

(** These properties are shared by essentially all variants of Separation
    Logic, and many generic results can be derived from these facts alone. *)

(** Remark: the star operator, together with the empty heap predicate,
    form a "commutative monoid structure". Moreover, the star is "regular"
    with respect to entailment and existentials. *)



(* ####################################################### *)
(** * Additional contents *)


(* ******************************************************* *)
(** ** Alternative proofs for the consequence rules. *)

(** It is simpler and more elegant to first establish
    the consequence rule for [Hoare_triple], then derive its
    generalization to the case of Separation Logic [triple]. *)


(* EX2! (Hoare_conseq) *)
(** Prove the consequence rule for Hoare triples. *)

Lemma Hoare_conseq : forall t H Q H' Q',
  Hoare_triple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  Hoare_triple t H Q.
Proof using.
(* SOLUTION *)
  introv M WH WQ. unfold Hoare_triple.
  intros s Hs. forwards (v&s'&R&HQ): M s.
  { applys WH. auto. }
  { exists v s'. split. { apply R. } { applys WQ. auto. } }
  (* variant proof script:
      intros s Ps. lets Ps': WH Ps.
      lets M': M Ps'. destruct M' as (v&s'&R&HQ).
      exists v s'. splits~. applys WQ. auto. *)
(* /SOLUTION *)
Qed.

(* EX2! (rule_conseq) *)
(** Prove the consequence rule by leveraging the lemma [Hoare_conseq],
    rather than going through the definition of [triple_lowlevel]. 
    Hint: apply lemma [Hoare_conseq] with the appropriate arguments,
    and use lemma [applys himpl_frame_l] to prove the entailments. *)

Lemma rule_conseq' : forall t H Q H' Q',
  triple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  triple t H Q.
Proof using.
(* SOLUTION *)
  introv M WH WQ. unfold triple. intros H''.
  applys Hoare_conseq M. 
  { applys himpl_frame_l. applys WH. }
  { intros x. applys himpl_frame_l. applys himpl_frame_l. applys WQ. }
(* /SOLUTION *)
Qed.


(* ******************************************************* *)
(** ** Proofs for the Separation Algebra *)

(** We next show the details of the proofs establishing the
    commutative monoid structure with the frame property.

    To establish the properties, we need to exploit a few
    basic facts about finite maps; we will introduce them as
    we go along. *)

(* EX1! (himpl_frame_l) *)
(** The simplest result to derive is the frame lemma for entailment. *)

Lemma himpl_frame_l' : forall H2 H1 H1',
  H1 ==> H1' ->
  (H1 \* H2) ==> (H1' \* H2).
Proof using. 
(* SOLUTION *)
  introv W (h1&h2&M1&M2&D&U). exists* h1 h2. 
(* /SOLUTION *)
Qed.

(* EX1! (himpl_frame_r) *)
(** State and prove a symmetric lemma to [himpl_frame_l] called [himpl_frame_r]
    to exploit an entailment on the right-hand-side of a star. *)

(* SOLUTION *)
Lemma himpl_frame_r : forall H1 H2 H2',
  H2 ==> H2' ->
  (H1 \* H2) ==> (H1 \* H2').
Proof using. 
  introv W. rewrite (hstar_comm H1 H2). rewrite (hstar_comm H1 H2').
  applys himpl_frame_l. auto.
Qed.
(* /SOLUTION *)

(** The second simplest result is the extrusion property for existentials. *)

Lemma hstar_hexists' : forall A (J:A->hprop) H,
  (hexists J) \* H = hexists (fun x => (J x) \* H).
Proof using.
  intros. applys himpl_antisym.
  { intros h (h1&h2&M1&M2&D&U). destruct M1 as (x&M1). exists~ x h1 h2. }
  { intros h (x&M). destruct M as (h1&h2&M1&M2&D&U). exists h1 h2. splits~. exists~ x. }
Qed.

(** To prove commutativity of star, we need to exploit the fact that 
    the union of two finite maps with disjoint domains commutes. *)

Check fmap_union_comm_of_disjoint : forall h1 h2,
  fmap_disjoint h1 h2 ->
  h1 \u h2 = h2 \u h1.

Lemma hstar_comm' : forall H1 H2,
   H1 \* H2 = H2 \* H1.
Proof using.
  asserts F: (forall H1 H2, H1 \* H2 ==> H2 \* H1).
  { intros. intros h (h1&h2&M1&M2&D&U). exists h2 h1.
    subst. splits~.
    { rewrite fmap_union_comm_of_disjoint; auto. } }
  intros. applys himpl_antisym. { applys F. } { applys F. }
Qed.

(** To prove that the empty heap predicate is a neutral for star,
    we need to exploit the fact that the union with an empty map
    is the identity. *)

Check fmap_union_empty_l : forall h, 
  fmap_empty \u h = h.

Lemma hstar_hempty_l' : forall H,
  \[] \* H = H.
Proof using.
  intros. applys himpl_antisym. 
  { intros h (h1&h2&M1&M2&D&U). hnf in M1. subst.
    rewrite @fmap_union_empty_l. auto. }
  { intros h M. exists (fmap_empty:heap) h. splits~.
    { hnf. auto. }
    { rewrite @fmap_union_empty_l. auto. } }
Qed.

(** The lemma showing that [\[]] is a left neutral can be derived
    from the previous result and commutativity. *)

Lemma hstar_hempty_r : forall H,
  H \* \[] = H.
Proof using.
  intros. rewrite hstar_comm'. rewrite hstar_hempty_l'. auto.
Qed.

(** Associativity of star is the most tedious result to derive.
    We need to exploit the associativity of union on finite maps,
    as well as lemmas about the disjointness of a map with the
    result of the union of two maps. *)

Check fmap_union_assoc : forall h1 h2 h3,
  (h1 \u h2) \u h3 = h1 \u (h2 \u h3).

Check fmap_disjoint_union_eq_l : forall h1 h2 h3,
    fmap_disjoint (h2 \u h3) h1 
  = (fmap_disjoint h1 h2 /\ fmap_disjoint h1 h3).

Check fmap_disjoint_union_eq_r : forall h1 h2 h3,
   fmap_disjoint h1 (h2 \u h3) 
 = (fmap_disjoint h1 h2 /\ fmap_disjoint h1 h3).

(* EX2! (hstar_assoc) *)
(** Complete the right-to-left part of the proof below. *)

Lemma hstar_assoc' : forall H1 H2 H3,
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).
Proof using.
  intros. applys himpl_antisym.
  { intros h (h'&h3&M1&M2&D&U). destruct M1 as (h1&h2&M3&M4&D'&U').
    subst h'. rewrite fmap_disjoint_union_eq_l in D.
    exists h1 (h2 \u h3). splits*.
    { exists* h2 h3. }
    { rewrite* @fmap_disjoint_union_eq_r. } 
    { rewrite* @fmap_union_assoc in U. } }
(* SOLUTION *)
  { intros h (h1&h'&M1&M2&D&U). destruct M2 as (h2&h3&M3&M4&D'&U').
    subst h'. rewrite fmap_disjoint_union_eq_r in D.
    exists (h1 \u h2) h3. splits*.
    { exists* h1 h2. }
    { rewrite* @fmap_disjoint_union_eq_l. } 
    { rewrite* @fmap_union_assoc. } }
(* /SOLUTION *)
Qed.


(* ******************************************************* *)
(** ** More on extensionality *)

(** To establish the antisymmetry of entailment, we have used
    the predicate extensionality axiom. In fact, this axiom is
    derivable from two more fundamental axioms. 

    The first axiom is "functional extensionality", which asserts
    that two functions are equal if they provide equal result
    for every argument. *)

Axiom functional_extensionality : forall A B (f g:A->B),
  (forall x, f x = g x) ->
  f = g.

(** The second axiom is "propositional extensionality", which asserts
    that two propositions that are logically equivalent (in the sense 
    that they imply each other) can be considered equal. *)

Axiom propositional_extensionality : forall (P Q:Prop),
  (P <-> Q) ->
  P = Q.

(* EX1! (predicate_extensionality_derived) *)
(** Using the above two axioms, show how to derive [predicate_extensionality]. *)

Lemma predicate_extensionality_derived : forall A (P Q:A->Prop),
  (forall x, P x <-> Q x) ->
  P = Q.
Proof using.
(* SOLUTION *)
  introv M. applys functional_extensionality.
  intros x. applys propositional_extensionality.
  applys M.
(* /SOLUTION *)
Qed.


(* ******************************************************* *)
(** ** Entailment lemmas for [\Top] *)

(* EX1! (himpl_htop_r) *)
(** Prove that any heap predicate entails [\Top] *)

Lemma himpl_htop_r : forall H,
  H ==> \Top.
Proof using. 
(* SOLUTION *)
  intros. intros h Hh.
  applys htop_intro. (* hnf; auto. *)
(* /SOLUTION *)
Qed.

(* EX2! (hstar_htop_htop) *)
(** Prove that [\Top \* \Top] is equivalent to [\Top] *)

Lemma hstar_htop_htop :
  \Top \* \Top = \Top.
Proof using.
(* SOLUTION *)
  applys himpl_antisym.
  { applys himpl_htop_r. }
  { rewrite <- hstar_hempty_l at 1. applys himpl_frame_l.
    applys himpl_htop_r. }
(* /SOLUTION *)
Qed.


(* ******************************************************* *)
(** ** Variants for the garbage collection rule *)

(** Recall the lemma [triple_htop_post]. *)

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

Lemma triple_htop_post_not_derived_from_triple_hany_post : forall t H Q,
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

    Technical remark: the previous remark can be mitigated. If we expose 
    that [triple t H Q <-> triple t' H Q] holds whenever [t] and [t']
    are observationally equivalent (with respect to the semantics 
    defined by [red]), and if we are able to prove that [let x = t in x]
    is observationally equivalent to [t] for some fresh variable x,
    then it is possible to prove that [triple_htop_post] is derivable
    from [triple_htop_pre]. (At a high-level, the postcondition of [t]
    can be viewed as the precondition of the [x] occuring in the 
    right-hand side of the term [let x = t in x].)  *)



(* ####################################################### *)
(** * Tactic support *)

(*
From Sep Require Import SepBase.
*)
























