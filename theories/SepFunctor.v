(**

This file formalizes a functor that may be instantiated con construct, e.g.
  -- a standard Separation Logic,
  -- a Separation Logic extended with credits,
  -- a Separation Logic extended with temporary read-only permissions.

The functor in this file assumes:
- a type for heaps
- a definition of \[P] (lifting of pure predicates) and of \* (star)
- five properties of these operators
  (neutral element, commutativity and associativity of star,
   extrusion of existentials, and frame property for entailment).

The functor also provides:

- derived heap operators: \[], (\exists _,_), \Top
- a number of useful lemmas for reasoning about these operators
- notation for representation predicates: [x ~> R X].

- [rew_heap] normalizes heap predicate expressions
- [hpull] extracts existentials and pure facts from LHS of entailments
- [hsimpl] simplifies heap entailments (it calls [hpull] first)
- [hhsimpl] uses [hsimpl] to solves goal of the form [X: H h, ... |- H' h]
- [hchange] performs transitivity steps in entailments, modulo frame

- [xpull] extracts existentials and pure facts from preconditions.
- [xchange] performs transitivity steps in preconditions.
- [xapply] applies a lemma (triple or characteristic formula) modulo
  frame and weakening.
- [xunfold] unfolds representation predicates of the form [x ~> R X]

- [xpulls] is like [xpull] but performs one substitution automatically.
- [xchanges] is like [xchange] but calls [hsimpl] to simplify subgoals.
- [xapplys] is like [xapply] but calls [hsimpl] to simplify subgoals.

- [mklocal F] is a predicate transformer used by characteristic formulae.
- [local F], where [F] is typically a triple or a characteristic formula,
  asserts that [F] can be subject to frame, weakening, and extraction
  of existentials and pure facts from preconditions. Tactics such as
  [xapply] apply the frame rule in a generic manner, and produce a
  [local] subgoal as side-condition.
- [xlocal] automatically discharges goals of the form [local F].

Author: Arthur Charguéraud, with contributions from Jacques-Henri Jourdan.
License: MIT.

*)

Set Implicit Arguments.
From TLC Require Export LibCore.
From Sep Require Export TLCbuffer Hsimpl.



(* ********************************************************************** *)
(** * Assumptions of the functor *)

Module Type SepCore.


(* ---------------------------------------------------------------------- *)
(* ** Representation of [hprop] *)

(** Type of heaps *)

Parameter heap : Type.

(** Type of heap predicates *)

Definition hprop := heap -> Prop.

(** Characterization of affine heaps: 
    the [haffine H] asserts that [H] only holds for affine heaps. *)

Parameter heap_affine : heap -> Prop.

Definition haffine (H : hprop) : Prop :=
  forall h, H h -> heap_affine h.


(* ---------------------------------------------------------------------- *)
(* ** Entailment *)

Definition himpl (H1 H2:hprop) : Prop :=
  forall (h:heap), H1 h -> H2 h.

Notation "H1 ==> H2" := (himpl H1 H2) (at level 55) : heap_scope.

Open Scope heap_scope.

Parameter himpl_refl : forall H,
  H ==> H.

Parameter himpl_trans : forall H2 H1 H3,
  (H1 ==> H2) ->
  (H2 ==> H3) ->
  (H1 ==> H3).

Parameter himpl_antisym : forall H1 H2,
  (H1 ==> H2) ->
  (H2 ==> H1) ->
  H1 = H2.

Definition qimpl A (Q1 Q2:A->hprop) : Prop :=
  forall (v:A), Q1 v ==> Q2 v.

Notation "Q1 ===> Q2" := (qimpl Q1 Q2) (at level 55) : heap_scope.


(* ---------------------------------------------------------------------- *)
(* ** Core operators *)

(** Abstract predicates *)

Parameter hempty : hprop.

Parameter hstar : hprop -> hprop -> hprop.

(** Concrete predicates *)

Definition hexists A (J:A->hprop) : hprop :=
  fun h => exists x, J x h.

Definition hforall (A : Type) (J : A -> hprop) : hprop :=
  fun h => forall x, J x h.

(** Notation to state the properties *)

Notation "\[]" := (hempty)
  (at level 0) : heap_scope.

Notation "H1 '\*' H2" := (hstar H1 H2)
  (at level 41, right associativity) : heap_scope.

Notation "Q \*+ H" := (fun x => hstar (Q x) H)
  (at level 40) : heap_scope.


(* ---------------------------------------------------------------------- *)
(* ** Core properties *)

(** Empty is left neutral for star *)

Parameter hstar_hempty_l : forall H,
  \[] \* H = H.

(** Star is commutative *)

Parameter hstar_comm : forall H1 H2,
   H1 \* H2 = H2 \* H1.

(** Star is associative *)

Parameter hstar_assoc : forall H1 H2 H3,
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).

(** Extrusion of existentials out of star *)

Parameter hstar_hexists : forall A (J:A->hprop) H,
  (hexists J) \* H = hexists (fun x => (J x) \* H).

(** Extrusion of foralls out of star *)

Parameter hstar_hforall : forall H A (J:A->hprop),
  (hforall J) \* H ==> hforall (J \*+ H).

(** The frame property (star on H2) holds for entailment *)

Parameter himpl_frame_l : forall H2 H1 H1',
  H1 ==> H1' ->
  (H1 \* H2) ==> (H1' \* H2).

(** Properties of haffine *)

Parameter haffine_hempty :
  haffine \[].

Parameter haffine_hstar : forall H1 H2,
  haffine H1 ->
  haffine H2 ->
  haffine (H1 \* H2).

End SepCore.



(* ********************************************************************** *)
(** * Definition of heap predicates *)

Module SepSetup (SH : SepCore).

Module HsimplArgs.

Include SH.

Hint Resolve himpl_refl.

Open Scope heap_scope.

Implicit Types h : heap.
Implicit Types H : hprop.
Implicit Types P : Prop.

(* ---------------------------------------------------------------------- *)
(* ** Additional notation for core predicates *)

(** Notation for [hexists] *)

Notation "'\exists' x1 .. xn , H" :=
  (hexists (fun x1 => .. (hexists (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\exists' '/ '  x1  ..  xn , '/ '  H ']'") : heap_scope.

(** Notation for [hforall] *)

Notation "'\forall' x1 .. xn , H" :=
  (hforall (fun x1 => .. (hforall (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\forall' '/ '  x1  ..  xn , '/ '  H ']'") : heap_scope.


(* ---------------------------------------------------------------------- *)
(* ** Derived heap predicates *)

(** Pure propositions lifted to heap predicates,
  written [ \[P] ].

  Remark: the definition below is equivalent to
  [fun h => (hempty h /\ P)]. *)

Definition hpure (P:Prop) : hprop :=
  hexists (fun (p:P) => hempty).

Notation "\[ P ]" := (hpure P)
  (at level 0, format "\[ P ]") : heap_scope.

(** The "Top" predicate, written [\Top], which holds of any heap,
  implemented as [\exists H, H]. *)

Definition htop : hprop :=
  hexists (fun (H:hprop) => H).

Notation "\Top" := (htop) : heap_scope.

(** The "GC" predicate, written [\GC], which holds of any heap,
  implemented as [\exists H, \[affine H] \* H]. *)

Definition hgc : hprop :=
  \exists H, \[haffine H] \* H.

Notation "\GC" := (hgc) : heap_scope.

(** Magic wand, written [H1 \-* H2] *)

Definition hwand (H1 H2 : hprop) : hprop :=
  hexists (fun (H:hprop) => H \* (hpure (H \* H1 ==> H2))).

Notation "H1 \-* H2" := (hwand H1 H2)
  (at level 43, right associativity) : heap_scope.

(** Magic wand for postconditions, written [Q1 \--* Q2] *)

Definition qwand A (Q1 Q2:A->hprop) :=
  hforall (fun x => hwand (Q1 x) (Q2 x)).

Notation "Q1 \--* Q2" := (qwand Q1 Q2)
  (at level 43) : heap_scope.

Open Scope heap_scope.
Delimit Scope heap_scope with hprop.

(** Disjunction, equivalent to [fun h => H1 h \/ H2 h] *)

Definition hor (H1 H2 : hprop) : hprop :=
  \exists (b:bool), if b then H1 else H2.

(** Non-separating conjunction, equivalent to [fun h => H1 h /\ H2 h] *)

Definition hand (H1 H2 : hprop) : hprop :=
  \forall (b:bool), if b then H1 else H2.

(** Affinity for postconditions *)

Definition haffine_post (A:Type) (J:A->hprop) : Prop :=
  forall x, haffine (J x).


(* ---------------------------------------------------------------------- *)
(* ** Notation for triples *)

(** Notation [F PRE H POST Q] for stating specifications, e.g.
    [triple t PRE H POST Q] is the same as [triple t H Q] *)

Notation "F 'PRE' H 'POST' Q" :=
  (F H Q)
  (at level 69, only parsing) : heap_scope_ext.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [hprop] *)

Global Instance hinhab : Inhab hprop.
Proof using. intros. apply (Inhab_of_val hempty). Qed.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [himpl] *)

Lemma himpl_inv : forall H1 H2 h,
  (H1 ==> H2) ->
  (H1 h) ->
  (H2 h).
Proof using. auto. Qed.

(** Additional notation for entailment
    [H1 ==+> H2] is short for [H1 ==> H1 \* H2] *)

Notation "H1 ==+> H2" := (H1%hprop ==> H1%hprop \* H2%hprop)
  (at level 55, only parsing) : heap_scope_ext.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [hstar] *)

Lemma hstar_hempty_r : forall H,
  H \* \[] = H.
Proof using.
  applys neutral_r_of_comm_neutral_l.
  applys~ hstar_comm.
  applys~ hstar_hempty_l.
Qed.

(* ---------------------------------------------------------------------- *)
(** Properties of [hpure] *)

Lemma hstar_hpure : forall P H h, 
  (\[P] \* H) h = (P /\ H h).
Proof using.
  intros. extens. unfold hpure.
  rewrite hstar_hexists.
  rewrite* hstar_hempty_l.
  iff (p&M) (p&M). { split~. } { exists~ p. }
Qed.

  (* corollary only used for the SL course *)
Lemma hstar_hpure_iff : forall P H h,
  (\[P] \* H) h <-> (P /\ H h).
Proof using. intros. rewrite* hstar_hpure. Qed.

Lemma himpl_hstar_hpure_r : forall P H H',
  P ->
  (H ==> H') ->
  H ==> (\[P] \* H').
Proof using.
  introv HP W. intros h K. rewrite* hstar_hpure.
  (* derivable, nevertheless useful to have here...
  introv HP W. rewrite <- (hstar_hempty_l H).
  applys himpl_frame_lr W. applys~ himpl_hempty_hpure. *)
Qed.

Lemma hpure_inv_hempty : forall P h,
  \[P] h ->
  P /\ \[] h.
Proof using.
  introv M. rewrite <- hstar_hpure.
  rewrite~ hstar_hempty_r.
Qed.

Lemma hpure_intro_hempty : forall P h,
  \[] h ->
  P ->
  \[P] h.
Proof using.
  introv M N. rewrite <- (hstar_hempty_l \[P]).
  rewrite hstar_comm. rewrite~ hstar_hpure.
Qed.

Lemma himpl_hempty_hpure : forall P,
  P ->
  \[] ==> \[P].
Proof using. introv HP. intros h Hh. applys* hpure_intro_hempty. Qed.

Lemma himpl_hstar_hpure_l : forall P H H',
  (P -> H ==> H') ->
  (\[P] \* H) ==> H'.
Proof using.
  introv W Hh. rewrite hstar_hpure in Hh. applys* W.
Qed.

Lemma hempty_eq_hpure_true :
  \[] = \[True].
Proof using.
  applys pred_ext_1. intros h. iff M.
  { applys* hpure_intro_hempty. }
  { forwards*: hpure_inv_hempty M. }
Qed.

Lemma hfalse_hstar_any : forall H,
  \[False] \* H = \[False].
Proof using.
  intros. applys pred_ext_1. intros h. rewrite hstar_hpure. iff M.
  { false*. } { lets: hpure_inv_hempty M. false*. }
Qed.

Lemma hpure_eq_hexists_empty : forall P,
  \[P] = (\exists (p:P), \[]).
Proof using. auto. Qed.


(* ---------------------------------------------------------------------- *)
(** Properties of hexists *)

Lemma hexists_intro : forall A (x:A) (J:A->hprop) h,
  J x h ->
  (hexists J) h.
Proof using. intros. exists~ x. Qed.

Lemma hexists_inv : forall A (J:A->hprop) h,
  (hexists J) h ->
  exists x, J x h.
Proof using. intros. destruct H as [x H]. exists~ x. Qed.

Lemma himpl_hexists_l : forall A H (J:A->hprop),
  (forall x, J x ==> H) ->
  (hexists J) ==> H.
Proof using. introv W. intros h (x&Hh). applys* W. Qed.

Lemma himpl_hexists_r : forall A (x:A) H J,
  (H ==> J x) ->
  H ==> (hexists J).
Proof using. introv W. intros h. exists x. apply~ W. Qed.

Lemma himpl_hexists : forall A (J1 J2:A->hprop),
  J1 ===> J2 ->
  hexists J1 ==> hexists J2.
Proof using.
  introv W. applys himpl_hexists_l. intros x. applys himpl_hexists_r W.
Qed.


(* ---------------------------------------------------------------------- *)
(** Properties of hforall *)

Lemma himpl_hforall_r : forall A (J:A->hprop) H,
  (forall x, H ==> J x) ->
  H ==> (hforall J).
Proof using. introv M. intros h Hh x. apply~ M. Qed.

Lemma himpl_hforall_l : forall A x (J:A->hprop) H,
  (J x ==> H) ->
  (hforall J) ==> H.
Proof using. introv M. intros h Hh. apply~ M. Qed.

Lemma himpl_hforall_l_exists : forall A (J:A->hprop) H,
  (exists x, J x ==> H) ->
  (hforall J) ==> H.
Proof using. introv (x&M). applys* himpl_hforall_l. Qed.

Lemma himpl_hforall : forall A (J1 J2:A->hprop),
  J1 ===> J2 ->
  hforall J1 ==> hforall J2.
Proof using.
  introv W. applys himpl_hforall_r. intros x. applys himpl_hforall_l W.
Qed.

Lemma hforall_specialize : forall A (x:A) (J:A->hprop),
  (hforall J) ==> (J x).
Proof using. intros. applys* himpl_hforall_l x. Qed.


(* ---------------------------------------------------------------------- *)
(** Properties of hwand (others are found further in the file) *)

Lemma hwand_equiv : forall H0 H1 H2,
  (H0 ==> H1 \-* H2) <-> (H0 \* H1 ==> H2).
Proof using.
  unfold hwand. iff M.
  { applys himpl_trans. applys himpl_frame_l M.
    (* applys himpl_hstar_trans_l (rm M). *)
    rewrite hstar_hexists. applys himpl_hexists_l. intros H.
    rewrite (hstar_comm H). rewrite hstar_assoc.
    applys~ himpl_hstar_hpure_l. }
  { applys himpl_hexists_r H0. 
    rewrite hstar_comm. rewrite <- (hstar_hempty_l H0) at 1.
    applys himpl_frame_l. applys himpl_hempty_hpure M. }
Qed.

Lemma himpl_hwand_r : forall H1 H2 H3,
  H1 \* H2 ==> H3 ->
  H1 ==> (H2 \-* H3).
Proof using. introv M. rewrite~ hwand_equiv. Qed.

Lemma himpl_hwand_r_inv : forall H1 H2 H3,
  H1 ==> (H2 \-* H3) ->
  H1 \* H2 ==> H3.
Proof using. introv M. rewrite~ <- hwand_equiv. Qed.


(* ---------------------------------------------------------------------- *)
(** Properties of qwand *)

Lemma qwand_equiv : forall H A (Q1 Q2:A->hprop),
  H ==> (Q1 \--* Q2) <-> (Q1 \*+ H) ===> Q2.
Proof using.
  unfold qwand. iff M.
  { intros x. rewrite hstar_comm. applys himpl_trans.
    applys himpl_frame_l M. applys himpl_trans. applys hstar_hforall.
    applys himpl_hforall_l x. rewrite <- hwand_equiv. applys himpl_refl. }
  { applys himpl_hforall_r. intros x.
    rewrite hwand_equiv. rewrite* hstar_comm. }
Qed.

Lemma himpl_qwand_r : forall A (Q1 Q2:A->hprop) H,
  Q1 \*+ H ===> Q2 ->
  H ==> (Q1 \--* Q2).
Proof using. introv M. rewrite~ qwand_equiv. Qed.

Arguments himpl_qwand_r [A].


(* ---------------------------------------------------------------------- *)
(** Properties of htop *)

Lemma htop_intro : forall h,
  \Top h.
Proof using. intros. exists~ (=h). Qed.

Lemma himpl_htop_r : forall H,
  H ==> \Top.
Proof using. intros. intros h Hh. applys* htop_intro. Qed.

Lemma htop_eq :
  \Top = (\exists H, H).
Proof using. auto. Qed.


(* ---------------------------------------------------------------------- *)
(* ** Properties of affine predicates *)

Lemma haffine_eq : forall H,
  haffine H = (forall h, H h -> heap_affine h).
Proof using. auto. Qed.

Lemma haffine_hexists : forall A (J:A->hprop),
  haffine_post J ->
  haffine (hexists J).
Proof using. introv F1 (x&Hx). applys* F1. Qed.

Lemma haffine_hforall : forall A `{Inhab A} (J:A->hprop),
  haffine_post J ->
  haffine (hforall J).
Proof using. introv IA F1 Hx. applys* F1 arbitrary. Qed.

Lemma haffine_hpure : forall P,
  haffine \[P].
Proof using.
  intros. applys* haffine_hexists. intros HP. applys* haffine_hempty.
Qed.

Lemma haffine_hgc :
  haffine \GC.
Proof using.
  applys haffine_hexists. intros H h Hh. rewrite hstar_hpure in Hh.
  destruct Hh as [M N]. applys* M.
Qed.



(* ---------------------------------------------------------------------- *)
(** Properties of hgc *)

Lemma hgc_eq :
  \GC = (\exists H, \[haffine H] \* H).
Proof using. auto. Qed.

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

Lemma hstar_hgc_hgc :
  \GC \* \GC = \GC. (* TODO : can be simplified *)
Proof using.
  applys himpl_antisym.
  { applys himpl_hgc_r. applys haffine_hstar; applys haffine_hgc. }
  { rewrite <- hstar_hempty_l at 1. applys himpl_frame_l. applys hempty_himpl_hgc. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [hor] *)

Lemma hor_sym : forall H1 H2,
  hor H1 H2 = hor H2 H1.
Proof using.
  intros. unfold hor. applys himpl_antisym.
  { applys himpl_hexists_l. intros b.
    applys himpl_hexists_r (neg b). destruct* b. }
  { applys himpl_hexists_l. intros b.
    applys himpl_hexists_r (neg b). destruct* b. }
Qed.

Lemma himpl_hor_r_r : forall H1 H2,
  H1 ==> hor H1 H2.
Proof using. intros. unfolds hor. exists* true. Qed.

Lemma himpl_hor_r_l : forall H1 H2,
  H2 ==> hor H1 H2.
Proof using. intros. unfolds hor. exists* false. Qed.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [hand] *)

Lemma hand_sym : forall H1 H2,
  hand H1 H2 = hand H2 H1.
Proof using.
  intros. unfold hand. applys himpl_antisym.
  { applys himpl_hforall_r. intros b.
    applys himpl_hforall_l (neg b). destruct* b. }
  { applys himpl_hforall_r. intros b.
    applys himpl_hforall_l (neg b). destruct* b. }
Qed.

Lemma himpl_hand_l_r : forall H1 H2,
  hand H1 H2 ==> H1.
Proof using. intros. unfolds hand. applys* himpl_hforall_l true. Qed.

Lemma himpl_hand_l_l : forall H1 H2,
  hand H1 H2 ==> H2.
Proof using. intros. unfolds hand. applys* himpl_hforall_l false. Qed.

Lemma himpl_hand_r : forall H1 H2 H3,
  H1 ==> H2 ->
  H1 ==> H3 ->
  H1 ==> hand H2 H3.
Proof using. introv M1 M2 Hh. intros b. case_if*. Qed.



End HsimplArgs.

Export HsimplArgs.

Module Import HS := HsimplSetup(HsimplArgs).

(* ---------------------------------------------------------------------- *)
(* ** Set operators to be opaque *)

Global Opaque hempty hpure hstar hexists htop hgc haffine.



(* ********************************************************************** *)
(* * More properties of the magic wand *)

(* ---------------------------------------------------------------------- *)
(* ** Properties of [hwand] *)

Lemma hwand_eq_hexists_hstar_hpure : forall H1 H2,
  (H1 \-* H2) = (\exists H, H \* \[H \* H1 ==> H2]).
Proof using. auto. Qed.

Lemma hwand_himpl : forall H1 H1' H2 H2',
  H1' ==> H1 ->
  H2 ==> H2' ->
  (H1 \-* H2) ==> (H1' \-* H2').
Proof using. introv M1 M2. hsimpl. hchange~ M1. Qed.

Lemma hwand_himpl_r : forall H1 H2 H2',
  H2 ==> H2' ->
  (H1 \-* H2) ==> (H1 \-* H2').
Proof using. introv M. applys~ hwand_himpl. Qed.

Lemma hwand_himpl_l : forall H1' H1 H2,
  H1' ==> H1 ->
  (H1 \-* H2) ==> (H1' \-* H2).
Proof using. introv M. applys* hwand_himpl. Qed.

Lemma hwand_hpure_r_intro : forall H1 H2 (P:Prop),
  (P -> H1 ==> H2) ->
  H1 ==> (\[P] \-* H2).
Proof using. introv M. applys himpl_hwand_r. hsimpl*. Qed.

Lemma hstar_hwand : forall H1 H2 H3,
  (H1 \-* H2) \* H3 ==> H1 \-* (H2 \* H3).
Proof using.
  hsimpl.
Qed.
  (* intros. unfold hwand. hsimpl ;=> H4 M. hchanges M. 
  unfold hwand. hsimpl ;=> H4 M. *)

Arguments hstar_hwand : clear implicits.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [qwand] *)

Lemma himpl_qwand_r_inv : forall H A (Q1 Q2:A->hprop),
  H ==> (Q1 \--* Q2) ->
  (Q1 \*+ H) ===> Q2.
Proof using. introv M. rewrite~ <- qwand_equiv. Qed.

Lemma hstar_qwand : forall H A (Q1 Q2:A->hprop),
  (Q1 \--* Q2) \* H ==> Q1 \--* (Q2 \*+ H).
Proof using. hsimpl.
(*
  intros. unfold qwand. hchanges hstar_hforall.
  applys himpl_hforall. intros x.
  hchanges hstar_hwand.
*)
Qed.

Lemma qwand_cancel : forall A (Q1 Q2:A->hprop),
  Q1 \*+ (Q1 \--* Q2) ===> Q2.
Proof using. hsimpl. Qed.
(*
  intros. intros x.
  hchange (qwand_specialize x Q1 Q2).
  hchanges (hwand_cancel (Q1 x)).
*)

Lemma qwand_cancel_part : forall H A (Q1 Q2:A->hprop),
  H \* ((Q1 \*+ H) \--* Q2) ==> (Q1 \--* Q2).
Proof using.
  intros. applys himpl_qwand_r. intros x.
  hchange (qwand_specialize x). 
Qed.

Lemma qwand_himpl : forall A (Q1 Q1' Q2 Q2':A->hprop),
  Q1' ===> Q1 ->
  Q2 ===> Q2' ->
  (Q1 \--* Q2) ==> (Q1' \--* Q2').
Proof using.
  introv M1 M2. applys himpl_hforall_r. intros x.
  applys himpl_hforall_l x. applys* hwand_himpl.
Qed.

Lemma qwand_himpl_l : forall A (Q1 Q1' Q2:A->hprop),
  Q1' ===> Q1 ->
  (Q1 \--* Q2) ==> (Q1' \--* Q2).
Proof using. introv M. applys* qwand_himpl. Qed.

Lemma qwand_himpl_r : forall A (Q1 Q2 Q2':A->hprop),
  Q2 ===> Q2' ->
  (Q1 \--* Q2) ==> (Q1 \--* Q2').
Proof using. introv M. applys* qwand_himpl. Qed.



(* ********************************************************************** *)
(* * Tactics for heap entailments *)

(* ---------------------------------------------------------------------- *)
(** Specific cleanup for formulaes *)

Ltac on_formula_pre cont :=
  match goal with
  | |- _ ?H ?Q => cont H
  | |- _ _ ?H ?Q => cont H
  | |- _ _ _ ?H ?Q => cont H
  | |- _ _ _ _ ?H ?Q => cont H
  | |- _ _ _ _ _ ?H ?Q => cont H
  | |- _ _ _ _ _ _ ?H ?Q => cont H
  | |- _ _ _ _ _ _ _ ?H ?Q => cont H
  | |- _ _ _ _ _ _ _ _ ?H ?Q => cont H
  | |- _ _ _ _ _ _ _ _ _ ?H ?Q => cont H
  | |- _ _ _ _ _ _ _ _ _ _ ?H ?Q => cont H
  end.

Ltac on_formula_post cont :=
  match goal with
  | |- _ ?H ?Q => cont Q
  | |- _ _ ?H ?Q => cont Q
  | |- _ _ _ ?H ?Q => cont Q
  | |- _ _ _ _ ?H ?Q => cont Q
  | |- _ _ _ _ _ ?H ?Q => cont Q
  | |- _ _ _ _ _ _ ?H ?Q => cont Q
  | |- _ _ _ _ _ _ _ ?H ?Q => cont Q
  | |- _ _ _ _ _ _ _ _ ?H ?Q => cont Q
  | |- _ _ _ _ _ _ _ _ _ ?H ?Q => cont Q
  | |- _ _ _ _ _ _ _ _ _ _ ?H ?Q => cont Q
  end.

Ltac remove_empty_heaps_formula tt :=
  repeat (on_formula_pre ltac:(remove_empty_heaps_from)).


(* ---------------------------------------------------------------------- *)
(* ** Tactic [haffine] simplifies a goal [haffine H] using structural
      rules. It may be extended to support custom extensions. *)

Ltac haffine_custom tt :=
  fail.

(* example extension:

  Ltac haffine_custom tt ::=
    repeat match goal with
    | |- haffine (hcredits _) => apply affine_credits; auto with zarith
    end.

*)

Ltac haffine_step tt :=
  match goal with 
  | |- haffine_post (_) => intros ? (* todo: interesting to have? *)
  | |- haffine ?H =>
    match H with
    | (hempty) => apply haffine_hempty
    | (hpure _) => apply haffine_hpure
    | (hstar _ _) => apply haffine_hstar
    | (hgc) => apply haffine_hgc
    | (hexists _) => apply haffine_hexists
    | (hforall _) => apply haffine_hforall
    | ?H' => haffine_custom tt
    | _ => try assumption
    end
  end.

Ltac haffine_core tt ::=
  repeat (haffine_step tt).

Tactic Notation "haffine" :=
  haffine_core tt.
Tactic Notation "haffine" "~" :=
  haffine; auto_tilde tt.
Tactic Notation "haffine" "*" :=
  haffine; auto_star tt.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [hhsimpl] to prove [H h] from [H' h] *)

(** [hhsimpl] applies to a goal of the form [H h].
   It looks up for an hypothesis of the form [H' h],
   where [H'] is a heap predicate (whose type is syntactically [hprop]).
   It then turns the goal into [H ==> H'], and calls [hsimpl].

   This tactic is very useful for establishing the soundness of
   Separation Logic derivation rules. It should never be used in
   the verification of concrete programs, since a heap [h] should
   never appear explicitly in such a proof, all the reasoning being
   conducted at the level of heap predicates. *)

Ltac hhsimpl_core tt :=
  match goal with N: ?H ?h |- _ ?h =>
    match type of H with hprop =>
    applys himpl_inv N; clear N; hsimpl
  end end.

Tactic Notation "hhsimpl" := hhsimpl_core tt.
Tactic Notation "hhsimpl" "~" := hhsimpl; auto_tilde.
Tactic Notation "hhsimpl" "*" := hhsimpl; auto_star.


(* ********************************************************************** *)
(** * Predicate [local] *)

(* ---------------------------------------------------------------------- *)
(* ** Definition of [local] *)

(** Type of characteristic formulae on values of type B *)

Notation "'~~' B" := (hprop->(B->hprop)->Prop)
  (at level 8, only parsing) : type_scope.

(** A formula [F] is mklocal (e.g. [F] could be the predicate SL [triple])
    if it is sufficient for establishing [F H Q] to establish that the
    the formula holds on a subheap, in the sense that [F H1 Q1] with
    [H = H1 \* H2] and [Q = Q1 \*+ H2]. 
    (Technically, we add an extra [\GC] in to capture the affinity of the logic.) *)

Definition local B (F:~~B) : Prop :=
  forall H Q, 
    (H ==> \exists H1 H2 Q1, H1 \* H2 \*
             \[F H1 Q1 /\ Q1 \*+ H2 ===> Q \*+ \GC]) ->
    F H Q.

(** [local_pred S] asserts that [local (S x)] holds for any [x].
    It is useful for describing loop invariants. *)

Definition local_pred A B (S:A->~~B) :=
  forall x, local (S x).


(* ---------------------------------------------------------------------- *)
(* ** Properties of [local] *)

Implicit Type P : Prop.
Implicit Type H : hprop.

(** Remark: for conciseness, we abbreviate names of lemmas,
    e.g. [local_inv_frame] is named [mklocal_conseq_frame]. *)

Section IsLocal.

Variables (B : Type).
Implicit Types (F : ~~B).
Hint Resolve haffine_hempty.

(** A introduction rule to establish [local], exposing the definition *)

Lemma local_intro : forall F,
  (forall H Q, 
    (H ==> \exists H1 H2 Q1, H1 \* H2 \*
             \[F H1 Q1 /\ Q1 \*+ H2 ===> Q \*+ \GC]) ->
    F H Q) ->
  local F.
Proof using. auto. Qed.

(** An elimination rule for [local] *)

Lemma local_elim : forall F H Q,
  local F ->
  (H ==> \exists H1 H2 Q1, H1 \* H2 \* \[F H1 Q1 /\ Q1 \*+ H2 ===> Q \*+ \GC]) ->
  F H Q.
Proof using. auto. Qed.

(** An elimination rule for [local] without [htop] *)

Lemma local_elim_frame : forall F H Q,
  local F ->
  (H ==> \exists H1 H2 Q1, H1 \* H2 \* \[F H1 Q1 /\ Q1 \*+ H2 ===> Q]) ->
  F H Q.
Proof using. 
  introv L M. applys~ local_elim. hchange M.
  hpull ;=> H1 H2 Q1 (N1&N2). hsimpl H1 H2 Q1. split~.
  hchanges~ N2.
Qed.

(** An elimination rule for [local] specialized for no frame, and no [htop] *)

Lemma local_elim_conseq_pre : forall F H Q,
  local F ->
  (H ==> \exists H1, H1 \* \[F H1 Q]) ->
  F H Q.
Proof using.
  introv L M. applys~ local_elim_frame. hchange M.
  hpull ;=> H1 N. hsimpl H1 \[] Q. splits*. hsimpl.
Qed.

(** Weaken and frame and gc property [mklocal] *)

Lemma local_conseq_frame_hgc : forall F H H1 H2 Q1 Q,
  local F ->
  F H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q \*+ \GC ->
  F H Q.
Proof using.
  introv L M WH WQ. applys~ local_elim. hchange WH.
  hsimpl~ H1 H2 Q1.
Qed.

(** Weaken and frame properties from [mklocal] *)

Lemma local_conseq_frame : forall H1 H2 Q1 F H Q,
  local F ->
  F H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q ->
  F H Q.
Proof using.
  introv L M WH WQ. applys* local_conseq_frame_hgc M. hchanges~ WQ.
Qed.

(** Frame rule *)

Lemma local_frame : forall H2 Q1 H1 F,
  local F ->
  F H1 Q1 ->
  F (H1 \* H2) (Q1 \*+ H2).
Proof using. introv L M. applys~ local_conseq_frame M. Qed.

(** Ramified frame rule *)

Lemma local_ramified_frame : forall Q1 H1 F H Q,
  local F ->
  F H1 Q1 ->
  H ==> H1 \* (Q1 \--* Q) ->
  F H Q.
Proof using.
  introv L M WH. applys~ local_conseq_frame (Q1 \--* Q) M.
  hsimpl.
Qed.

(** Ramified frame rule with \GC *)

Lemma local_ramified_frame_hgc : forall Q1 H1 F H Q,
  local F ->
  F H1 Q1 ->
  H ==> H1 \* (Q1 \--* Q \*+ \GC) ->
  F H Q.
Proof using.
  introv L M WH. applys~ local_conseq_frame_hgc (Q1 \--* Q \*+ \GC) M.
  hsimpl.
Qed.

(** Consequence rule *)

Lemma local_conseq : forall H' Q' F H Q,
  local F ->
  F H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  F H Q.
Proof using.
  introv L M WH WQ. applys* local_conseq_frame_hgc \[] M. 
  { hsimpl*. } { hchanges WQ. }
Qed.

(** Garbage collection on precondition from [mklocal] *)

Lemma local_hgc_pre : forall F H Q,
  local F ->
  F H Q ->
  F (H \* \GC) Q.
Proof using. introv L M. applys~ local_conseq_frame_hgc M. Qed.

Lemma local_conseq_pre_hgc : forall H' F H Q,
  local F ->
  H ==> H' \* \GC ->
  F H' Q ->
  F H Q.
Proof using. introv L WH M. applys* local_conseq_frame_hgc M. Qed.

(** Garbage collection on postcondition from [mklocal] *)

Lemma local_hgc_post : forall F H Q,
  local F ->
  F H (Q \*+ \GC) ->
  F H Q.
Proof using. introv L M. applys* local_conseq_frame_hgc \[] M; hsimpl. Qed.

Lemma local_conseq_post_hgc : forall Q' F H Q,
  local F ->
  F H Q' ->
  Q' ===> Q \*+ \GC ->
  F H Q.
Proof using.
  introv L M WQ. applys* local_conseq_frame_hgc \[] M.
  { hsimpl. } { hchanges WQ. }
Qed.

(** Variant of the above, useful for tactics to specify
    the garbage collected part *)

Lemma local_hgc_pre_on : forall HG H' F H Q,
  local F ->
  haffine HG ->
  H ==> HG \* H' ->
  F H' Q ->
  F H Q.
Proof using. introv L K WH M. applys~ local_conseq_pre_hgc M. hchanges~ WH. Qed.

(** Weakening on pre and post with gc-post from [mklocal] *)

Lemma local_conseq_hgc_post : forall H' Q' F H Q,
  local F ->
  F H' Q' ->
  H ==> H' ->
  Q' ===> Q \*+ \GC ->
  F H Q.
Proof using.
  introv L M WH WQ. applys~ local_conseq_frame_hgc \[] M.
  { hchanges WH. } { hchanges WQ. }
Qed.

(** Weakening on pre and post with gc-pre from [mklocal] *)

Lemma local_conseq_hgc_pre : forall H' Q' F H Q,
  local F ->
  F H' Q' ->
  H ==> H' \* \GC ->
  Q' ===> Q ->
  F H Q.
Proof using.
  introv L M WH WQ. applys~ local_conseq_frame_hgc \GC M.
  { hchanges WQ. }
Qed.

(** Weakening on pre from [mklocal] *)

Lemma local_conseq_pre : forall H' F H Q,
  local F ->
  F H' Q ->
  H ==> H' ->
  F H Q.
Proof using. introv L M WH. applys* local_conseq M. Qed.

(** Weakening on post from [mklocal] *)

Lemma local_conseq_post : forall Q' F H Q,
  local F ->
  F H Q' ->
  Q' ===> Q ->
  F H Q.
Proof using. introv L M WQ. applys* local_conseq M. Qed.

(** Extraction of pure facts from [mklocal] *)

Lemma local_hpure : forall F H P Q,
  local F ->
  (P -> F H Q) ->
  F (\[P] \* H) Q.
Proof using.
  introv L M. applys~ local_elim_conseq_pre. hpull ;=> HP. hsimpl~ H.
Qed.

(** Extraction of existentials from [mklocal] *)

Lemma local_hexists : forall F A (J:A->hprop) Q,
  local F ->
  (forall x, F (J x) Q) ->
  F (hexists J) Q.
Proof using.
  introv L M. applys~ local_elim_conseq_pre. hpull ;=> x. hsimpl* (J x).
Qed.

(** Extraction of existentials below a star from [mklocal] *)

Lemma local_hstar_hexists : forall F H A (J:A->hprop) Q,
  local F ->
  (forall x, F ((J x) \* H) Q) ->
   F (hexists J \* H) Q.
Proof using.
  introv L M. rewrite hstar_hexists. applys~ local_hexists.
Qed.

(** Extraction of forall from [mklocal] *)

Lemma local_hforall : forall A (x:A) F (J:A->hprop) Q,
  local F ->
  F (J x) Q ->
  F (hforall J) Q.
Proof using.
  introv L M. applys~ local_elim_conseq_pre.
  applys himpl_hforall_l x. hsimpl~ (J x).
Qed.

Lemma local_hforall_exists : forall F A (J:A->hprop) Q,
  local F ->
  (exists x, F (J x) Q) ->
  F (hforall J) Q.
Proof using. introv L (x&M). applys* local_hforall. Qed.

(** Extraction of forall below a star from [mklocal] *)
(* TODO needed? *)

Lemma local_hstar_hforall_l : forall F H A (J:A->hprop) Q,
  local F ->
  (exists x, F ((J x) \* H) Q) ->
  F (hforall J \* H) Q.
Proof using.
  introv L (x&M). 
  applys local_conseq_pre; [ auto | | applys hstar_hforall ].
  (* TODO: fix level for notation \forall and \hstar, so that parentheses show up *)
  (* above line same as: xchanges hstar_hforall. *)
  applys* local_hforall.
Qed.

(** Case analysis for [hor] *)

Lemma local_hor : forall F H1 H2 Q,
  local F ->
  F H1 Q ->
  F H2 Q ->
  F (hor H1 H2) Q.
Proof using. introv L M1 M2. apply* local_hexists. intros b. case_if*. Qed.

(** Left branch for [hand] *)

Lemma local_hand_l : forall F H1 H2 Q,
  local F ->
  F H1 Q ->
  F (hand H1 H2) Q.
Proof using. introv L M1. applys* local_hforall true. Qed.

(** Right branch for [hand] *)

Lemma local_hand_r : forall F H1 H2 Q,
  local F ->
  F H2 Q ->
  F (hand H1 H2) Q.
Proof using. introv L M1. applys* local_hforall false. Qed.

(** Extraction of heap representation from [mklocal] *)

Lemma local_name_heap : forall F H Q,
  local F ->
  (forall h, H h -> F (= h) Q) ->
  F H Q.
Proof using.
  introv L M. applys~ local_elim_conseq_pre.
  intros h Hh. exists (= h). rewrite hstar_comm.
  applys* himpl_hstar_hpure_r (= h).
Qed.

(** Extraction of pure facts from the precondition under local *)

Lemma local_prop : forall F H Q P,
  local F ->
  (H ==> H \* \[P]) ->
  (P -> F H Q) ->
  F H Q.
Proof using.
  introv L WH M. applys~ local_elim_conseq_pre.
  hchanges WH. rew_heap~.
Qed.

(** Extraction of proof obligations from the precondition under local *)

Lemma local_hwand_hpure_l : forall F (P:Prop) H Q,
  local F ->
  P ->
  F H Q ->
  F (\[P] \-* H) Q.
Proof using.
  introv L HP M. applys~ local_elim_conseq_pre. hchanges~ hwand_hpure_l_intro.
Qed.

End IsLocal.

Global Opaque local.


(* ********************************************************************** *)
(** * Definition of the predicate transformer [mklocal] *)
(* TODO needed? *)

(** Remark: this section might be specific to old-style characteristic formulae *)

(** The [mklocal] predicate is a predicate transformer that allows
    to turn a formula into a mklocal formula. *)

Definition mklocal B (F:~~B) : ~~B :=
  fun (H:hprop) (Q:B->hprop) =>
    H ==> \exists H1 H2 Q1,
       H1 \* H2 \* \[F H1 Q1 /\ Q1 \*+ H2 ===> Q \*+ \GC].

Section Local.
Transparent local.
Variables (B:Type).
Implicit Types (F:~~B).

(** The [mklocal] operator can be freely erased from a conclusion *)

Lemma mklocal_erase : forall F H Q,
  F H Q ->
  mklocal F H Q.
Proof using.
  introv M. unfold mklocal. hsimpl H \[]. splits*. hsimpl.
Qed.

(** [mklocal] is idempotent, i.e. nested applications
   of [mklocal] are redundant *)

Lemma mklocal_mklocal : forall F,
  mklocal (mklocal F) = mklocal F.
Proof using.
  extens. intros H Q. iff M.
  { unfold mklocal. eapply himpl_trans; [apply M|]. hpull ;=> H1 H2 Q1 [P1 P2].
    unfold mklocal in P1. hchange P1. hpull ;=> H1' H2' Q1' [P1' P2'].
    hsimpl H1' (H2 \* H2') Q1'. splits*.
    intros x. hchanges P2'. hchange P2. }
  { apply~ mklocal_erase. }
Qed.

(** The predicate [mklocal] satisfies [local] *)

Lemma local_mklocal : forall F,
  local (mklocal F).
Proof using. introv M. rewrite <- mklocal_mklocal. applys M. Qed.

(** A [mklocal] can be introduced at the head of a formula satisfying [local] *)

Lemma eq_mklocal_of_local : forall F,
  local F -> 
  F = mklocal F.
Proof using.
  introv L. applys pred_ext_2. intros H Q. iff M.
  { applys~ mklocal_erase. }
  { applys~ local_elim. }
Qed.

(** [mklocal] is a covariant transformer w.r.t. predicate inclusion *)

Notation "Q1 ===>' Q2" := (forall x y, Q1 x y -> Q2 x y) (at level 55).

Lemma mklocal_weaken : forall F F',
  F ===>' F' ->
  mklocal F ===>' mklocal F'.
Proof using.
  unfold mklocal. introv M. intros H Q N. hchange (rm N) ;=> H1 H2 Q' [P1 P2]. 
  hsimpl H1 H2 Q'. split~. (* applys~ M. *)
Qed.

(** Extraction of contradictions from the precondition under mklocal *)

Lemma mklocal_false : forall F H Q,
  mklocal F H Q ->
  (forall H' Q', F H' Q' -> False) ->
  (H ==> \[False]).
Proof using.
  introv M N. hchange M. hpull ;=> H' H1 Q' [HF _]. false* N.
Qed.

End Local.


(* ********************************************************************** *)
(* * Tactics for triples and characteristic formulae *)

(* ---------------------------------------------------------------------- *)
(* ** Tactic [xlocal] to prove side-conditions of the form [mklocal F]. *)

Ltac xlocal_base tt :=
  auto 1.

(* e.g.
Ltac xlocal_base tt ::=
  try first [ applys local_mklocal ].
*)

Ltac xlocal_unfold_pred tt :=
  try match goal with |- local_pred ?S =>
    let r := fresh "TEMP" in intros r end.

Ltac xlocal_core tt :=
  try first [ assumption | xlocal_unfold_pred tt; xlocal_base tt ].

Tactic Notation "xlocal" :=
  xlocal_core tt.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xpull_check] tests whether it would be useful
      to call [xpull] to extract things from the precondition.
      Applies to a goal of the form [F H Q]. *)

Ltac xpull_check tt := (* DEPRECATED *)
  idtac.
(* 
  let H := xprecondition tt in
  hpull_check_rec H.
*)

(* ---------------------------------------------------------------------- *)
(* ** Tactic [xpull] to extract existentials and pure facts from
      preconditions. *)

(** [xpull] plays a similar role to [hpull], except that it works on
   goals of the form [F H Q], where [F] is typically a triple predicate
   or a characteristic formula.

   [xpull] simplifies the precondition [H] as follows:
   - it removes empty heap predicates
   - it pulls pure facts out as hypotheses into the context
   - it pulls existentials as variables into the context.

   At the end, it regeneralizes in the goals the new variables
   from the context, so as to allow the user to introduce them
   by giving appropriate names. *)


(** Lemmas *)

Lemma xpull_start : forall B (F:~~B) H Q,
  F (\[] \* H) Q -> 
  F H Q.
Proof using. intros. rew_heap in *. auto. Qed.

Lemma xpull_keep : forall B (F:~~B) H1 H2 H3 Q,
  F ((H2 \* H1) \* H3) Q -> 
  F (H1 \* (H2 \* H3)) Q.
Proof using. intros. rewrite (hstar_comm H2) in H. rew_heap in *. auto. Qed.

Lemma xpull_assoc : forall B (F:~~B) H1 H2 H3 H4 Q,
  F (H1 \* (H2 \* (H3 \* H4))) Q ->
  F (H1 \* ((H2 \* H3) \* H4)) Q.
Proof using. intros. rew_heap in *. auto. Qed.

Lemma xpull_starify : forall B (F:~~B) H1 H2 Q,
  F (H1 \* (H2 \* \[])) Q -> 
  F (H1 \* H2) Q.
Proof using. intros. rew_heap in *. auto. Qed.

Lemma xpull_empty : forall B (F:~~B) H1 H2 Q,
  (F (H1 \* H2) Q) -> 
  F (H1 \* (\[] \* H2)) Q.
Proof using. intros. rew_heap. auto. Qed.

Lemma xpull_hpure : forall B (F:~~B) H1 H2 P Q,
  local F -> 
  (P -> F (H1 \* H2) Q) ->
  F (H1 \* (\[P] \* H2)) Q.
Proof using.
  intros. rewrite hstar_comm_assoc. apply~ local_hpure.
Qed.

Lemma xpull_id : forall A (x X : A) B (F:~~B) H1 H2 Q,
  local F -> 
  (x = X -> F (H1 \* H2) Q) -> 
  F (H1 \* (x ~> Id X \* H2)) Q.
Proof using. intros. unfold Id. apply~ xpull_hpure. Qed.

Lemma xpull_hexists : forall B (F:~~B) H1 H2 A (J:A->hprop) Q,
  local F ->
  (forall x, F (H1 \* ((J x) \* H2)) Q) ->
   F (H1 \* (hexists J \* H2)) Q.
Proof using.
  intros. rewrite hstar_comm_assoc. apply~ local_hstar_hexists.
  intros. rewrite~ hstar_comm_assoc.
Qed.

(*
Lemma xpull_hwand_hpure_l : forall B (F:~~B) H1 H2 (P:Prop) Q,
  local F ->
  (P -> F (H1 \* H2) Q) ->
   F (H1 \* (\[P] \-* H2)) Q.
*)

Ltac hpull_xpull_iris_hook tt := idtac.

Ltac xpull_setup tt :=
  pose ltac_mark;
  intros;
  try match goal with |- ?H ==> ?H' =>
        fail 100 "you should call hpull, not xpull" end;
  hpull_xpull_iris_hook tt;
  apply xpull_start.

Ltac xpull_post_processing_for_hyp H :=
  idtac.

Ltac xpull_cleanup tt :=
  remove_empty_heaps_formula tt;
  gen_until_mark_with_processing ltac:(xpull_post_processing_for_hyp).

Ltac xpull_hpure tt :=
  apply xpull_hpure; [ try xlocal | intro ].
Ltac xpull_hexists tt :=
  apply xpull_hexists; [ try xlocal | intro ].
Ltac xpull_id tt :=
  apply xpull_id; [ try xlocal | intro ].

Ltac xpull_step tt :=
  let go HP :=
    match HP with _ \* ?HN =>
    match HN with
    | ?H \* _ =>
      match H with
      | \[] => apply xpull_empty
      | \[_] => xpull_hpure tt
      | hexists _ => xpull_hexists tt
      | _ ~> Id _ => xpull_id tt
      | _ \* _ => apply xpull_assoc
      | _ => apply xpull_keep
      end
    | \[] => fail 1
    | _ => apply xpull_starify
    end end in
  on_formula_pre ltac:(go).

Ltac xpull_main tt :=
  xpull_setup tt;
  (repeat (xpull_step tt));
  xpull_cleanup tt.

Tactic Notation "xpull" := xpull_main tt.
Tactic Notation "xpull" "~" := xpull; auto_tilde.
Tactic Notation "xpull" "*" := xpull; auto_star.

(* Demo *)

Lemma xpull_demo_1 : forall H1 H2 A (P:A->Prop) (J:A->hprop) B (F:~~B) (Q:B->hprop),
  local F ->
  F (H1 \* \exists x, (J x \* H2 \* \[P x])) Q.
Proof using.
  introv L. dup.
  { xpull_setup tt.
    xpull_step tt.
    xpull_step tt.
    xpull_step tt.
    xpull_step tt.
    xpull_step tt.
    xpull_step tt.
    xpull_step tt.
    xpull_step tt.
    xpull_cleanup tt. demo. }
  { xpull. demo. }
Abort.


(* ---------------------------------------------------------------------- *)
(** Auxiliary tactics used by some tactics *)

(* [xprecondition tt] returns the current precondition. *)

Ltac xprecondition tt :=
  match goal with |- ?R ?H ?Q => constr:(H) end.

(* [xpostcondition tt] returns the current postcondition. *)

Ltac xpostcondition tt :=
  match goal with |- ?E =>
  match get_fun_arg E with (_,?Q) => constr:(Q)
  end end.
  (* LATER: is this now equivalent to:
     match goal with |- ?J ?Q => constr:(Q) end. *)

(** [xpostcondition_is_evar tt] returns a boolean indicating
    whether the postcondition of the current goal is an evar. *)

Ltac xpostcondition_is_evar tt :=
  let Q := xpostcondition tt in
  is_evar_as_bool Q.


(* ---------------------------------------------------------------------- *)
(* ** [xapply] and [xapplys] *)

(** [xapply E] applies a lemma [E] modulo frame/weakening.
    It applies to a goal of the form [F H Q], and replaces it
    with [F ?H' ?Q'], applies [E] to the goal, then produces
    the side condition [H ==> ?H'] and,
    - if [Q] is instantiated, then leaves [?Q' ===> Q \* \GC]
    - otherwise it instantiates [Q] with [Q'].

    [xapplys E] is like [xapply E] but also attemps to simplify
    the subgoals using [hsimpl].
*)

Ltac xapply_core H cont1 cont2 :=
  forwards_nounfold_then H ltac:(fun K =>
    match xpostcondition_is_evar tt with
    | true => eapply local_conseq_frame; [ xlocal | sapply K | cont1 tt | try apply qimpl_refl ]
    | false => eapply local_conseq_frame_hgc; [ xlocal | sapply K | cont1 tt | cont2 tt ]
    end).

Ltac xapply_base H :=
  xpull_check tt;
  xapply_core H ltac:(fun tt => idtac) ltac:(fun tt => idtac).

Ltac xapplys_base H :=
  xpull_check tt;
  xapply_core H ltac:(fun tt => hsimpl) ltac:(fun tt => hsimpl).

Tactic Notation "xapply" constr(H) :=
  xapply_base H.
Tactic Notation "xapply" "~" constr(H) :=
  xapply H; auto_tilde.
Tactic Notation "xapply" "*" constr(H) :=
  xapply H; auto_star.

Tactic Notation "xapplys" constr(H) :=
  xapplys_base H.
Tactic Notation "xapplys" "~" constr(H) :=
  xapplys H; auto_tilde.
Tactic Notation "xapplys" "*" constr(H) :=
  xapplys H; auto_star.


(* Demo *)

Lemma xapply_demo_1 : forall H1 H2 H3 B (F:~~B) (Q1:B->hprop),
  local F ->
  F H1 Q1 ->
  H2 ==> H3 ->
  F (H2 \* H1) (Q1 \*+ H3).
Proof using.
  introv L M HW. dup.
  { xapply M. hsimpl. hchanges HW. }
  { xapplys M. hchanges HW. }
Abort.


(*--------------------------------------------------------*)
(* ** [xchange] *)

(** [xchange E] applies to a goal of the form [F H Q]
    and to a lemma [E] of type [H1 ==> H2] or [H1 = H2].
    It replaces the goal with [F H' Q], where [H']
    is computed by replacing [H1] with [H2] in [H].

    The substraction is computed by solving [H ==> H1 \* ?H']
    with [hsimpl]. If you need to solve this implication by hand,
    use [xchange_no_simpl E] instead.

    [xchange <- E] is useful when [E] has type [H2 = H1]
      instead of [H1 = H2].

    [xchange_show E] is useful to visualize the instantiation
    of the lemma used to implement [xchange].
    *)

(* Lemma used by [xchange] *)

Lemma xchange_lemma : forall H1 H1' H2 B H Q (F:~~B),
  local F ->
  (H1 ==> H1') ->
  (H ==> H1 \* H2) ->
  F (H1' \* H2) Q ->
  F H Q.
Proof using.
  introv W1 L W2 M. applys local_conseq_frame __ \[]; eauto.
  hsimpl. hchange~ W2. hsimpl~. rew_heap~.
Qed.

Ltac xchange_apply L cont1 cont2 :=
   eapply xchange_lemma;
     [ try xlocal | applys L | cont1 tt | cont2 tt (*xtag_pre_post*) ].

(* Note: the term modif should be either himpl_of_eq or himpl_of_eq_sym *)
Ltac xchange_forwards L modif cont1 cont2 :=
  forwards_nounfold_then L ltac:(fun K =>
  match modif with
  | __ =>
     match type of K with
     | _ = _ => xchange_apply (@himpl_of_eq _ _ _ K) cont1 cont2
     | _ => xchange_apply K cont1 cont2
     end
  | _ => xchange_apply (@modif _ _ _ K) cont1 cont2
  end).

Ltac xchange_with_core cont1 cont2 H H' :=
  eapply xchange_lemma with (H1:=H) (H1':=H');
    [ try xlocal | | cont1 tt | cont2 tt (* xtag_pre_post*)  ].

Ltac xchange_core cont1 cont2 E modif :=
  match E with
  | ?H ==> ?H' => xchange_with_core cont1 cont2 H H'
  | _ => xchange_forwards E modif
          ltac:(fun _ => instantiate; cont1 tt)
          ltac:(fun _ => instantiate; cont2 tt)
  end.

Ltac xchange_base cont1 cont2 E modif :=
  xpull_check tt;
  match goal with
  | |- _ ==> _ => hchange_core E modif ltac:(hchange_hsimpl_cont) cont2
  | |- _ ===> _ => hchange_core E modif ltac:(hchange_hsimpl_cont) cont2
  | _ => xchange_core cont1 cont2 E modif
  end.

Ltac hpull_or_xpull tt :=
  match goal with
  | |- _ ==> _ => hpull
  | |- _ ===> _ => hpull
  | |- _ => xpull
  end.

Tactic Notation "xchange" constr(E) :=
  xchange_base ltac:(fun tt => hsimpl) ltac:(idcont) E __.
Tactic Notation "xchange" "~" constr(E) :=
  xchange E; auto_tilde.
Tactic Notation "xchange" "*" constr(E) :=
  xchange E; auto_star.

Tactic Notation "xchange" "<-" constr(E) :=
  xchange_base ltac:(fun tt => hsimpl) ltac:(idcont) E himpl_of_eq_sym.
Tactic Notation "xchange" "~" "<-" constr(E) :=
  xchange <- E; auto_tilde.
Tactic Notation "xchange" "*" "<-" constr(E) :=
  xchange <- E; auto_star.

Tactic Notation "xchanges" constr(E) :=
  xchange_base ltac:(fun tt => hsimpl) ltac:(fun tt => hpull_or_xpull tt) E __.
Tactic Notation "xchanges" "~" constr(E) :=
  xchanges E; auto_tilde.
Tactic Notation "xchanges" "*" constr(E) :=
  xchanges E; auto_star.

Tactic Notation "xchange_no_simpl" constr(E) :=
  xchange_base ltac:(idcont) ltac:(idcont)E __.
Tactic Notation "xchange_no_simpl" "<-" constr(E) :=
  xchange_base ltac:(idcont) E himpl_of_eq_sym.

Tactic Notation "xchange_show" constr(E) :=
  xchange_forwards E __ ltac:(idcont) ltac:(idcont).
Tactic Notation "xchange_show" "<-" constr(E) :=
  xchange_forwards himpl_of_eq_sym ltac:(idcont) ltac:(idcont).


(* Demo *)

Lemma xchange_demo_1 : forall H1 H1' H2 B (F:~~B) (Q:B->hprop),
  local F ->
  H1 ==> H1' ->
  F (H2 \* H1) Q.
Proof using.
  introv L M. xchange M.
Abort.


(* ********************************************************************** *)
(* * Weakest-preconditions *)

(* ---------------------------------------------------------------------- *)
(* ** Definition of the weakest precondition for a formula *)

Definition weakestpre (B : Type) (F:hprop->(B->hprop)->Prop) (Q:B->hprop) : hprop :=
  \exists (H:hprop), H \* \[F H Q].

Lemma weakestpre_eq : forall B (F:~~B) H Q,
  local F -> (* in fact, only requires weaken-pre and extract-hexists rules to hold *)
  F H Q = (H ==> weakestpre F Q).
Proof using.
  introv L. applys prop_ext. unfold weakestpre. iff M.
  { hsimpl. rew_heap~. }
  { applys~ local_conseq_pre M. xpull~. }
Qed.

Lemma weakestpre_conseq : forall B (F:~~B) Q1 Q2,
  local F ->
  Q1 ===> Q2 ->
  weakestpre F Q1 ==> weakestpre F Q2.
Proof using.
  introv L W. unfold weakestpre. hpull ;=> H1 M. hsimpl~.
  xapply M. hsimpl. hsimpl. hchanges W.
Qed.

Lemma weakestpre_conseq_wand : forall B (F:~~B) Q1 Q2, 
  local F ->
  (Q1 \--* Q2) \* weakestpre F Q1 ==> weakestpre F Q2.
Proof using.
  introv L. unfold weakestpre. hpull ;=> H1 M.
  hsimpl (H1 \* (Q1 \--* Q2)). xapplys M.
Qed.

Lemma weakestpre_frame : forall B (F:~~B) H Q,
  local F ->
  (weakestpre F Q) \* H ==> weakestpre F (Q \*+ H).
Proof using.
  introv L. unfold weakestpre. hpull ;=> H1 M.
  hsimpl (H1 \* H). xapplys M.
Qed.

Lemma weakestpre_absorb : forall B (F:~~B) Q,
  local F ->
  weakestpre F Q \* \GC ==> weakestpre F Q.
Proof using.
  introv L. unfold weakestpre. hpull ;=> H1 M.
  hsimpl~ (H1 \* \GC). xapplys M.
Qed.

Lemma weakestpre_pre : forall B (F:~~B) Q,
  local F ->
  F (weakestpre F Q) Q.
Proof using. intros. unfold weakestpre. xpull ;=> H'. auto. Qed.

Lemma himpl_weakestpre : forall B (F:~~B) H Q,
  F H Q ->
  H ==> weakestpre F Q.
Proof using. introv M. unfold weakestpre. hsimpl~ H. Qed.


(* ********************************************************************** *)
(* * Tactics for representation predicates *)

(* ---------------------------------------------------------------------- *)
(* ** Tactic [xunfold] to unfold heap predicates *)

(** For technical reasons, on a heap predicate [x ~> R X],
  and due to the opacity of the arrow (needed to avoid undesired
  simplifications), a call to [unfold R] does not perform the
  desired unfolding of the representation predicate [R] in the
  form [Rbody X x], but instead leaves something of the
  form [x ~> (fun x' => Rbody X x')]. The latter is  logically
  equivalent to [(fun x' => Rbody X x') x)] and thus to [Rbody X x],
  but it does not simplify by [simpl] as desired.

  The tactic [xunfold] is meant for performing the desired
  unfolding. Its implementation is a bit of a hack, due to limitations
  of [rewrite], which does not work smoothly under binders, and
  fails to properly identify the beta-redex that could be simplified. *)


(** [xunfold at n] unfold the definition of the arrow [~>]
    at the occurence [n] in the goal. *)

Definition repr' (A:Type) (S:A->hprop) (x:A) : hprop := S x.

Ltac xunfold_at_core n :=
  let h := fresh "temp" in
  ltac_set (h := repr) at n;
  change h with repr';
  unfold repr';
  clear h.

Tactic Notation "xunfold" "at" constr(n) :=
  xunfold_at_core n.

(** [xunfold E] unfolds all occurences of the representation
    predicate [E].
    Limitation: won't work if E has more than 12 arguments.

    Implementation: converts all occurences of repr to repr',
    then unfolds these occurences one by one, and considers
    them for unfolding. *)

Ltac xunfold_arg_core E :=
  let E := get_head E in (* to get rid of typeclasses arguments *)
  change repr with repr';
  let h := fresh "temp" in
  set (h := repr');
  repeat (
    unfold h at 1;
    let ok := match goal with
      | |- context [ repr' (E) _ ] => constr:(true)
      | |- context [ repr' (E _) _ ] => constr:(true)
      | |- context [ repr' (E _ _) _ ] => constr:(true)
      | |- context [ repr' (E _ _ _) _ ] => constr:(true)
      | |- context [ repr' (E _ _ _ _) _ ] => constr:(true)
      | |- context [ repr' (E _ _ _ _ _) _ ] => constr:(true)
      | |- context [ repr' (E _ _ _ _ _ _) _ ] => constr:(true)
      | |- context [ repr' (E _ _ _ _ _ _ _) _ ] => constr:(true)
      | |- context [ repr' (E _ _ _ _ _ _ _ _) _ ] => constr:(true)
      | |- context [ repr' (E _ _ _ _ _ _ _ _ _) _ ] => constr:(true)
      | |- context [ repr' (E _ _ _ _ _ _ _ _ _ _) _ ] => constr:(true)
      | |- context [ repr' (E _ _ _ _ _ _ _ _ _ _ _) _ ] => constr:(true)
      | |- context [ repr' (E _ _ _ _ _ _ _ _ _ _ _ _) _ ] => constr:(true)
      | _ => constr:(false)
      end in
    match ok with
    | true => unfold repr'
    | false => change repr' with repr
    end);
  clear h;
  first [ progress (simpl E) | unfold E ].

Tactic Notation "xunfold" constr(E) :=
  xunfold_arg_core E.
Tactic Notation "xunfold" "~" constr(E) := xunfold E; auto_tilde.
Tactic Notation "xunfold" "*" constr(E) := xunfold E; auto_star.

(** [xunfold E] unfolds a specific occurence of the representation
    predicate [E]. *)

Ltac xunfold_arg_at_core E n :=
  let E := get_head E in (* to get rid of typeclasses arguments *)
  let n := number_to_nat n in
  change repr with repr';
  let h := fresh "temp" in
  set (h := repr');
  let E' := fresh "tempR" in
  set (E' := E);
  let rec aux n :=
    try (
      unfold h at 1;
      let ok := match goal with
        | |- context [ repr' (E') _ ] => constr:(true)
        | |- context [ repr' (E' _) _ ] => constr:(true)
        | |- context [ repr' (E' _ _) _ ] => constr:(true)
        | |- context [ repr' (E' _ _ _) _ ] => constr:(true)
        | |- context [ repr' (E' _ _ _ _) _ ] => constr:(true)
        | |- context [ repr' (E' _ _ _ _ _) _ ] => constr:(true)
        | |- context [ repr' (E' _ _ _ _ _ _) _ ] => constr:(true)
        | |- context [ repr' (E' _ _ _ _ _ _ _) _ ] => constr:(true)
        | |- context [ repr' (E' _ _ _ _ _ _ _ _) _ ] => constr:(true)
        | |- context [ repr' (E' _ _ _ _ _ _ _ _ _) _ ] => constr:(true)
        | |- context [ repr' (E' _ _ _ _ _ _ _ _ _ _) _ ] => constr:(true)
        | |- context [ repr' (E' _ _ _ _ _ _ _ _ _ _ _) _ ] => constr:(true)
        | |- context [ repr' (E' _ _ _ _ _ _ _ _ _ _ _ _) _ ] => constr:(true)
        | _ => constr:(false)
        end in
      match ok with
      | true =>
         match n with
         | (S O)%nat =>
            (* unfold repr' *)
            match goal with
            | |- context [ repr' (E') ?p ] =>
                change (repr' (E') p) with (E p)
            | |- context [ repr' (E' ?x1) ?p ] =>
                change (repr' (E' x1) p) with (E x1 p)
            | |- context [ repr' (E' ?x1 ?x2) ?p ] =>
                change (repr' (E' x1 x2) p) with (E x1 x2 p)
            | |- context [ repr' (E' ?x1 ?x2 ?x3) ?p ] =>
                change (repr' (E' x1 x2 x3) p) with (E x1 x2 x3 p)
            | |- context [ repr' (E' ?x1 ?x2 ?x3 ?x4) ?p ] =>
                change (repr' (E' x1 x2 x3 x4) p) with (E x1 x2 x3 x4 p)
            | |- context [ repr' (E' ?x1 ?x2 ?x3 ?x4 ?x5) ?p ] =>
                change (repr' (E' x1 x2 x3 x4 x5) p) with (E x1 x2 x3 x4 x5 p)
            | |- context [ repr' (E' ?x1 ?x2 ?x3 ?x4 ?x5 ?x6) ?p ] =>
                change (repr' (E' x1 x2 x3 x4 x5 x6) p) with (E x1 x2 x3 x4 x5 x6 p)
            | |- context [ repr' (E' ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7) ?p ] =>
                change (repr' (E' x1 x2 x3 x4 x5 x6 x7) p) with (E x1 x2 x3 x4 x5 x6 x7 p)
            | |- context [ repr' (E' ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8) ?p ] =>
                change (repr' (E' x1 x2 x3 x4 x5 x6 x7 x8) p) with (E x1 x2 x3 x4 x5 x6 x7 x8 p)
            | |- context [ repr' (E' ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9) ?p ] =>
                change (repr' (E' x1 x2 x3 x4 x5 x6 x7 x8 x9) p) with (E x1 x2 x3 x4 x5 x6 x7 x8 x9 p)
           end;
            first [ progress (simpl E) | unfold E ]
         | (S ?n')%nat => change repr' with repr; aux n'
         end
      | false => change repr' with repr; aux n
      end)
     in
  aux n;
  unfold h;
  clear h;
  change repr' with repr;
  unfold E';
  clear E'.

Tactic Notation "xunfold" constr(E) "at" constr(n) :=
  xunfold_arg_at_core E n.

Ltac xunfolds_post tt :=
  first [ hpull | xpull ].

Tactic Notation "xunfolds" "at" constr(n) :=
  xunfold at n; xunfolds_post tt.

Tactic Notation "xunfolds" constr(E) :=
  xunfold E; xunfolds_post tt.

Tactic Notation "xunfolds" constr(E) "at" constr(n) :=
  xunfold E at n; xunfolds_post tt.


(* ---------------------------------------------------------------------- *)
(* ** Set [repr] to be opaque *)

Global Opaque repr.

End SepSetup.
