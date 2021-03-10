(**

This file formalizes characteristic formulae in weakest-precondition form
for lifted Separation Logic.

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)


Set Implicit Arguments.
From CFML Require Export WPBase SepLifted.
Import LibListExec.RewListExec.
Open Scope heap_scope.
Generalizable Variables A.

Implicit Types v w : val.
Implicit Types t : trm.



(* ********************************************************************** *)
(* * WP generator *)

(* ---------------------------------------------------------------------- *)
(* ** Type of a WP *)

(** A formula is a predicate over a post-condition. *)

Definition Formula := forall A (EA:Enc A), (A -> hprop) -> hprop.

Global Instance Inhab_Formula : Inhab Formula.
Proof using. apply (Inhab_of_val (fun _ _ _ => \[])). Qed.

Declare Scope wp_scope.
Open Scope wp_scope.
Delimit Scope wp_scope with wp.

Notation "^ F Q" := ((F:Formula) _ _ Q)
  (at level 45, F at level 0, Q at level 0,
   format "^ F  Q") : wp_scope.


(* ---------------------------------------------------------------------- *)
(* ** Semantic interpretation of a WP *)

(** Lifted version of [weakestpre] *)

Definition Weakestpre (T:forall `{Enc A},hprop->(A->hprop)->Prop) : Formula :=
  fun A (EA:Enc A) => weakestpre T.

(** Lifted version of [wp] *)

Definition Wp (t:trm) : Formula :=
  Weakestpre (@Triple t).

(** Lifted version of [wpsubst E t] *)

Definition Wpsubst (E:ctx) (t:trm) : Formula :=
  Wp (isubst E t).


(* ---------------------------------------------------------------------- *)
(* ** Definition of [MkStruct] for WP *)

(** The [MkStruct] predicate lifts [mkstruct]. *)

Definition MkStruct (F:Formula) : Formula :=
  fun A (EA:Enc A) (Q:A->hprop) => mkstruct (@F A EA) Q.

Lemma mkstruct_MkStruct_eq : forall A `{EA:Enc A} (F:Formula),
  mkstruct (@MkStruct F A EA) = (@MkStruct F A EA).
Proof using.
  intros. apply fun_ext_1. intros Q.
  unfold MkStruct. rewrite mkstruct_mkstruct. split~.
Qed.

Lemma structural_MkStruct : forall A `{EA:Enc A} (F:Formula),
  structural (@MkStruct F A EA).
Proof using. intros. rewrite <- mkstruct_MkStruct_eq. apply structural_mkstruct. Qed.

Hint Resolve structural_MkStruct.

(** The predicate [Structural] lifts [structural] *)

Definition Structural (F:Formula) : Prop :=
  forall A (EA:Enc A), structural (@F A EA).

Lemma Structural_Mkstruct : forall (F:Formula),
  Structural (MkStruct F).
Proof using. intros. intros A EA. applys structural_mkstruct. Qed.

(** A [MkStruct] can be introduced at the head of a formula satisfying [Struct] *)

Lemma eq_Mkstruct_of_Structural : forall (F:Formula),
  Structural F ->
  F = MkStruct F.
Proof using.
  introv L. applys fun_ext_3. intros A EA Q.
  unfold MkStruct. rewrite* <- eq_mkstruct_of_structural.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Tag for improved pretty-printing of CF *)

Definition Wptag (F:Formula) : Formula := F.

Notation "'`' F" :=
  ((Wptag F%wp))
  (at level 69, F at level 100, format "'`' F") : wp_scope.


(* ---------------------------------------------------------------------- *)
(* ** Combinators to force the type of an argument or a return value *)

(** Constructor to force the return type of a Formula *)

Definition Formula_cast `{Enc A1} (F:(A1->hprop)->hprop) : Formula :=
  fun A2 (EA2:Enc A2) (Q:A2->hprop) =>
    \exists (Q':A1->hprop), F Q' \* \[Q' ===> Post_cast A1 Q].


(* ---------------------------------------------------------------------- *)
(* ** Definition of CF blocks *)

(** These auxiliary definitions give the characteristic formula
    associated with each term construct. *)

Definition Wpgen_fail : Formula :=
  MkStruct (fun A (EA:Enc A) Q =>
    \[False]).


Definition Wpgen_val (v:val) : Formula :=
  MkStruct (fun A (EA:Enc A) Q => Post_cast_val Q v).

Definition Wpgen_Val_no_mkstruct A1 `{EA1:Enc A1} (V:A1) : Formula :=
  fun A2 (EA2:Enc A2) Q => Post_cast A1 Q V.

Definition Wpaux_var (E:ctx) (x:var) : Formula :=
  match Ctx.lookup x E with
  | None => `Wpgen_fail
  | Some v => `Wpgen_val v
  end.

Definition Wpgen_let (F1:Formula) (F2of:forall A1 (EA1:Enc A1), A1->Formula) : Formula :=
  MkStruct (fun A (EA:Enc A) Q =>
    \exists (A1:Type) (EA1:Enc A1),
      ^F1 (fun (X:A1) => ^(F2of _ _ X) Q)).

Definition Wpgen_let_typed (F1:Formula) `{EA1:Enc A1} (F2of:A1->Formula) : Formula :=
  MkStruct (fun A (EA:Enc A) Q =>
    ^F1 (fun (X:A1) => ^(F2of X) Q)).

Definition Wpgen_seq (F1 F2:Formula) : Formula :=
  MkStruct (fun A (EA:Enc A) Q =>
    ^F1 (fun (X:unit) => ^F2 Q)).

Definition Wpaux_getval Wpgen (E:ctx) (t1:trm) (F2of:val->Formula) : Formula :=
  match t1 with
  | trm_val v => F2of v
  | trm_var x => match Ctx.lookup x E with
                 | Some v => F2of v
                 | None => `Wpgen_fail
                 end
  | _ => `Wpgen_let (Wpgen E t1) (fun A1 (EA1:Enc A1) (V1:A1) => F2of (``V1))
  end.

Definition Wpaux_getval_typed Wpgen (E:ctx) (t1:trm) `{EA1:Enc A1} (F2of:A1->Formula) : Formula :=
  match t1 with
  | trm_val v => `Wpgen_let_typed (`Wpgen_val v) F2of
  | trm_var x => match Ctx.lookup x E with
                 | Some v => `Wpgen_let_typed (`Wpgen_val v) F2of
                 | None => `Wpgen_fail
                 end
  | _ => `Wpgen_let_typed (Wpgen E t1) F2of
  end.

Definition Wpaux_constr Wpgen (E:ctx) (id:idconstr) : list val -> list trm -> Formula :=
  fix mk (rvs : list val) (ts : list trm) : Formula :=
    match ts with
    | nil => `Wpgen_val (val_constr id (LibListExec.rev rvs))
    | t1::ts' => Wpaux_getval Wpgen E t1 (fun v1 => mk (v1::rvs) ts')
    end.

Definition Wpgen_app (t:trm) : Formula :=
  MkStruct (Wp t).

Definition Wpaux_apps Wpgen (E:ctx) (v0:func) : list val -> list trm -> Formula :=
  (fix mk (rvs : list val) (ts : list trm) : Formula :=
    match ts with
    | nil => `Wpgen_app (trm_apps v0 (trms_vals (LibListExec.rev rvs)))
    | t1::ts' => Wpaux_getval Wpgen E t1 (fun v1 => mk (v1::rvs) ts')
    end).

Definition Wpgen_if_bool (b:bool) (F1 F2:Formula) : Formula :=
  MkStruct (fun A (EA:Enc A) Q =>
    if b then ^F1 Q else ^F2 Q).

Definition Wpaux_if (F0 F1 F2:Formula) : Formula :=
  `Wpgen_let_typed F0 (fun (b:bool) => `Wpgen_if_bool b F1 F2).

Definition Wpgen_while (F1 F2:Formula) : Formula :=
  MkStruct (`Formula_cast (fun (Q:unit->hprop) =>
    \forall (R:Formula),
    let F := Wpaux_if F1 (Wpgen_seq F2 R) (Wpgen_val val_unit) in
    \[ structural (@R unit _) /\ (forall (Q':unit->hprop), ^F Q' ==> ^R Q')] \-* (^R Q))).
    (* --TODO: use a lifted version of structural *)

Definition Wpgen_for_int (n1 n2:int) (F1:int->Formula) : Formula :=
  MkStruct (Formula_cast (fun (Q:unit->hprop) =>
    \forall (S:int->Formula),
    let F i := If (i <= n2) then (`Wpgen_seq (F1 i) (S (i+1)))
                            else (`Wpgen_val val_unit) in
    \[   (forall i, structural (S i unit _))
      /\ (forall i (Q':unit->hprop), ^(F i) Q' ==> ^(S i) Q')] \-* (^(S n1) Q))).
     (* --TODO: use a lifted version of structural_pred *)

Definition Wpgen_case (F1:Formula) (P:Prop) (F2:Formula) : Formula :=
  MkStruct (fun A (EA:Enc A) Q =>
    hand (^F1 Q) (\[P] \-* ^F2 Q)).

Definition Wpaux_match Wpgen (E:ctx) (v:val) : list (pat*trm) ->  Formula :=
  fix mk (pts:list(pat*trm)) : Formula :=
    match pts with
    | nil => `Wpgen_fail
    | (p,t)::pts' =>
        let xs := patvars p in
        let F1 A (EA:Enc A) (Q:A->hprop) :=
           hforall_vars (fun G => let E' := (Ctx.app G E) in
              \[v = patsubst G p] \-* ^(Wpgen E' t) Q) Ctx.empty xs in
        let P := forall_vars (fun G => v <> patsubst G p) Ctx.empty xs in
        Wpgen_case F1 P (mk pts')
    end.
  (* Note: the body of the cons case above, if put in an auxiliary definition,
     does not appear to simplify well using [xwp_simpl] *)


(* ---------------------------------------------------------------------- *)
(* ** Definition of the CF generator *)

Fixpoint Wpgen (E:ctx) (t:trm) : Formula :=
  let aux := Wpgen E in
  match t with
  | trm_val v => `Wpgen_val v
  | trm_var x => Wpaux_var E x
  | trm_fixs f xs t1 =>
      match xs with
      | nil => `Wpgen_fail
      | _ => `Wpgen_val (val_fixs f xs (isubst (Ctx.rem_vars xs (Ctx.rem f E)) t1))
      end
  | trm_constr id ts => Wpaux_constr Wpgen E id nil ts
  | trm_if t0 t1 t2 =>
     Wpaux_getval_typed Wpgen E t0 (fun b0 =>
       `Wpgen_if_bool b0 (aux t1) (aux t2))
  | trm_let z t1 t2 =>
     match z with
     | bind_anon => `Wpgen_seq (aux t1) (aux t2)
     | bind_var x => `Wpgen_let (aux t1) (fun A (EA:Enc A) (X:A) =>
                         Wpgen (Ctx.add x (enc X) E) t2)
     end
  | trm_apps t0 ts =>
     Wpaux_getval Wpgen E t0 (fun v0 =>
       Wpaux_apps Wpgen E v0 nil ts)
  | trm_while t1 t2 => `Wpgen_while (aux t1) (aux t2)
  | trm_for x t1 t2 t3 =>
     Wpaux_getval_typed Wpgen E t1 (fun n1 =>
       Wpaux_getval_typed Wpgen E t2 (fun n2 =>
         `Wpgen_for_int n1 n2 (fun n =>
            Wpgen (Ctx.add x (enc n) E) t3)))
  | trm_match t0 pts =>
      Wpaux_getval Wpgen E t0 (fun v0 =>
        Wpaux_match Wpgen E v0 pts)
  | trm_fail => `Wpgen_fail
  end.


(* ********************************************************************** *)
(* * Soundness proof *)

(* ---------------------------------------------------------------------- *)
(* ** Properties of semantical wp *)

(** [Wp t] is a structural formula *)

Lemma Structural_Wp : forall t,
  Structural (Wp t).
Proof using.
  intros. intros A EA. unfolds Wp. unfolds Weakestpre.
  applys structural_weakestpre. applys local_Triple.
Qed.

Arguments Structural_Wp : clear implicits.

(** Equivalence between a [triple] and its weakest-precondition presentation. *)

Lemma Triple_eq_himpl_Wp : forall A `{EA:Enc A} H (Q:A->hprop) t,
  Triple t H Q = (H ==> ^(Wp t) Q).
Proof using. intros. applys weakestpre_eq. applys local_Triple. Qed.

(** Reformulation of the right-to-left implication above as an implication. *)

Lemma Triple_of_Wp : forall A `{EA:Enc A} H (Q:A->hprop) t,
  H ==> ^(Wp t) Q ->
  Triple t H Q.
Proof using. intros. rewrite* Triple_eq_himpl_Wp. Qed.

(** Reformulation of the left-to-right implication above in the form
    of an entailment. *)

Lemma qimpl_Wp_of_Triple : forall t `{EA:Enc A} F,
  (forall Q, Triple t (F Q) Q) ->
  F ===> ((Wp t) A EA).
Proof using. introv M. intros Q. rewrite~ <- Triple_eq_himpl_Wp. Qed.

(** Another formulation of the same corollary --- currently not used *)
Lemma himpl_Wp_of_Triple : forall A `{EA:Enc A} (Q1:A->hprop) t H1,
  Triple t H1 Q1 ->
  H1 ==> ^(Wp t) Q1.
Proof using. introv M. rewrite* <- Triple_eq_himpl_Wp. Qed.


(* ---------------------------------------------------------------------- *)
(* ** Soundness of the [mklocal] transformer *)

(** [The [MkStruct] transformer may be stripped from the postcondition. *)

Lemma MkStruct_erase : forall H F `{EA:Enc A} (Q:A->hprop),
  H ==> ^F Q ->
  H ==> ^(MkStruct F) Q.
Proof using.
  introv M. xchanges M. applys mkstruct_erase.
Qed.

(** The [MkStruct] transformer is sound w.r.t. [Triple], in other words, it
    may be stripped from the precondition. *)

Lemma Triple_MkStruct_pre : forall t (F:Formula) `{EA:Enc A} (Q:A->hprop),
  (forall (Q:A->hprop), Triple t (^F Q) Q) ->
  Triple t (^(MkStruct F) Q) Q.
Proof using.
  introv M. applys~ local_elim.
  unfold MkStruct, mkstruct. xpull ;=> Q'.
  xsimpl (^F Q') ((Q' \--* Q \*+ \GC)) Q'. split~.
  { xsimpl. }
Qed.

(** The tactic [remove_MkStruct] applies to goal of the form [triple t (mklocal F Q) Q]
    and turns it into [triple t (F Q) Q] for a fresh [Q]. *)

Ltac remove_MkStruct :=
  match goal with |- @Triple _ _ _ _ ?Q =>
    applys Triple_MkStruct_pre; try (clear Q; intros Q); fold wp end.


(* ---------------------------------------------------------------------- *)
(* ** Soundness of [wp] *)

(* [F1 ====> F2] asserts that a Formula entails another one at all types. *)

Notation "F1 ====> F2" := (forall (A:Type) (EA:Enc A), F1 A EA ===> F2 A EA)
  (at level 67).


(** [Wpgen_sound t] asserts that [wp] is sound for all contexts [E],
    in the sense that the syntactic wp entails the semantics wp.
    The definition below is equivalent to:
[[
    Definition Wpgen_sound t :=
       forall E `{EA:Enc A} (Q:A->hprop),
       ^(Wpgen E t) Q ==> ^(Wpsubst E t) Q.
]]
*)

Definition Wpgen_sound t := forall E,
  (Wpgen E t) ====> (Wpsubst E t).

(** Lemma for [Wpgen_fail] *)

Lemma himpl_Wpgen_fail_l : forall A `{EA:Enc A} (Q:A->hprop) H,
  ^Wpgen_fail Q ==> H.
Proof using. intros. unfold Wpgen_fail, MkStruct, mkstruct. xpull. Qed.

(* --TODO: use lemma below for all occurences of wpgen_fail *)
Lemma Triple_Wpgen_fail : forall t `{EA:Enc A} (Q Q':A->hprop),
  Triple t (^Wpgen_fail Q) Q'.
Proof using.
  intros. apply Triple_of_Wp. applys himpl_Wpgen_fail_l.
Qed.

(** Soundness of the [wp] for the various constructs *)

Lemma Wpgen_sound_fail :
  Wpgen_sound trm_fail.
Proof using. intros. intros E A EA Q. applys himpl_Wpgen_fail_l. Qed.

Lemma Wpgen_sound_getval : forall E C t1 (F2of:val->Formula),
  evalctx C ->
  Wpgen_sound t1 ->
  (forall v, F2of v ====> Wpsubst E (C (trm_val v))) ->
  Wpaux_getval Wpgen E t1 F2of ====> Wpsubst E (C t1).
Proof using.
  introv HC M1 M2. intros A EA. applys qimpl_Wp_of_Triple. simpl. intros Q.
  tests C1: (trm_is_val t1).
  { destruct C1 as (v&Et). subst. simpl.
    apply Triple_of_Wp. applys M2. }
  tests C2: (trm_is_var t1).
  { destruct C2 as (x&Et). subst. simpl. case_eq (Ctx.lookup x E).
    { intros v Ev. rewrites~ (>> isubst_evalctx_trm_var Ev).
      apply Triple_of_Wp. applys M2. }
    { introv N. remove_MkStruct. xtpull. intros; false. } }
  asserts_rewrite (Wpaux_getval Wpgen E t1 (@F2of)
    = Wpgen_let (Wpgen E t1) (fun A1 (EA1:Enc A1) (V1:A1) => F2of (``V1))).
  { destruct t1; auto. { false C1. hnfs*. } { false C2. hnfs*. } }
  remove_MkStruct. xtpull ;=> A1 EA1. applys~ Triple_isubst_evalctx EA1.
  { apply Triple_of_Wp. applys M1. }
  { intros v. apply Triple_of_Wp. applys M2. }
Qed.

Lemma Wpgen_sound_var : forall x,
  Wpgen_sound (trm_var x).
Proof using.
  intros. intros E A EA. simpl. applys qimpl_Wp_of_Triple.
  intros Q. unfold Wpaux_var. simpl. destruct (Ctx.lookup x E).
  { remove_MkStruct. unfold Post_cast_val. xtpull ;=> V EQ. applys* Triple_val. }
  {  applys~ Triple_Wpgen_fail. }
Qed.

Lemma Wpgen_sound_val : forall v,
  Wpgen_sound (trm_val v).
Proof using.
  intros. intros E A EA. simpl. applys qimpl_Wp_of_Triple.
  intros Q. remove_MkStruct. unfold Post_cast_val. xtpull ;=> V EQ.
  simpl. intros. applys* Triple_val.
Qed.

Lemma Wpgen_sound_fixs : forall f xs t,
  Wpgen_sound (trm_fixs f xs t).
Proof using.
  intros. intros E A EA. simpl. applys qimpl_Wp_of_Triple.
  intros Q. destruct xs as [|x xs'].
  { applys~ Triple_Wpgen_fail. }
  { remove_MkStruct. applys~ triple_fixs. auto_false. }
Qed.

Lemma Wpgen_sound_if_bool : forall b (F1 F2:Formula) E t1 t2,
  F1 ====> (Wpsubst E t1) ->
  F2 ====> (Wpsubst E t2) ->
  Wpgen_if_bool b F1 F2 ====> Wpsubst E (trm_if b t1 t2).
Proof using.
  introv M1 M2. intros A EA. applys qimpl_Wp_of_Triple. simpl. intros Q.
  remove_MkStruct. applys Triple_if.
  apply Triple_of_Wp. case_if. { applys M1. } { applys M2. }
Qed.
(* --TODO choose version *)

Lemma Wpgen_sound_if_bool' : forall b (F1 F2:Formula) E t1 t2,
  F1 ====> (Wpsubst E t1) ->
  F2 ====> (Wpsubst E t2) ->
  Wpgen_if_bool b F1 F2 ====> Wp (if b then isubst E t1 else isubst E t2).
Proof using.
  introv M1 M2. intros A EA. applys qimpl_Wp_of_Triple. simpl. intros Q.
  remove_MkStruct. apply Triple_of_Wp. case_if. { applys M1. } { applys M2. }
Qed.

Lemma Wpgen_sound_seq : forall (F1 F2:Formula) E t1 t2,
  F1 ====> Wpsubst E t1 ->
  F2 ====> Wpsubst E t2 ->
  Wpgen_seq F1 F2 ====> Wpsubst E (trm_seq t1 t2).
Proof using.
  introv M1 M2. intros A EA. applys qimpl_Wp_of_Triple. intros Q.
  remove_MkStruct. simpl. applys Triple_seq.
  { rewrite Triple_eq_himpl_Wp. applys* M1. }
  { rewrite Triple_eq_himpl_Wp. applys* M2. }
Qed.

Lemma Wpgen_sound_let : forall (F1:Formula) (F2of:forall `{EA1:Enc A1},A1->Formula) E (x:var) t1 t2,
  F1 ====> Wpsubst E t1 ->
  (forall A `{EA:Enc A} (X:A), F2of X ====> Wpsubst (Ctx.add x (enc X) E) t2) ->
  Wpgen_let F1 (@F2of) ====> Wpsubst E (trm_let x t1 t2).
Proof using.
  Opaque Ctx.rem.
  introv M1 M2. intros A EA. applys qimpl_Wp_of_Triple. intros Q.
  remove_MkStruct. xtpull ;=> A1 EA1. simpl. applys Triple_let.
  { rewrite Triple_eq_himpl_Wp. applys* M1. }
  { intros X. rewrite Triple_eq_himpl_Wp.
    unfold Subst1. rewrite <- isubst_add_eq_subst1_isubst. applys* M2. }
Qed.

Lemma Wpgen_sound_let_typed : forall (F1:Formula) `{EA1:Enc A1} (F2of:A1->Formula) E (x:var) t1 t2,
  F1 ====> Wpsubst E t1 ->
  (forall (X:A1), F2of X ====> Wpsubst (Ctx.add x (enc X) E) t2) ->
  Wpgen_let_typed F1 F2of ====> Wpsubst E (trm_let x t1 t2).
Proof using.
  Opaque Ctx.rem.
  introv M1 M2. intros A EA. applys qimpl_Wp_of_Triple. intros Q.
  remove_MkStruct. xtpull. simpl. applys Triple_let EA1.
  (* --LATER: typeclass should not be resolved arbitrarily to EA if EA1 is not provided *)
  { rewrite Triple_eq_himpl_Wp. applys* M1. }
  { intros X. rewrite Triple_eq_himpl_Wp.
    unfold Subst1. rewrite <- isubst_add_eq_subst1_isubst. applys* M2. }
Qed.

Lemma Wpgen_sound_let_typed_val : forall v E (C:trm -> trm) `{EA:Enc A} (F2of:A->Formula),
  evalctx C ->
  (forall V, F2of V ====> @Wpsubst E (C ``V)) ->
  Wpgen_let_typed (`Wpgen_val v) F2of ====> Wp (isubst E (C v)).
Proof using.
  introv HC M1. intros A1 EA1. applys qimpl_Wp_of_Triple. intros Q.
  remove_MkStruct. applys~ Triple_isubst_evalctx EA.
  { rewrite Triple_eq_himpl_Wp. lets K: Wpgen_sound_val.
    unfold Wpgen_sound in K. simpl in K. xchange K. }
  { intros V. rewrite Triple_eq_himpl_Wp. xchange M1. }
Qed.

Lemma Wpgen_sound_getval_typed : forall E C t1 `{EA:Enc A} (F2of:A->Formula),
  evalctx C ->
  Wpgen_sound t1 ->
  (forall (V:A), F2of V ====> Wpsubst E (C ``V)) ->
  Wpaux_getval_typed Wpgen E t1 F2of ====> Wpsubst E (C t1).
Proof using.
  introv HC M1 M2. intros A1 EA1. applys qimpl_Wp_of_Triple. simpl. intros Q.
  tests C1: (trm_is_val t1).
  { destruct C1 as (v&Et). subst. simpl.
    apply Triple_of_Wp. applys~ Wpgen_sound_let_typed_val. }
  tests C2: (trm_is_var t1).
  { destruct C2 as (x&Et). subst. simpl. case_eq (Ctx.lookup x E).
    { intros v Ev. rewrites~ (>> isubst_evalctx_trm_var Ev).
      apply Triple_of_Wp. applys~ Wpgen_sound_let_typed_val. }
    { introv N. remove_MkStruct. xtpull. intros; false. } }
  asserts_rewrite (Wpaux_getval_typed Wpgen E t1 (@F2of) = Wpgen_let_typed (Wpgen E t1) F2of).
  { destruct t1; auto. { false C2. hnfs*. } }
  remove_MkStruct. applys~ Triple_isubst_evalctx EA.
  { apply Triple_of_Wp. applys M1. }
  { intros V. apply Triple_of_Wp. applys M2. }
Qed.

Lemma Wpgen_sound_if_trm : forall (F0 F1 F2:Formula) E t0 t1 t2,
  F0 ====> (Wpsubst E t0) ->
  F1 ====> (Wpsubst E t1) ->
  F2 ====> (Wpsubst E t2) ->
  Wpaux_if F0 F1 F2 ====> Wpsubst E (trm_if t0 t1 t2).
Proof using.
  introv M0 M1 M2. intros A EA. applys qimpl_Wp_of_Triple. intros Q.
  remove_MkStruct. xtpull. simpl. applys Triple_if_trm.
  { rewrite Triple_eq_himpl_Wp. applys* M0. }
  { intros b. apply Triple_of_Wp. applys* Wpgen_sound_if_bool'. }
Qed.

Lemma Wpgen_sound_if : forall t1 t2 t3,
  Wpgen_sound t1 ->
  Wpgen_sound t2 ->
  Wpgen_sound t3 ->
  Wpgen_sound (trm_if t1 t2 t3).
Proof using.
  intros. intros E. simpl.
  applys~ Wpgen_sound_getval_typed (fun t1 => trm_if t1 t2 t3).
  intros v1. applys* Wpgen_sound_if_bool.
Qed.

Lemma Wpgen_sound_apps : forall t0 ts,
  Wpgen_sound t0 ->
  (forall t, mem t ts -> Wpgen_sound t) ->
  Wpgen_sound (trm_apps t0 ts).
Proof using.
  introv IH0 IHts. intros E A EA Q. simpl.
  applys~ Wpgen_sound_getval (fun t1 => trm_apps t1 ts). intros v0. clear Q.
  cuts M: (forall rvs,
    Wpaux_apps Wpgen E v0 rvs ts ====>
    Wp (trm_apps v0 ((trms_vals (LibList.rev rvs))++(LibList.map (isubst E) ts)))).
  { unfold Wpsubst. simpl. rew_list_exec. applys M. }
  induction ts as [|t ts']; intros.
  { simpl. rew_list_exec. rew_list.
    apply~ mkstruct_erase_l. applys Structural_Wp. }
  { specializes IHts' __. { intros t' Ht'. applys* IHts. }
    unfold Wpaux_apps. fold (Wpaux_apps Wpgen E v0). rew_listx.
    forwards~ M: Wpgen_sound_getval E (fun t1 => trm_apps v0 (trms_vals (rev rvs) ++ t1 :: ts')).
    2:{ unfold Wpsubst in M. rewrite isubst_trm_apps_app in M. applys M. }
    intros v1. intros A1 EA1. applys qimpl_Wp_of_Triple. intros Q.
    rewrite isubst_trm_apps_args. simpl. apply Triple_of_Wp.
    forwards M: IHts' (v1::rvs). rewrite app_trms_vals_rev_cons in M. applys M. }
Qed.

Lemma Wpgen_sound_while : forall (F1 F2:Formula) E t1 t2,
  F1 ====> Wpsubst E t1 ->
  F2 ====> Wpsubst E t2 ->
  Wpgen_while F1 F2 ====> Wpsubst E (trm_while t1 t2).
Proof using.
  introv M1 M2. intros A EA. applys qimpl_Wp_of_Triple. intros Q.
  remove_MkStruct. simpl.
  unfold Formula_cast, Wptag. xtpull ;=> Q' C. applys Triple_enc_change (rm C).
  set (R := Wp (trm_while (isubst E t1) (isubst E t2))).
  applys Triple_hforall R. simpl. applys Triple_hwand_hpure_l.
  { split.
    { applys Structural_Wp. }
    { clears Q. applys qimpl_Wp_of_Triple. intros Q.
      applys Triple_while_raw.
      asserts_rewrite~ (
         trm_if (isubst E t1) (trm_seq (isubst E t2) (trm_while (isubst E t1) (isubst E t2))) val_unit
       = isubst E (trm_if t1 (trm_seq t2 (trm_while t1 t2)) val_unit)).
      rewrite Triple_eq_himpl_Wp. applys~ Wpgen_sound_if_trm.
      { applys~ Wpgen_sound_seq. }
      { intros A1 EA1 Q''. applys Wpgen_sound_val. } } }
  { rewrite~ @Triple_eq_himpl_Wp. }
Qed.

Lemma Wpgen_sound_for_int : forall (x:var) n1 n2 (F1:int->Formula) E t1,
  (forall (n:int), F1 n ====> Wpsubst (Ctx.add x (``n) E) t1) ->
  Wpgen_for_int n1 n2 F1 ====> Wpsubst E (trm_for x n1 n2 t1).
Proof using. Opaque Ctx.add Ctx.rem.
  introv M. intros A EA. applys qimpl_Wp_of_Triple. intros Q.
  remove_MkStruct. simpl.
  unfold Formula_cast, Wptag. xtpull ;=> Q' C.
  applys Triple_enc_change (rm C).
  set (S := fun (i:int) => Wp (isubst E (trm_for x i n2 t1))).
  applys Triple_hforall S. simpl. applys Triple_hwand_hpure_l.
  { split.
    { intros r. applys Structural_Wp. }
    { clears Q. intros i. applys qimpl_Wp_of_Triple. intros Q.
      applys Triple_for_raw. fold isubst.
      rewrite~ @Triple_eq_himpl_Wp. case_if.
      { unfold Subst1. rewrite <- isubst_add_eq_subst1_isubst.
        asserts_rewrite (trm_seq (isubst (Ctx.add x (``i) E) t1) (trm_for x (i + 1)%I n2 (isubst (Ctx.rem x E) t1))
          = (isubst (Ctx.add x (``i) E) (trm_seq t1 (trm_for x (i + 1)%I n2 t1)))).
        { simpl. rewrite Ctx.rem_anon, Ctx.rem_add_same. auto. }
        applys Wpgen_sound_seq.
        { applys* M. }
        { unfold S. unfold Wpsubst. simpl. rewrite~ Ctx.rem_add_same. } }
      { applys Wpgen_sound_val E. } } }
  { rewrite~ @Triple_eq_himpl_Wp. }
Qed.

Lemma Wpgen_sound_for_trm : forall x t1 t2 t3,
  Wpgen_sound t1 ->
  Wpgen_sound t2 ->
  Wpgen_sound t3 ->
  Wpgen_sound (trm_for x t1 t2 t3).
Proof using.
  introv M1 M2 M3. intros E A EA Q. simpl.
  applys~ Wpgen_sound_getval_typed (fun t1 => trm_for x t1 t2 t3).
  intros n1. applys~ Wpgen_sound_getval_typed (fun t2 => trm_for x n1 t2 t3).
  intros n2. unfold Wptag. rewrite (enc_int_eq n2). applys~ Wpgen_sound_for_int.
Qed.

Lemma Wpgen_sound_match : forall t0 pts,
  Wpgen_sound t0 ->
  (forall p t, mem (p,t) pts -> Wpgen_sound t) ->
  Wpgen_sound (trm_match t0 pts).
Proof using.
  introv M1 M2. intros E Q. simpl.
  applys~ Wpgen_sound_getval (fun t1 => trm_match t1 pts).
  intros v. clears t0 Q.
  induction pts as [|(p,t) pts'].
  { simpl. intros A EA Q. applys himpl_Wpgen_fail_l. }
  { simpl. intros A EA. applys qimpl_Wp_of_Triple. intros Q. remove_MkStruct.
    simpl. applys Triple_match.
    { intros G EG Hp. applys Triple_hand_l.
      forwards~ IH: M2 p t. clears IHpts' M2. subst v.
      rewrite <- EG. rewrite <- isubst_app_eq_isubst_isubst_rem_vars.
      sets_eq xs: (Ctx.dom G). forwards~ W: hforall_vars_intro G xs.
      applys~ Triple_conseq Q W. simpl.
      applys~ Triple_hwand_hpure_l.
      applys Triple_of_Wp. applys IH. }
    { intros Hp. applys Triple_hand_r. applys Triple_hwand_hpure_l.
      { applys~ forall_vars_intro. }
      applys Triple_of_Wp. applys IHpts'. { introv M. applys* M2. } } }
Qed.

Lemma Wpgen_sound_constr : forall E id ts,
  (forall t, mem t ts -> Wpgen_sound t) ->
  Wpaux_constr Wpgen E id nil ts ====> Wpsubst E (trm_constr id ts).
Proof using.
  introv IHwp. cuts M: (forall rvs,
         Wpaux_constr Wpgen E id rvs ts
    ====> Wpsubst E (trm_constr id ((trms_vals (LibList.rev rvs))++ts))).
  { applys M. }
  induction ts as [|t ts']; intros.
  { simpl. rew_list_exec. rew_list. applys qimpl_Wp_of_Triple.
    simpl. rew_list_exec.
    intros Q. remove_MkStruct. rewrite map_isubst_trms_vals. applys~ @triple_constr.
    (* --LATER: Triple_constr is not suitable here *) }
  { specializes IHts' __. { intros t' Ht'. applys* IHwp. }
    applys~ Wpgen_sound_getval (fun t1 => trm_constr id (trms_vals (rev rvs) ++ t1 :: ts')).
    intros v1. fold (Wpaux_constr Wpgen E id). intros A1 EA1.
    applys qimpl_Wp_of_Triple. intros Q. rewrite isubst_trm_constr_args.
    apply Triple_of_Wp.
    forwards M: IHts' (v1::rvs). xchange M. rewrite app_trms_vals_rev_cons.
    unfold Wpsubst. rewrite* isubst_trm_constr_args. }
Qed.

(** Putting it all together *)

Lemma Wpgen_sound_trm : forall t,
  Wpgen_sound t.
Proof using.
  intros t. induction t using trm_induct; intros E A EA Q.
  { applys Wpgen_sound_val. }
  { applys Wpgen_sound_var. }
  { applys Wpgen_sound_fixs. }
  { applys~ Wpgen_sound_constr. }
  { applys* Wpgen_sound_if. }
  { destruct b as [|x].
    { applys* Wpgen_sound_seq. }
    { applys* Wpgen_sound_let. } }
  { applys* Wpgen_sound_apps. }
  { applys* Wpgen_sound_while. }
  { applys* Wpgen_sound_for_trm. }
  { applys* Wpgen_sound_match. }
  { applys Wpgen_sound_fail. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Corollaries of the soundness of [wp] *)

Lemma Triple_isubst_Wpgen : forall t E `{EA:Enc A} (Q:A->hprop),
  Triple (isubst E t) (^(Wpgen E t) Q) Q.
Proof using.
  intros. rewrite Triple_eq_himpl_Wp. applys Wpgen_sound_trm.
Qed.

Lemma Triple_isubst_of_Wpgen : forall t E H `{EA:Enc A} (Q:A->hprop),
  H ==> ^(Wpgen E t) Q ->
  Triple (isubst E t) H Q.
Proof using. introv M. xtchanges M. applys Triple_isubst_Wpgen. Qed.

Lemma Triple_of_Wpgen : forall (t:trm) H `{EA:Enc A} (Q:A->hprop),
  H ==> ^(Wpgen Ctx.empty t) Q ->
  Triple t H Q.
Proof using.
  introv M. xtchanges M. pattern t at 1; rewrite <- (isubst_empty t).
  applys Triple_isubst_Wpgen.
Qed.

(* not used *)
Lemma Wp_of_Wpgen : forall t H `{EA:Enc A} (Q:A->hprop),
  H ==> ^(Wpgen Ctx.empty t) Q ->
  H ==> ^(Wp t) Q.
Proof using. introv M. applys himpl_weakestpre. applys* Triple_of_Wpgen. Qed.

(* not used *)
Lemma himpl_Wpgen_app_of_Triple : forall A `{EA:Enc A} (Q:A->hprop) t H,
  Triple t H Q ->
  H ==> ^(Wpgen_app t) Q.
Proof using. intros. applys MkStruct_erase. rewrite~ <- Triple_eq_himpl_Wp. Qed.


(* ********************************************************************** *)
(* * Notation for characteristic formulae *)

(* ---------------------------------------------------------------------- *)
(* ** Notation for computed WP *)

Notation "'Fail'" :=
  ((Wpgen_fail))
  (at level 69) : wp_scope.

Notation "'Val' v" :=
  ((Wpgen_val v))
  (at level 69) : wp_scope.

Notation "'Cast' V" :=
  ((Wpgen_Val_no_mkstruct V))
  (at level 69) : wp_scope.

Notation "'Return' F " :=
  (Formula_cast F)
  (at level 68) : wp_scope.

Notation "'Let_' x ':=' F1 'in' F2" :=
  ((Wpgen_let_typed F1 (fun x => F2)))
  (at level 69, x ident, right associativity,
  format "'[v' '[' 'Let_'  x  ':='  F1  'in' ']'  '/'  '[' F2 ']' ']'") : wp_scope.

Notation "'Let_' [ A EA ] x ':=' F1 'in' F2" :=
  ((Wpgen_let F1 (fun A EA x => F2)))
  (at level 69, A at level 0, EA at level 0, x ident, right associativity,
  format "'[v' '[' 'Let_'  [ A  EA ]  x  ':='  F1  'in' ']'  '/'  '[' F2 ']' ']'") : wp_scope.

Notation "'Seq' F1 '; F2" :=
  ((Wpgen_seq F1 F2))
  (at level 68, right associativity,
   format "'[v' 'Seq'  '[' F1 ']' '';' '/'  '[' F2 ']' ']'") : wp_scope.

Notation "'App' f v1 " :=
  ((Wpgen_app (trm_apps f (trms_vals (v1::nil)))))
  (at level 68, f, v1 at level 0) : wp_scope.

Notation "'App' f v1 .. vn " :=
  ((Wpgen_app (trm_apps f (trms_vals (cons v1 .. (cons vn nil) ..)))))
  (at level 68, f, v1, vn at level 0) : wp_scope.

Notation "'Ifval' b 'Then' F1 'Else' F2" :=
  ((Wpgen_if_bool b F1 F2))
  (at level 69) : wp_scope.

Notation "'While' F1 'Do' F2 'Done'" :=
  ((Wpgen_while F1 F2))
  (at level 69, F2 at level 68,
   format "'[v' 'While'  F1  'Do'  '/' '[' F2 ']' '/'  'Done' ']'")
   : wp_scope.

Notation "'For' x '=' n1 'To' n2 'Do' F3 'Done'" :=
  ((Wpgen_for_int n1 n2 (fun x => F3)))
  (at level 69, x ident,
   format "'[v' 'For'  x  '='  n1  'To'  n2  'Do'  '/' '[' F3 ']' '/'  'Done' ']'")
  : wp_scope.

Notation "'Case' v '=' vp ''=>' F1 ''|' F2" :=
  ((Wpgen_case (fun A EA Q => \[v = vp%val] \-* F1 A EA Q) (v <> vp%val) F2))
  (at level 69, v, vp at level 0,
   format "'[v' 'Case'  v  '='  vp  ''=>'  '[' '/' F1 ']' '[' '/'  ''|'  F2 ']' ']'")
   : wp_scope.

Notation "'Case' v '=' vp [ x1 ] ''=>' F1 ''|' F2" :=
  ((Wpgen_case (fun A EA Q => \forall x1, \[v = vp%val] \-* F1 A EA Q) (forall x1, v <> vp%val) F2))
  (at level 69, v, vp at level 0, x1 ident,
   format "'[v' 'Case'  v  '='  vp  [ x1 ]  ''=>'  '[' '/' F1 ']' '[' '/'  ''|'  F2 ']' ']'")
   : wp_scope.

Notation "'Case' v '=' vp [ x1 x2 ] ''=>' F1 ''|' F2" :=
  ((Wpgen_case (fun A EA Q => \forall x1 x2, \[v = vp%val] \-* F1 A EA Q) (forall x1 x2, v <> vp%val) F2))
  (at level 69, v, vp at level 0, x1 ident, x2 ident,
   format "'[v' 'Case'  v  '='  vp  [ x1  x2 ]  ''=>'  '[' '/' F1 ']' '[' '/'  ''|'  F2 ']' ']'")
   : wp_scope.


(* TODO: use custom entry

  Declare Scope wp_scope.

  (** Notation for printing proof obligations arising from [wpgen]. *)

  Notation "'PRE' H 'CODE' F 'POST' Q" :=
    (H ==> (mkstruct F) Q)
    (at level 8, H at level 0, F, Q at level 0,
     format "'[v' 'PRE'  H  '/' 'CODE'  F '/' 'POST'  Q ']'") : wp_scope.

  Notation "` F" :=
    (mkstruct F)
    (at level 10,
     format "` F") : wp_scope.

  (** Custom grammar for the display of characteristic formulae. *)

  Declare Custom Entry wp.

  Notation "<[ e ]>" :=
    e
    (at level 0, e custom wp at level 99) : wp_scope.

  Notation "` F" :=
    (mkstruct F)
    (in custom wp at level 10,
     format "` F") : wp_scope.

  Notation "( x )" :=
    x
    (in custom wp,
     x at level 99) : wp_scope.

  Notation "{ x }" :=
    x
    (in custom wp at level 0,
     x constr,
     only parsing) : wp_scope.

  Notation "x" :=
    x
    (in custom wp at level 0,
     x constr at level 0) : wp_scope.

  Notation "'Fail'" :=
    ((wpgen_fail))
    (in custom wp at level 69) : wp_scope.

  Notation "'Val' v" :=
    ((wpgen_val v))
    (in custom wp at level 69) : wp_scope.

  Notation "'Let' x ':=' F1 'in' F2" :=
    ((wpgen_let F1 (fun x => F2)))
    (in custom wp at level 69,
     x ident,
     F1 custom wp at level 99,
     F2 custom wp at level 99,
     right associativity,
    format "'[v' '[' 'Let'  x  ':='  F1  'in' ']' '/' '[' F2 ']' ']'") : wp_scope.

  Notation "'Seq' F1 ; F2" :=
    ((wpgen_seq F1 F2))
    (in custom wp at level 68,
     F1 custom wp at level 99,
     F2 custom wp at level 99,
     right associativity,
     format "'[v' 'Seq'  '[' F1 ']'  ; '/' '[' F2 ']' ']'") : wp_scope.

  Notation "'App' f v1" :=
    ((wp (trm_app f v1)))
    (in custom wp at level 68, f, v1 at level 0) : wp_scope.

  Notation "'App' f v1 v2" :=
    ((wp (trm_app (trm_app f v1) v2)))
    (in custom wp at level 68, f, v1, v2 at level 0) : wp_scope.

  Notation "'If_' v 'Then' F1 'Else' F2" :=
    ((wpgen_if v F1 F2))
    (in custom wp at level 69,
     F1 custom wp at level 99,
     F2 custom wp at level 99,
     left associativity,
     format "'[v' '[' 'If_'  v  'Then'  ']' '/' '['   F1 ']' '/' 'Else' '/' '['   F2 ']' ']'") : wp_scope.

  Notation "'Fun' x '=>' F1" :=
    ((wpgen_fun (fun x => F1)))
    (in custom wp at level 69,
     x ident,
     F1 custom wp at level 99,
     right associativity,
    format "'[v' '[' 'Fun'  x  '=>'  F1  ']' ']'") : wp_scope.

  Notation "'Fix' f x '=>' F1" :=
    ((wpgen_fix (fun f x => F1)))
    (in custom wp at level 69,
     f ident, x ident,
     F1 custom wp at level 99,
     right associativity,
     format "'[v' '[' 'Fix'  f  x  '=>'  F1  ']' ']'") : wp_scope.


*)

(*
  | Cf_app (ts, tret, f, vs) -> (* TODO: maybe make the return type explicit? *)
  | Cf_body (f, fvs, targs, typ, cf1) ->
  | Cf_let ((x,typ), cf1, cf2) ->
  | Cf_let_poly (x, fvs_strict, fvs_other, typ, cf1, cf2) ->
  | Cf_val (x, fvs_strict, typ, v, cf) ->
  | Cf_fun (ncs, cf) ->
  | Cf_caseif (v,cf1,cf2) ->
  | Cf_case (v,tps,pat,vwhenopt,aliases,cf1,cf2) ->
  | Cf_match (label, n, cf1) ->
  | Cf_seq (cf1,cf2) ->
  | Cf_for (dir,i_name,v1,v2,cf) ->
  | Cf_while (cf1,cf2) ->
  | Cf_pay (cf1) ->
*)

(* ********************************************************************** *)
(* TODO: present in the course  wpgen_assert *)

Definition Wpgen_assert (F1:Formula) : Formula :=
  MkStruct (Formula_cast (fun (Q:unit->hprop) =>
    Q tt \* \[Q tt ==> ^F1 (fun r => \[r = true] \* Q tt)])).

Definition Wpgen_done : Formula :=
  MkStruct (fun A (EA:Enc A) Q =>
    \[False] \-* \[True]).

Definition Wpgen_Val A1 {EA1:Enc A1} (V:A1) : Formula :=
  MkStruct (Wpgen_Val_no_mkstruct V).
  (* MkStruct (fun A (EA:Enc A) (Q:A->hprop) => Post_cast A Q V)). *)

(*
Arguments WPLifted.Wpgen_Val [A1] {EA1} V. (* prevents expanded implicit arguments *)
*)

(* TODO
  Lemma xval_lifted_lemma : forall A `{EA:Enc A} (V:A) H (Q:A->hprop),
    H ==> Q V ->
    H ==> ^(Wpgen_val_lifted V) Q.
  Proof using. introv E N. subst. applys MkStruct_erase. ... Qed.
*)

(* alternative?
Definition Wpgen_val_lifted `{Enc A} (V:A) : Formula :=
  MkStruct (Formula_cast (fun (Q:A->hprop) => Q V)).
*)

(* for the reference:

Definition Formula_cast `{Enc A1} (F:(A1->hprop)->hprop) : Formula :=
  fun A2 (EA2:Enc A2) (Q:A2->hprop) =>
    \exists (Q':A1->hprop), F Q' \* \[Q' ===> Post_cast A1 Q].

Definition Wpgen_Val_no_mkstruct A1 `{EA1:Enc A1} (V:A1) : Formula :=
  fun A2 (EA2:Enc A2) Q => Post_cast A1 Q V.
*)

(* includes the return type *)

Definition Wpgen_app_typed (A1:Type) `{EA1:Enc A1} (t:trm) : Formula :=
  MkStruct (Formula_cast (fun (Q1:A1->hprop) => ^(Wp t) Q1)).

Arguments Wpgen_app_typed A1 {EA1} t.

Fixpoint Trm_apps (f:trm) (Vs:dyns) : trm :=
  match Vs with
  | nil => f
  | (Dyn V)::Vs' => Trm_apps (f (enc V)) Vs'
  end.

Definition Wpgen_App_typed (A1:Type) `{EA1:Enc A1} (f:trm) (Vs:dyns) : Formula :=
  Wpgen_app_typed A1 (Trm_apps f Vs).
(* MkStruct (Formula_cast (fun (Q1:A1->hprop) => Wp (Trm_apps f Vs) Q1)). *)

Arguments Wpgen_App_typed A1 {EA1} f Vs.


Definition Wpgen_for_downto_int (n1 n2:int) (F1:int->Formula) : Formula :=
  MkStruct (Formula_cast (fun (Q:unit->hprop) =>
    \forall (S:int->Formula),
    let F i := If (i >= n2) then (`Wpgen_seq (F1 i) (S (i-1)))
                            else (`Wpgen_val val_unit) in
    \[   (forall i, structural (S i unit _))
      /\ (forall i (Q':unit->hprop), ^(F i) Q' ==> ^(S i) Q')] \-* (^(S n1) Q))).


(*
Definition Wpgen_fix (Fof:val->val->Formula) : Formula :=
  MkStruct (fun A (EA:Enc A) Q =>
    \forall vf, \[forall vx A' (EA':Enc A') Q',
                    Fof vf vx Q' ==> wp (trm_app vf vx) Q'] \-* Q vf).
*)

(* LATER
Definition Formula_entails (F1 F2:Formula) : Prop :=
  forall A (EA:Enc A) Q, ^F1 Q ==> ^F2 Q.

Definition Wpgen_fixs (Fof:val->vals->Formula) : Formula :=
  MkStruct (fun A (EA:Enc A) Q =>
    \forall vf, \[forall vxs, Formula_entails (Fof vf vxs) (Wp (trm_apps vf vxs))]
                \-* Q vf).

Definition Wpgen_fixs_custom (Custom:(val->(vals->Formula->Prop)->Prop) : Formula :=
  MkStruct (fun A (EA:Enc A) Q =>
    \forall vf, \[Custom vf (fun vxs Fof => Formula_entails (Fof vf) (Wp (trm_apps vf vxs)))]
                \-* Q vf).
*)

(* usage: Wpgen_fixs_custom (fun f Pof =>
             forall A1..AM .. x1..xN, Pof [x1;..;xn] (Wpbody vf) *)


Definition Wpgen_let_fun (BodyOf:forall A,Enc A->(A->hprop)->hprop) : Formula :=
  MkStruct (fun A (EA:Enc A) (Q:A->hprop) =>
    BodyOf _ _ Q).

(* LATER: a function that takes a list of propositions parameterized
    by the list of names of the functions that occur.

   Custom notation for

   Wpgen_let_funs ((fun f1 f2 => B1)::(fun f1 f2 => B2)::nil).

  Definition Wpgen_let_funs (Defs:list()) : Formula :=

*)

Definition Wpgen_let_Val A1 `{EA1:Enc A1} (V:A1) (Fof:A1->Formula) : Formula :=
  MkStruct (fun A (EA:Enc A) (Q:A->hprop) =>
    \forall (x:A1), \[x = V] \-* ^(Fof x) Q).

Definition Wpgen_body (P:Prop) : Prop :=
  P.

Definition Wpgen_dummy : Formula :=
  Wpgen_fail.


(* ********************************************************************** *)


(*

    Fixpoint wpgen (E:ctx) (t:trm) : formula :=
      mkstruct match t with
      | ..
      | trm_fix f x t1 => wpgen_fix (fun vf v => wpgen ((f,vf)::(x,v)::E) t1)
      | ..

    Definition wpgen_fix (Fof:val->val->formula) : formula := fun Q =>
      \forall vf, \[forall vx Q', Fof vf vx Q' ==> wp (trm_app vf vx) Q'] \-* Q vf.

    Lemma xfun_spec_lemma : forall (S:val->Prop) H Q Fof,
      (forall vf,
        (forall vx H' Q', (H' ==> Fof vx Q') -> triple (trm_app vf vx) H' Q') ->
        S vf) ->
      (forall vf, S vf -> (H ==> Q vf)) ->
      H ==> wpgen_fun Fof Q.
    Proof using.
      introv M1 M2. unfold wpgen_fun. xsimpl. intros vf N.
      applys M2. applys M1. introv K. rewrite <- wp_equiv. xchange K. applys N.
    Qed.

    Tactic Notation "xfun" constr(S) :=
      xseq_xlet_if_needed; xstruct_if_needed; applys xfun_spec_lemma S.
    Lemma xfun_nospec_lemma : forall H Q Fof,
      (forall vf,
           (forall vx H' Q', (H' ==> Fof vx Q') -> triple (trm_app vf vx) H' Q') ->
         (H ==> Q vf)) ->
      H ==> wpgen_fun Fof Q.
    Proof using.
      introv M. unfold wpgen_fun. xsimpl. intros vf N. applys M.
      introv K. rewrite <- wp_equiv. xchange K. applys N.
    Qed.

    Tactic Notation "xfun" :=
      xseq_xlet_if_needed; xstruct_if_needed; applys xfun_nospec_lemma.




---TUTO on wp for assertions

  H ==> wp t (fun r => \[r = true] \* H) ->
  H ==> wp (val_assert t) (fun _ => H).

 wp t (fun r => \[r = true] \* H) ==> wp (val_assert t) (fun _ => H)
 \exists H, H \* \[H ==> wp t (fun r => \[r = true] \* H)] \* (#H \--* Q) ==> wp (val_assert t) Q

 Q tt \* \[Q tt ==> wp t (fun r => \[r = true] \* Q tt)] ==> wp (val_assert t) Q

*)