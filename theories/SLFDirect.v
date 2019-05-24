(**

Separation Logic Foundations

Chapter: "Direct".

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From TLC Require Export LibCore.
From Sep Require Import TLCbuffer Var.
From Sep Require Fmap Hsimpl.

(* ####################################################### *)
(** * Imports *)

(* ******************************************************* *)
(** ** Extensionality axioms *)

Module Assumptions.

(** The file [LibAxioms] from the TLC library includes the axioms of
    functional extensionality and propositional extensionality.
    These axioms are essential to proving equalities between
    heap predicates, and between postconditions. *)

Axiom functional_extensionality : forall A B (f g:A->B),
  (forall x, f x = g x) ->
  f = g.

Axiom propositional_extensionality : forall (P Q:Prop),
  (P <-> Q) ->
  P = Q.

End Assumptions.


(* ******************************************************* *)
(** ** Variables *)

(** The file [Var.v] defines the type [var] as an alias for [string].

    It provides the boolean function [var_eq x y] to compare two variables.

    It provides the tactic [case_var] to perform case analysis on 
    expressions of the form [if var_eq x y then .. else ..] 
    that appear in the goal. *)


(* ******************************************************* *)
(** ** Finite maps *)

(** The file [Fmap.v] provides a formalization of finite maps, which
    are then used to represent heaps in the semantics.

    The implementation details need not be revealed. 
  
    Finiteness of maps is essential because to justify that allocation
    yields a fresh reference, one must be able to argue for the 
    existence of a location fresh from existing heaps. From the 
    finiteness of heaps and the infinite number of variables, we
    can conclude that fresh locations always exist. 
    
    The library [Fmap.v] provides the basic operations of finite maps,
    and in particular the definition of disjointness.

    It provides a tactic [fmap_disjoint] to automate the disjointness proofs,
    and a tactic [fmap_eq] to prove equalities between heaps modulo
    associativity and commutativity. Without these two tactics, the 
    proofs would be extremely tedious and fragile. *)



(* ####################################################### *)
(** * Source language *)

(* ******************************************************* *)
(** ** Syntax *)

Definition loc : Type := nat.

Inductive val : Type :=
  | val_unit : val
  | val_bool : bool -> val
  | val_int : int -> val
  | val_loc : loc -> val
  | val_fun : var -> trm -> val
  | val_fix : var -> var -> trm -> val
  | val_ref : val
  | val_get : val
  | val_set : val
  | val_add : val

with trm : Type :=
  | trm_val : val -> trm
  | trm_var : var -> trm
  | trm_fun : var -> trm -> trm
  | trm_fix : var -> var -> trm -> trm
  | trm_app : trm -> trm -> trm
  | trm_seq : trm -> trm -> trm
  | trm_let : var -> trm -> trm -> trm
  | trm_if : trm -> trm -> trm -> trm.

Definition heap : Type := fmap loc val.

Notation "'heap_empty'" := (@Fmap.empty loc val)
  (at level 0).

Notation "h1 \u h2" := (Fmap.union h1 h2) (* optional *)
  (at level 37, right associativity).


(* ******************************************************* *)
(** ** Implicit Types *)

Implicit Types f : var.
Implicit Types b : bool.
Implicit Types l : loc.
Implicit Types n : int.
Implicit Types v w r : val.
Implicit Types t : trm.
Implicit Types h s : heap.

(** The type of values is inhabited. *)

Global Instance Inhab_val : Inhab val.
Proof using. apply (Inhab_of_val val_unit). Qed.


(* ******************************************************* *)
(** ** Substitution *)

Fixpoint subst (y:var) (w:val) (t:trm) : trm :=
  let aux t := subst y w t in
  let if_y_eq x t1 t2 := if var_eq x y then t1 else t2 in
  match t with
  | trm_val v => trm_val v
  | trm_var x => if_y_eq x (trm_val w) t
  | trm_fun x t1 => trm_fun x (if_y_eq x t1 (aux t1))
  | trm_fix f x t1 => trm_fix f x (if_y_eq f t1 (if_y_eq x t1 (aux t1)))
  | trm_app t1 t2 => trm_app (aux t1) (aux t2)
  | trm_seq t1 t2 => trm_seq  (aux t1) (aux t2)
  | trm_let x t1 t2 => trm_let x (aux t1) (if_y_eq x t2 (aux t2))
  | trm_if t0 t1 t2 => trm_if (aux t0) (aux t1) (aux t2)
  end.


(* ******************************************************* *)
(** ** Coercions *)

Coercion val_bool : bool >-> val.
Coercion val_int : Z >-> val.
Coercion val_loc : loc >-> val.

Coercion trm_val : val >-> trm.
Coercion trm_var : var >-> trm.
Coercion trm_app : trm >-> Funclass.


(* ******************************************************* *)
(** ** Semantics *)

Inductive eval : heap -> trm -> heap -> val -> Prop :=
  | eval_val : forall s v,
      eval s (trm_val v) s v
  | eval_fun : forall s x t1,
      eval s (trm_fun x t1) s (val_fun x t1)
  | eval_fix : forall s f x t1,
      eval s (trm_fix f x t1) s (val_fix f x t1)
  | eval_app_fun : forall s1 s2 v1 v2 x t1 v,
      v1 = val_fun x t1 ->
      eval s1 (subst x v2 t1) s2 v ->
      eval s1 (trm_app v1 v2) s2 v
  | eval_app_fix : forall s1 s2 v1 v2 f x t1 v,
      v1 = val_fix f x t1 ->
      eval s1 (subst x v2 (subst f v1 t1)) s2 v ->
      eval s1 (trm_app v1 v2) s2 v
  | eval_seq : forall s1 s2 s3 t1 t2 v1 v,
      eval s1 t1 s2 v1 ->
      eval s2 t2 s3 v ->
      eval s1 (trm_seq t1 t2) s3 v
  | eval_let : forall s1 s2 s3 x t1 t2 v1 r, 
      eval s1 t1 s2 v1 ->
      eval s2 (subst x v1 t2) s3 r ->
      eval s1 (trm_let x t1 t2) s3 r
  | eval_if_case : forall s1 s2 b v t1 t2,
      eval s1 (if b then t1 else t2) s2 v ->
      eval s1 (trm_if (val_bool b) t1 t2) s2 v
  | eval_add : forall s n1 n2,
      eval s (val_add (val_int n1) (val_int n2)) s (val_int (n1 + n2))
  | eval_ref : forall s v l,
      ~ Fmap.indom s l ->
      eval s (val_ref v) (Fmap.update s l v) (val_loc l)
  | eval_get : forall s l,
      Fmap.indom s l ->
      eval s (val_get (val_loc l)) s (Fmap.read s l)
  | eval_set : forall s l v,
      Fmap.indom s l ->
      eval s (val_set (val_loc l) v) (Fmap.update s l v) val_unit.


(* ####################################################### *)
(** * Heap predicates *)

(** For technical reasons, to enable sharing the code implementing 
    the tactic [hsimpl], we need the definitions that follow to be
    wrapped in a module. *)

Module HsimplArgs.


(* ******************************************************* *)
(** ** Hprop and entailement *)

(** Type of heap predicates *)

Definition hprop := heap -> Prop.

(** Entailment for heap predicates *)

Definition himpl (H1 H2:hprop) : Prop :=
  forall h, H1 h -> H2 h.

Notation "H1 ==> H2" := (himpl H1 H2) (at level 55).

(** Entailment between postconditions *)

Definition qimpl A (Q1 Q2:A->hprop) : Prop :=
  forall (v:A), Q1 v ==> Q2 v.

Notation "Q1 ===> Q2" := (qimpl Q1 Q2) (at level 55).

(** Implicit Types *)

Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.


(* ******************************************************* *)
(** ** Definition of heap predicates *)

(** Core heap predicates *)

Definition hempty : hprop :=
  fun h => (h = Fmap.empty).

Definition hsingle (l:loc) (v:val) : hprop :=
  fun h => (h = Fmap.single l v).

Definition hstar (H1 H2 : hprop) : hprop :=
  fun h => exists h1 h2, H1 h1
                              /\ H2 h2
                              /\ Fmap.disjoint h1 h2
                              /\ h = Fmap.union h1 h2.

Definition hexists A (J:A->hprop) : hprop :=
  fun h => exists x, J x h.

Definition hforall (A : Type) (J : A -> hprop) : hprop :=
  fun h => forall x, J x h.

Notation "\[]" := (hempty)
  (at level 0).

Notation "l '~~~>' v" := (hsingle l v) (at level 32).

Notation "H1 '\*' H2" := (hstar H1 H2)
  (at level 41, right associativity).

Notation "'\exists' x1 .. xn , H" :=
  (hexists (fun x1 => .. (hexists (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\exists' '/ '  x1  ..  xn , '/ '  H ']'").

Notation "'\forall' x1 .. xn , H" :=
  (hforall (fun x1 => .. (hforall (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\forall' '/ '  x1  ..  xn , '/ '  H ']'").

(** Derived heap predicates.

    The following operators are defined in terms of the ones
    above, rather than as functions over heaps, to reduce the
    proof effort. (See the summary in [SLFWand.v] for details.) *)

Definition hpure (P:Prop) : hprop :=
  \exists (p:P), \[].

Definition htop : hprop :=
  \exists (H:hprop), H.

Definition hwand (H1 H2 : hprop) : hprop :=
  \exists H0, H0 \* hpure ((H0 \* H1) ==> H2).

Definition qwand A (Q1 Q2:A->hprop) :=
  \forall x, hwand (Q1 x) (Q2 x).

Notation "\[ P ]" := (hpure P)
  (at level 0, format "\[ P ]").

Notation "\Top" := (htop).

Notation "Q \*+ H" := (fun x => hstar (Q x) H)
  (at level 40).

Notation "H1 \-* H2" := (hwand H1 H2)
  (at level 43, right associativity).

Notation "Q1 \--* Q2" := (qwand Q1 Q2)
  (at level 43).


(* ******************************************************* *)
(** ** Basic properties of Separation Logic operators *)

(* ---------------------------------------------------------------------- *)
(* ** Tactic for automation *)

(** [auto] is set up to process goals of the form [h1 = h2] by calling
    [fmap_eq], which proves equality modulo associativity and commutativity. *)

Hint Extern 1 (_ = _ :> heap) => fmap_eq.

(** [auto] is set up to process goals of the form [Fmap.disjoint h1 h2] by calling
    [fmap_disjoint], which essentially normalizes all disjointness goals and
    hypotheses, split all conjunctions, and invokes proof search with a base
    of hints specified in [Fmap.v]. *)

Import Fmap.DisjointHints.

Tactic Notation "fmap_disjoint_pre" :=
  subst; rew_disjoint; jauto_set.

Hint Extern 1 (Fmap.disjoint _ _) => fmap_disjoint_pre.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [himpl] and [qimpl] *)

Lemma himpl_refl : forall H,
  H ==> H.
Proof using. introv M. auto. Qed.

Hint Resolve himpl_refl.

Lemma himpl_trans : forall H2 H1 H3,
  (H1 ==> H2) ->
  (H2 ==> H3) ->
  (H1 ==> H3).
Proof using. introv M1 M2. intros h H1h. eauto. Qed.

Lemma himpl_trans_r : forall H2 H1 H3,
   H2 ==> H3 ->
   H1 ==> H2 ->
   H1 ==> H3.
Proof using. introv M1 M2. applys* himpl_trans M2 M1. Qed.

Lemma himpl_antisym : forall H1 H2,
  (H1 ==> H2) ->
  (H2 ==> H1) ->
  (H1 = H2).
Proof using. introv M1 M2. applys pred_ext_1. intros h. iff*. Qed.

Lemma himpl_forall_trans : forall H1 H2,
  (forall H, H ==> H1 -> H ==> H2) ->
  H1 ==> H2.
Proof using. introv M. applys~ M. Qed.

Lemma qimpl_refl : forall A (Q:A->hprop),
  Q ===> Q.
Proof using. intros. hnfs*. Qed.

Hint Resolve qimpl_refl.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [hempty] *)

Lemma hempty_intro :
  \[] heap_empty.
Proof using. hnfs~. Qed.

Lemma hempty_inv : forall h,
  \[] h ->
  h = heap_empty.
Proof using. auto. Qed.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [hstar] *)

Lemma hstar_intro : forall H1 H2 h1 h2,
  H1 h1 ->
  H2 h2 ->
  Fmap.disjoint h1 h2 ->
  (H1 \* H2) (h1 \u h2).
Proof using. intros. exists~ h1 h2. Qed.

Lemma hstar_inv : forall H1 H2 h,
  (H1 \* H2) h ->
  exists h1 h2, H1 h1 /\ H2 h2 /\ Fmap.disjoint h1 h2 /\ h = h1 \u h2.
Proof using. introv M. hnf in M. eauto. Qed.

Lemma hstar_comm : forall H1 H2,
   H1 \* H2 = H2 \* H1.
Proof using.
  intros H1 H2. unfold hprop, hstar. extens. intros h.
  iff (h1&h2&M1&M2&D&U); rewrite~ Fmap.union_comm_of_disjoint in U; 
  exists* h2 h1.
Qed.

Lemma hstar_assoc : forall H1 H2 H3,
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).
Proof using.
  intros H1 H2 H3. applys pred_ext_1. intros h. split.
  { intros (h'&h3&(h1&h2&M3&M4&D'&U')&M2&D&U). subst h'.
    exists h1 (h2 \+ h3). splits~. { exists* h2 h3. } }
  { intros (h1&h'&M1&(h2&h3&M3&M4&D'&U')&D&U). subst h'.
    exists (h1 \+ h2) h3. splits~. { exists* h1 h2. } }
Qed.

Lemma hstar_hempty_l : forall H,
  hempty \* H = H.
Proof using.
  intros. applys pred_ext_1. intros h.
  iff (h1&h2&M1&M2&D&U) M.
  { forwards E: hempty_inv M1. subst.
    rewrite~ Fmap.union_empty_l. }
  { exists heap_empty h. splits~. applys hempty_intro. }
Qed.

Lemma hstar_hempty_r : forall H,
  H \* \[] = H.
Proof using.
  applys neutral_r_of_comm_neutral_l.
  applys~ hstar_comm.
  applys~ hstar_hempty_l.
Qed.

Lemma hstar_hexists : forall A (J:A->hprop) H,
  (hexists J) \* H = hexists (fun x => (J x) \* H).
Proof using.
  intros. applys pred_ext_1. intros h. iff M.
  { destruct M as (h1&h2&(x&M1)&M2&D&U). exists~ x h1 h2. }
  { destruct M as (x&(h1&h2&M1&M2&D&U)). exists h1 h2. splits~. exists~ x. }
Qed.

Lemma hstar_hforall : forall H A (J:A->hprop),
  (hforall J) \* H ==> hforall (J \*+ H).
Proof using.
  intros. intros h M. destruct M as (h1&h2&M1&M2&D&U). intros x. exists~ h1 h2.
Qed.

Lemma himpl_frame_l : forall H2 H1 H1',
  H1 ==> H1' ->
  (H1 \* H2) ==> (H1' \* H2).
Proof using. introv W (h1&h2&?). exists* h1 h2. Qed.

Lemma himpl_frame_r : forall H1 H2 H2',
  H2 ==> H2' ->
  (H1 \* H2) ==> (H1 \* H2').
Proof using.
  introv M. do 2 rewrite (@hstar_comm H1). applys~ himpl_frame_l.
Qed.

Lemma himpl_frame_lr : forall H1 H1' H2 H2',
  H1 ==> H1' ->
  H2 ==> H2' ->
  (H1 \* H2) ==> (H1' \* H2').
Proof using.
  introv M1 M2. applys himpl_trans. applys~ himpl_frame_l M1. applys~ himpl_frame_r.
Qed.

Lemma himpl_hstar_trans_l : forall H1 H2 H3 H4,
  H1 ==> H2 ->
  H2 \* H3 ==> H4 ->
  H1 \* H3 ==> H4.
Proof using.
  introv M1 M2. applys himpl_trans M2. applys himpl_frame_l M1. 
Qed.

Lemma himpl_hstar_trans_r : forall H1 H2 H3 H4,
  H1 ==> H2 ->
  H3 \* H2 ==> H4 ->
  H3 \* H1 ==> H4.
Proof using.
  introv M1 M2. applys himpl_trans M2. applys himpl_frame_r M1. 
Qed.


(* ---------------------------------------------------------------------- *)
(** Properties of [hpure] *)

Lemma hpure_intro : forall P,
  P ->
  \[P] heap_empty.
Proof using. introv M. exists M. hnfs*. Qed.

Lemma hpure_inv : forall P h,
  \[P] h ->
  P /\ h = heap_empty.
Proof using. introv (p&M). split~. Qed.

Lemma hstar_hpure : forall P H h, 
  (\[P] \* H) h = (P /\ H h).
Proof using.
  intros. extens. unfold hpure.
  rewrite hstar_hexists.
  rewrite* hstar_hempty_l.
  iff (p&M) (p&M). { split~. } { exists~ p. }
Qed.

Lemma hstar_hpure_iff : forall P H h,
  (\[P] \* H) h <-> (P /\ H h).
Proof using. intros. rewrite* hstar_hpure. Qed.

Lemma himpl_hstar_hpure_r : forall P H H',
  P ->
  (H ==> H') ->
  H ==> (\[P] \* H').
Proof using.
  introv HP W. intros h K. rewrite* hstar_hpure.
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


(* ---------------------------------------------------------------------- *)
(** Properties of [hexists] *)

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

(* not needed *)
Lemma himpl_hexists : forall A (J1 J2:A->hprop),
  J1 ===> J2 ->
  hexists J1 ==> hexists J2.
Proof using.
  introv W. applys himpl_hexists_l. intros x. applys himpl_hexists_r W.
Qed.


(* ---------------------------------------------------------------------- *)
(** Properties of [hforall] *)

Lemma himpl_hforall_r : forall A (J:A->hprop) H,
  (forall x, H ==> J x) ->
  H ==> (hforall J).
Proof using. introv M. intros h Hh x. apply~ M. Qed.

Lemma himpl_hforall_l : forall A x (J:A->hprop) H,
  (J x ==> H) ->
  (hforall J) ==> H.
Proof using. introv M. intros h Hh. apply~ M. Qed.

Lemma hforall_specialize : forall A (x:A) (J:A->hprop),
  (hforall J) ==> (J x).
Proof using. intros. applys* himpl_hforall_l x. Qed.

(* not needed *)
Lemma himpl_hforall : forall A (J1 J2:A->hprop),
  J1 ===> J2 ->
  hforall J1 ==> hforall J2.
Proof using.
  introv W. applys himpl_hforall_r. intros x. applys himpl_hforall_l W.
Qed.


(* ---------------------------------------------------------------------- *)
(** Properties of [hwand] *)

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

Lemma hwand_cancel : forall H1 H2,
  H1 \* (H1 \-* H2) ==> H2.
Proof using. intros. rewrite hstar_comm. rewrite~ <- hwand_equiv. Qed.

Arguments hwand_cancel : clear implicits.

Lemma himpl_hempty_hwand_same : forall H,
  \[] ==> (H \-* H).
Proof using. intros. rewrite hwand_equiv. rewrite~ hstar_hempty_l. Qed.

Lemma hwand_hempty_l : forall H,
  (\[] \-* H) = H.
Proof using.
  intros. applys himpl_antisym.
  { rewrite <- (hstar_hempty_l (\[] \-* H)). applys hwand_cancel. }
  { rewrite hwand_equiv. rewrite~ hstar_hempty_r. }
Qed.

Lemma hwand_hpure_l_intro : forall (P:Prop) H,
  P ->
  \[P] \-* H ==> H.
Proof using. 
  introv HP. rewrite <- (hstar_hempty_l (\[P] \-* H)).
  forwards~ K: himpl_hempty_hpure P.
  applys* himpl_hstar_trans_l K. applys hwand_cancel.
Qed.

Arguments hwand_hpure_l_intro : clear implicits.

Lemma hwand_curry : forall H1 H2 H3,
  (H1 \* H2) \-* H3 ==> H1 \-* (H2 \-* H3).
Proof using.
  intros. do 2 rewrite hwand_equiv.
  rewrite hstar_assoc. rewrite hstar_comm. applys hwand_cancel.
Qed.

Lemma hwand_uncurry : forall H1 H2 H3,
  H1 \-* (H2 \-* H3) ==> (H1 \* H2) \-* H3.
Proof using.
  intros. rewrite hwand_equiv. rewrite <- (hstar_comm (H1 \* H2)). 
  rewrite (@hstar_comm H1). rewrite hstar_assoc.
  applys himpl_trans. applys himpl_frame_r. applys hwand_cancel.
  applys hwand_cancel.
Qed.

Lemma hwand_curry_eq : forall H1 H2 H3,
  (H1 \* H2) \-* H3 = H1 \-* (H2 \-* H3).
Proof using.
  intros. applys himpl_antisym.
  { applys hwand_curry. }
  { applys hwand_uncurry. }
Qed.


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

Lemma qwand_specialize : forall A (x:A) (Q1 Q2:A->hprop),
  (Q1 \--* Q2) ==> (Q1 x \-* Q2 x).
Proof using.
  intros. applys himpl_forall_trans. intros H M.
  rewrite qwand_equiv in M. specializes M x.
  rewrite hwand_equiv. rewrite~ hstar_comm.
Qed.

Arguments qwand_specialize [ A ].


(* ---------------------------------------------------------------------- *)
(** Properties of [htop] *)

Lemma htop_intro : forall h,
  \Top h.
Proof using. intros. exists~ (=h). Qed.

Lemma himpl_htop_r : forall H,
  H ==> \Top.
Proof using. intros. intros h Hh. applys* htop_intro. Qed.

Lemma htop_eq :
  \Top = (\exists H, H).
Proof using. auto. Qed.

Lemma hstar_htop_htop :
  \Top \* \Top = \Top.
Proof using.
  applys himpl_antisym.
  { applys himpl_htop_r. }
  { applys himpl_forall_trans. intros H M. applys himpl_trans M.
    rewrite <- (hstar_hempty_r \Top) at 1. applys himpl_frame_r.
    applys himpl_htop_r. }
Qed.


(* ---------------------------------------------------------------------- *)
(** Properties of [hsingle] *)

Lemma hsingle_intro : forall l v,
  (l ~~~> v) (Fmap.single l v).
Proof using. intros. hnfs*. Qed.

Lemma hsingle_inv: forall l v h,
  (l ~~~> v) h ->
  h = Fmap.single l v.
Proof using. auto. Qed.

Lemma hstar_hsingle_same_loc : forall l v1 v2,
  (l ~~~> v1) \* (l ~~~> v2) ==> \[False].
Proof using.
  intros. unfold hsingle. intros h (h1&h2&E1&E2&D&E). false.
  subst. applys* Fmap.disjoint_single_single_same_inv.
Qed.


(* ******************************************************* *)
(** ** Hsimpl tactic *)

(** The definitions and properties above enable us to instantiate
    the [hsimpl] tactic, which implements powerful simplifications
    for Separation Logic entailments. 

    For technical reasons, we need to provide a definition for [hgc],
    a restriction of [htop] to affine heap predicates. For our purpose,
    it suffices to define [hgc] as an alias for [htop]. *)

(* ---------------------------------------------------------------------- *)
(** Definition and properties of hgc *)

Definition hgc := htop.

Notation "\GC" := (hgc).

Definition haffine := fun H => True.

Lemma haffine_hempty :
  haffine \[].
Proof using. hnfs*. Qed.

Lemma himpl_hgc_r : forall H,
  haffine H ->
  H ==> \GC.
Proof using. introv M. applys himpl_htop_r. Qed.

Lemma hstar_hgc_hgc :
  \GC \* \GC = \GC.
Proof using. applys hstar_htop_htop. Qed.


(* ---------------------------------------------------------------------- *)
(** Functor instantiation to obtain [hsimpl] *)

End HsimplArgs. 

(** We are now ready to instantiate the functor. *)

Module Export HS := Hsimpl.HsimplSetup(HsimplArgs).

(** At this point, the tactic [hsimpl] is available.
    See the file [SLFHimpl.v] for demos of its usage. *)  

(** And we open the module [HsimplArgs], essentially pretending
    that it was never created. *)

Export HsimplArgs.


(* ####################################################### *)
(** * Reasoning rules *)


(* ******************************************************* *)
(** ** Evaluation rules for primitives in Separation style *)

(** It is not needed to follow through these proofs. *)

Lemma eval_get_sep : forall s s2 l v, 
  s = Fmap.union (Fmap.single l v) s2 ->
  eval s (val_get (val_loc l)) s v.
Proof using.
  introv ->. forwards Dv: Fmap.indom_single l v.
  applys_eq eval_get 1.
  { applys~ Fmap.indom_union_l. }
  { rewrite~ Fmap.read_union_l. rewrite~ Fmap.read_single. }
Qed.

Lemma eval_set_sep : forall s1 s2 h2 l v1 v2,
  s1 = Fmap.union (Fmap.single l v1) h2 ->
  s2 = Fmap.union (Fmap.single l v2) h2 ->
  Fmap.disjoint (Fmap.single l v1) h2 ->
  eval s1 (val_set (val_loc l) v2) s2 val_unit.
Proof using.
  introv -> -> D. forwards Dv: Fmap.indom_single l v1.
  applys_eq eval_set 2.
  { applys~ Fmap.indom_union_l. }
  { rewrite~ Fmap.update_union_l. fequals.
    rewrite~ Fmap.update_single. }
Qed.

Lemma eval_ref_sep : forall s1 s2 v l,
  s2 = Fmap.single l v ->
  Fmap.disjoint s2 s1 ->
  eval s1 (val_ref v) (Fmap.union s2 s1) (val_loc l).
Proof using.
  introv -> D. forwards Dv: Fmap.indom_single l v.
  rewrite <- Fmap.update_eq_union_single. applys~ eval_ref.
  { intros N. applys~ Fmap.disjoint_inv_not_indom_both D N. }
Qed.


(* ******************************************************* *)
(** ** Hoare reasoning rules *)

(** * Definition of Hoare triples *)

Definition hoare (t:trm) (H:hprop) (Q:val->hprop) :=
  forall h, H h -> exists h' v, eval h t h' v /\ Q v h'.

(** The tactic [himpl_fold] applies to a goal of the form [H1 h].
    It searches the context for an assumption of the from [H2 h],
    then replaces the goal with [H1 ==> H2].
    It also deletes the assumption [H2 h]. *)

Lemma himpl_inv : forall H1 H2 h,
  (H1 ==> H2) ->
  (H1 h) ->
  (H2 h).
Proof using. auto. Qed.

Ltac himpl_fold_core tt :=
  match goal with N: ?H ?h |- _ ?h =>
    applys himpl_inv N; clear N end.

Tactic Notation "himpl_fold" := himpl_fold_core tt.
Tactic Notation "himpl_fold" "~" := himpl_fold; auto_tilde.
Tactic Notation "himpl_fold" "*" := himpl_fold; auto_star.

(** Structural rules for [hoare] triples. *)

Lemma hoare_conseq : forall t H' Q' H Q,
  hoare t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  hoare t H Q.
Proof using.
  introv M MH MQ HF. forwards (h'&v&R&K): M h.
  { himpl_fold~. }
  exists h' v. splits~. { himpl_fold. auto. }
Qed.

Lemma hoare_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, hoare t (J x) Q) ->
  hoare t (hexists J) Q.
Proof using. introv M. intros h (x&Hh). applys M Hh. Qed.

Lemma hoare_hpure : forall t (P:Prop) H Q,
  (P -> hoare t H Q) ->
  hoare t (\[P] \* H) Q.
Proof using.
  introv M. intros h (h1&h2&M1&M2&D&U). destruct M1 as (M1&HP).
  lets E: hempty_inv HP. subst. rewrite Fmap.union_empty_l. applys~ M. 
Qed.

(** Reasoning rules for [hoare] triples. *)

Lemma hoare_val : forall v H Q,
  H ==> Q v ->
  hoare (trm_val v) H Q.
Proof using.
  introv M. intros h Hh. exists h v. splits.
  { applys eval_val. }
  { himpl_fold~. }
Qed.

Lemma hoare_fun : forall x t1 H Q,
  H ==> Q (val_fun x t1) ->
  hoare (trm_fun x t1) H Q.
Proof using.
  introv M. intros h Hh. exists___. splits.
  { applys~ eval_fun. }
  { himpl_fold~. }
Qed.

Lemma hoare_fix : forall f x t1 H Q,
  H ==> Q (val_fix f x t1) ->
  hoare (trm_fix f x t1) H Q.
Proof using.
  introv M. intros h Hh. exists___. splits.
  { applys~ eval_fix. }
  { himpl_fold~. }
Qed.

Lemma hoare_app_fun : forall v1 v2 x t1 H Q,
  v1 = val_fun x t1 ->
  hoare (subst x v2 t1) H Q ->
  hoare (trm_app v1 v2) H Q.
Proof using.
  introv E M. intros s K0. forwards (s'&v&R1&K1): (rm M) K0.
  exists s' v. splits. { applys eval_app_fun E R1. } { applys K1. }
Qed.

Lemma hoare_app_fix : forall v1 v2 f x t1 H Q,
  v1 = val_fix f x t1 ->
  hoare (subst x v2 (subst f v1 t1)) H Q ->
  hoare (trm_app v1 v2) H Q.
Proof using.
  introv E M. intros s K0. forwards (s'&v&R1&K1): (rm M) K0.
  exists s' v. splits. { applys eval_app_fix E R1. } { applys K1. }
Qed.

Lemma hoare_seq : forall t1 t2 H Q H1,
  hoare t1 H (fun r => H1) ->
  hoare t2 H1 Q ->
  hoare (trm_seq t1 t2) H Q.
Proof using.
  introv M1 M2 Hh.
  forwards* (h1'&v1&R1&K1): (rm M1).
  forwards* (h2'&v2&R2&K2): (rm M2).
  exists h2' v2. splits~. { applys~ eval_seq R1 R2. }
Qed.

Lemma hoare_let : forall z t1 t2 H Q Q1,
  hoare t1 H Q1 ->
  (forall v, hoare (subst z v t2) (Q1 v) Q) ->
  hoare (trm_let z t1 t2) H Q.
Proof using.
  introv M1 M2 Hh.
  forwards* (h1'&v1&R1&K1): (rm M1).
  forwards* (h2'&v2&R2&K2): (rm M2).
  exists h2' v2. splits~. { applys~ eval_let R2. }
Qed.

Lemma hoare_if_case : forall (b:bool) t1 t2 H Q,
  hoare (if b then t1 else t2) H Q ->
  hoare (trm_if b t1 t2) H Q.
Proof using.
  introv M1. intros h Hh. forwards* (h1'&v1&R1&K1): (rm M1).
  exists h1' v1. splits~. { applys* eval_if_case. }
Qed.

Lemma hoare_add : forall H n1 n2,
  hoare (val_add n1 n2)
    H
    (fun r => \[r = val_int (n1 + n2)] \* H).
Proof using.
  intros. intros s K0. exists s (val_int (n1 + n2)). split.
  { applys eval_add. }
  { rewrite hstar_hpure_iff. split.
    { auto. }
    { applys K0. } }
Qed.

Lemma hoare_ref : forall H v,
  hoare (val_ref v)
    H
    (fun r => (\exists l, \[r = val_loc l] \* l ~~~> v) \* H).
Proof using.
  intros. intros s1 K0.
  forwards~ (l&D&_): (Fmap.single_fresh 0%nat s1 v).
  exists (Fmap.union (Fmap.single l v) s1) (val_loc l). split.
  { applys~ eval_ref_sep D. }
  { applys hstar_intro.
    { exists l. rewrite hstar_hpure.
      split. { auto. } { applys hsingle_intro. } }
    { applys K0. }
    { applys D. } }
Qed.

Lemma hoare_get : forall H v l,
  hoare (val_get l)
    ((l ~~~> v) \* H)
    (fun r => \[r = v] \* (l ~~~> v) \* H).
Proof using.
  intros. intros s K0. 
  exists s v. split.
  { destruct K0 as (s1&s2&P1&P2&D&U).
    lets E1: hsingle_inv P1. subst s1.
    applys eval_get_sep U. }
  { rewrite hstar_hpure. auto. }
Qed.

Lemma hoare_set : forall H w l v,
  hoare (val_set (val_loc l) w)
    ((l ~~~> v) \* H)
    (fun r => \[r = val_unit] \* (l ~~~> w) \* H).
Proof using.
  intros. intros s1 K0.
  destruct K0 as (h1&h2&P1&P2&D&U).
  lets E1: hsingle_inv P1.
  exists ((Fmap.single l w) \u h2) val_unit. split.
  { subst h1. applys eval_set_sep U D. auto. }
  { rewrite hstar_hpure. split.
    { auto. }
    { applys hstar_intro.
      { applys hsingle_intro. }
      { applys P2. }
      { subst h1. applys Fmap.disjoint_single_set D. } } }
Qed.


(* ******************************************************* *)
(** ** Definition of [wp] and reasoning rules *)


(* ---------------------------------------------------------------------- *)
(** Definition of [wp] w.r.t. [hoare]  *)

Definition wp (t:trm) := fun (Q:val->hprop) =>
  \exists H, H \* \[forall H', hoare t (H \* H') (Q \*+ H' \*+ \Top)].


(* ---------------------------------------------------------------------- *)
(** Structural rule for [wp]. *)

Lemma wp_ramified : forall Q1 Q2 t,
  (wp t Q1) \* (Q1 \--* Q2 \*+ \Top) ==> (wp t Q2).
Proof using.
  intros. unfold wp. hpull ;=> H M.
  hsimpl (H \* (Q1 \--* Q2 \*+ \Top)). intros H'.
  applys hoare_conseq M; hsimpl.
Qed.

Arguments wp_ramified : clear implicits.

(** Corollaries *)

Lemma wp_conseq : forall t Q1 Q2,
  Q1 ===> Q2 ->
  wp t Q1 ==> wp t Q2.
Proof using. 
  introv M. applys himpl_trans_r (wp_ramified Q1 Q2). hsimpl. hchanges M.
Qed.

Lemma wp_frame : forall t H Q,
  (wp t Q) \* H ==> wp t (Q \*+ H).
Proof using. intros. applys himpl_trans_r wp_ramified. hsimpl. Qed.

Lemma wp_ramified_frame : forall t Q1 Q2,
  (wp t Q1) \* (Q1 \--* Q2) ==> (wp t Q2).
Proof using. intros. applys himpl_trans_r wp_ramified. hsimpl. Qed.

Lemma wp_hany_pre : forall t H Q,
  (wp t Q) \* H ==> wp t Q.
Proof using. intros. applys himpl_trans_r wp_ramified. hsimpl. Qed.

Lemma wp_hany_post : forall t H Q ,
  wp t (Q \*+ H) ==> wp t Q.
Proof using. intros. applys himpl_trans_r wp_ramified. hsimpl. Qed.


(* ---------------------------------------------------------------------- *)
(** Reasoning rules for terms. *)

Lemma wp_val : forall v Q,
  Q v ==> wp (trm_val v) Q.
Proof using. intros. unfold wp. hsimpl; intros H'. applys hoare_val. hsimpl. Qed.

Lemma wp_fun : forall x t Q,
  Q (val_fun x t) ==> wp (trm_fun x t) Q.
Proof using. intros. unfold wp. hsimpl; intros H'. applys hoare_fun. hsimpl. Qed.

Lemma wp_fix : forall f x t Q,
  Q (val_fix f x t) ==> wp (trm_fix f x t) Q.
Proof using. intros. unfold wp. hsimpl; intros H'. applys hoare_fix. hsimpl. Qed.

Lemma wp_app_fun : forall x v1 v2 t1 Q,
  v1 = val_fun x t1 ->
  wp (subst x v2 t1) Q ==> wp (v1 v2) Q.
Proof using. introv EQ1. unfold wp. hsimpl; intros. applys* hoare_app_fun. Qed.

Lemma wp_app_fix : forall f x v1 v2 t1 Q,
  v1 = val_fix f x t1 ->
  wp (subst x v2 (subst f v1 t1)) Q ==> wp (v1 v2) Q.
Proof using. introv EQ1. unfold wp. hsimpl; intros. applys* hoare_app_fix. Qed.

Lemma wp_seq : forall t1 t2 Q,
  wp t1 (fun r => wp t2 Q) ==> wp (trm_seq t1 t2) Q.
Proof using.
  intros. unfold wp at 1. hsimpl. intros H' M1.
  unfold wp at 1. hsimpl. intros H''.
  applys hoare_seq. applys (rm M1). unfold wp.
  repeat rewrite hstar_hexists. applys hoare_hexists; intros H'''.
  rewrite (hstar_comm H'''); repeat rewrite hstar_assoc.
  applys hoare_hpure; intros M2. applys hoare_conseq M2; hsimpl.
Qed.

Lemma wp_let : forall x t1 t2 Q,
  wp t1 (fun v => wp (subst x v t2) Q) ==> wp (trm_let x t1 t2) Q.
Proof using.
  intros. unfold wp at 1. hsimpl. intros H' M1.
  unfold wp at 1. hsimpl. intros H''.
  applys hoare_let. applys (rm M1). intros v. simpl. unfold wp.
  repeat rewrite hstar_hexists. applys hoare_hexists; intros H'''.
  rewrite (hstar_comm H'''); repeat rewrite hstar_assoc.
  applys hoare_hpure; intros M2. applys hoare_conseq M2; hsimpl.
Qed.

Lemma wp_if_case : forall b t1 t2 Q,
  wp (if b then t1 else t2) Q ==> wp (trm_if b t1 t2) Q.
Proof using.
  intros. repeat unfold wp. hsimpl; intros H M H'.
  applys hoare_if_case. applys M.
Qed.

Lemma wp_if : forall b t1 t2 Q,
  (if b then wp t1 Q else wp t2 Q) ==> wp (trm_if b t1 t2) Q.
Proof using. intros. applys himpl_trans wp_if_case. case_if~. Qed.


(* ******************************************************* *)
(** ** Definition of triple and equivalence *)

Definition triple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall (H':hprop), hoare t (H \* H') (Q \*+ H' \*+ \Top).

Lemma wp_equiv : forall t H Q,
  (triple t H Q) <-> (H ==> wp t Q).
Proof using.
  unfold wp, triple. iff M.
  { hsimpl H. apply M. }
  { intros H'. applys hoare_conseq. 2:{ applys himpl_frame_l M. }
     { clear M. rewrite hstar_hexists. applys hoare_hexists. intros H''.
       rewrite (hstar_comm H''). rew_heap. applys hoare_hpure. intros N.
       applys N. } 
     { auto. } }
Qed.


(* ******************************************************* *)
(** ** Specification for primitive functions *)

Lemma triple_add : forall n1 n2,
  triple (val_add n1 n2)
    \[]
    (fun r => \[r = val_int (n1 + n2)]).
Proof using.
  intros. unfold triple. intros H'. applys hoare_conseq hoare_add; hsimpl~.
Qed.

Lemma triple_ref : forall v,
  triple (val_ref v)
    \[]
    (fun r => \exists l, \[r = val_loc l] \* l ~~~> v).
Proof using.
  intros. unfold triple. intros H'. applys hoare_conseq hoare_ref; hsimpl~.
Qed.

Lemma triple_get : forall v l,
  triple (val_get l)
    (l ~~~> v)
    (fun r => \[r = v] \* (l ~~~> v)).
Proof using.
  intros. unfold triple. intros H'. applys hoare_conseq hoare_get; hsimpl~.
Qed.

Lemma triple_set : forall w l v,
  triple (val_set (val_loc l) w)
    (l ~~~> v)
    (fun r => \[r = val_unit] \* l ~~~> w).
Proof using.
  intros. unfold triple. intros H'. applys hoare_conseq hoare_set; hsimpl~.
Qed.


(* ####################################################### *)
(** * WP generator *)


(* ******************************************************* *)
(** ** Definition of context as list of bindings *)

(** This formalization of contexts leverages TLC definitions.
    For direct definitions, open file [SLFWPgen.v]. *)

Open Scope liblist_scope.

(** A context is an association list from variables to values. *)

Definition ctx : Type := list (var*val).

(** [rem x E] denotes the removal of bindings on [x] from [E]. *)

Definition rem : var -> ctx -> ctx := 
  @LibListAssocExec.rem var var_eq val.

(** [lookup x E] returns [Some v] if [x] is bound to a value [v],
    and [None] otherwise. *)

Definition lookup : var -> ctx -> option val := 
  @LibListAssocExec.get_opt var var_eq val.

(** [ctx_disjoint E1 E2] asserts that the two contexts have disjoint
    domains. *)

Definition ctx_disjoint (E1 E2:ctx) : Prop := 
  forall x v1 v2, lookup x E1 = Some v1 -> lookup x E2 = Some v2 -> False.

(** [ctx_equiv E1 E2] asserts that the two contexts bind same
    keys to same values. *)

Definition ctx_equiv (E1 E2:ctx) : Prop :=
  forall x, lookup x E1 = lookup x E2.

(** Basic properties of context operations follow. *)

Section CtxOps.

Lemma is_beq_var_eq :
  LibListAssocExec.is_beq var_eq.
Proof using. applys var_eq_spec. Qed.

Hint Resolve is_beq_var_eq.

Lemma ctx_equiv_eq :
  ctx_equiv = @LibListAssoc.equiv var val.
Proof using.
  intros. extens. intros E1 E2.
  unfold ctx_equiv, lookup, LibListAssoc.equiv. iff M.
  { intros x. specializes M x. do 2 rewrite~ LibListAssocExec.get_opt_eq in M. }
  { intros x. do 2 rewrite~ LibListAssocExec.get_opt_eq. }
Qed.

Lemma ctx_disjoint_eq :
  ctx_disjoint = @LibListAssoc.disjoint var val.
Proof using.
  intros. extens. intros E1 E2.
  unfold ctx_disjoint, lookup, LibListAssoc.disjoint. iff M; intros x v1 v2 K1 K2.
  { applys M; rewrite* LibListAssocExec.get_opt_eq. }
  { rewrite LibListAssocExec.get_opt_eq in K1, K2; auto. applys* M. }
Qed.

Lemma lookup_nil : forall y,
  lookup y (nil:ctx) = None.
Proof using.
  intros. unfold lookup. rewrite~ LibListAssocExec.get_opt_eq. 
Qed.

Lemma lookup_cons : forall x v E y,
  lookup y ((x,v)::E) = (If x = y then Some v else lookup y E).
Proof using.
  intros. unfold lookup. repeat rewrite~ LibListAssocExec.get_opt_eq.
Qed.

Lemma lookup_app : forall E1 E2 x,
  lookup x (E1 ++ E2) = match lookup x E1 with
                         | None => lookup x E2
                         | Some v => Some v
                         end.
Proof using. 
  intros. unfold lookup. repeat rewrite~ LibListAssocExec.get_opt_eq.
  applys~ LibListAssoc.get_opt_app.
Qed.

Lemma lookup_rem : forall x y E,
  lookup x (rem y E) = If x = y then None else lookup x E.
Proof using. 
  intros. unfold lookup, rem. repeat rewrite~ LibListAssocExec.get_opt_eq.
  repeat rewrite~ LibListAssocExec.rem_eq. applys~ LibListAssoc.get_opt_rem.
Qed.

Lemma rem_nil : forall y,
  rem y (nil:ctx) = nil.
Proof using.
  intros. unfold rem. rewrite~ LibListAssocExec.rem_eq.
Qed.

Lemma rem_cons : forall x v E y,
  rem y ((x,v)::E) = (If x = y then rem y E else (x,v) :: rem y E).
Proof using. 
  intros. unfold rem. repeat rewrite~ LibListAssocExec.rem_eq.
  rewrite~ LibListAssoc.rem_cons.
Qed.

Lemma rem_app : forall x E1 E2,
  rem x (E1 ++ E2) = rem x E1 ++ rem x E2.
Proof using. 
  intros. unfold rem. repeat rewrite~ LibListAssocExec.rem_eq.
  rewrite~ LibListAssoc.rem_app.
Qed.

Lemma ctx_equiv_rem : forall x E1 E2,
  ctx_equiv E1 E2 ->
  ctx_equiv (rem x E1) (rem x E2).
Proof using.
  introv M. rewrite ctx_equiv_eq in *. unfold rem.
  repeat rewrite~ LibListAssocExec.rem_eq.
  applys~ LibListAssoc.equiv_rem.
Qed.

Lemma ctx_disjoint_rem : forall x E1 E2,
  ctx_disjoint E1 E2 ->
  ctx_disjoint (rem x E1) (rem x E2).
Proof using.
  introv M. rewrite ctx_disjoint_eq in *. unfold rem.
  repeat rewrite~ LibListAssocExec.rem_eq.
  applys~ LibListAssoc.disjoint_rem.
Qed.

End CtxOps.

Hint Rewrite lookup_nil lookup_cons rem_nil rem_cons : rew_ctx.

Tactic Notation "rew_ctx" :=
   autorewrite with rew_ctx.


(* ******************************************************* *)
(** ** Definition of multi-substitution *)

Fixpoint isubst (E:ctx) (t:trm) : trm :=
  match t with
  | trm_val v =>
       v
  | trm_var x =>
       match lookup x E with
       | None => t
       | Some v => v
       end
  | trm_fun x t1 =>
       trm_fun x (isubst (rem x E) t1)
  | trm_fix f x t1 =>
       trm_fix f x (isubst (rem x (rem f E)) t1)
  | trm_if t0 t1 t2 =>
       trm_if (isubst E t0) (isubst E t1) (isubst E t2)
  | trm_seq t1 t2 =>
       trm_seq (isubst E t1) (isubst E t2)
  | trm_let x t1 t2 =>
       trm_let x (isubst E t1) (isubst (rem x E) t2)
  | trm_app t1 t2 => 
       trm_app (isubst E t1) (isubst E t2)
  end.


(* ******************************************************* *)
(** ** Definition of [mkstruct] *)

(** Let [formula] denote the type of [wp t] and [wpgen t]. *)

Definition formula := (val -> hprop) -> hprop.

Implicit Type F : formula.

(** [mkstruct F] transforms a formula [F] into one that satisfies 
    structural rules of Separation Logic. *)

Definition mkstruct (F:formula) : formula :=
  fun Q => \exists Q', F Q' \* (Q' \--* (Q \*+ \GC)).

Lemma mkstruct_ramified : forall Q1 Q2 F,
  (mkstruct F Q1) \* (Q1 \--* Q2 \*+ \Top) ==> (mkstruct F Q2).
Proof using. unfold mkstruct. hsimpl. Qed.

Arguments mkstruct_ramified : clear implicits.

Lemma mkstruct_erase : forall Q F,
  F Q ==> mkstruct F Q.
Proof using. unfolds mkstruct. hsimpl. Qed.

Arguments mkstruct_erase : clear implicits.


(* ******************************************************* *)
(** ** Definition of [wpgen] *)

Definition wpgen_fail : formula := fun Q =>
  \[False].

Definition wpgen_val (v:val) : formula := fun Q =>
  Q v.

Definition wpgen_var (E:ctx) (x:var) : formula :=
  match lookup x E with
  | None => wpgen_fail
  | Some v => wpgen_val v
  end.

Definition wpgen_seq (F1 F2:formula) : formula := fun Q =>
  F1 (fun v => F2 Q).

Definition wpgen_let (F1:formula) (F2of:val->formula) : formula := fun Q =>
  F1 (fun v => F2of v Q).

Definition wpgen_if (v:val) (F1 F2:formula) : formula := fun Q =>
  \exists (b:bool), \[v = val_bool b] \* (if b then F1 Q else F2 Q).

Definition wpgen_if_trm (F0 F1 F2:formula) : formula := 
  wpgen_let F0 (fun v => mkstruct (wpgen_if v F1 F2)).

Fixpoint wpgen (E:ctx) (t:trm) : formula :=
  mkstruct match t with
  | trm_val v =>
       wpgen_val v
  | trm_var x =>
       wpgen_var E x
  | trm_fun x t1 =>
       wpgen_val (val_fun x (isubst (rem x E) t1))
  | trm_fix f x t1 =>
       wpgen_val (val_fix f x (isubst (rem x (rem f E)) t1))
  | trm_if t0 t1 t2 =>
      match isubst E t0 with
      | trm_val v0 => wpgen_if v0 (wpgen E t1) (wpgen E t2)
      | _ => wpgen_fail
      end
  | trm_seq t1 t2 =>
       wpgen_seq (wpgen E t1) (wpgen E t2)
  | trm_let x t1 t2 =>
       wpgen_let (wpgen E t1) (fun v => wpgen ((x,v)::E) t2)
  | trm_app t1 t2 => 
       wp (isubst E t)
  end.


(* ******************************************************* *)
(** ** Properties of [isubst] *)

(** The goal of this entire section is only to establish [isubst_nil]
    and [isubst_rem], which assert:
[[
        isubst nil t = t
    and 
        isubst ((x,v)::E) t = subst x v (isubst (rem x E) t)
]]
    The proofs presented here depend on TLC library for association
    lists. A standalone formalization may be found in [SLFWPgen.v].
*)


(** The first targeted lemma. *)

Lemma isubst_nil : forall t,
  isubst nil t = t.
Proof using.
  intros t. induction t; simpl; rew_ctx; fequals.
Qed.

(** The next lemma relates [subst] and [isubst]. *)

Lemma subst_eq_isubst_one : forall x v t,
  subst x v t = isubst ((x,v)::nil) t.
Proof using.
  intros. induction t; simpl; rew_ctx.
  { fequals. }
  { case_var~. }
  { fequals. case_var~. { rewrite~ isubst_nil. } }
  { fequals. case_var; rew_ctx; try case_var; try rewrite isubst_nil; auto. }
  { fequals*. }
  { fequals*. }
  { fequals*. case_var~. { rewrite~ isubst_nil. } }
  { fequals*. }
Qed.

(** The next lemma shows that equivalent contexts produce equal
    results for [isubst] *)

Lemma isubst_ctx_equiv : forall t E1 E2,
  ctx_equiv E1 E2 ->
  isubst E1 t = isubst E2 t.
Proof using.
  hint ctx_equiv_rem.
  intros t. induction t; introv EQ; rew_ctx; simpl; fequals~.
  { rewrite~ EQ. }
Qed.

(** The next lemma asserts that [isubst] distribute over concatenation
    of disjoint contexts. *)

Lemma isubst_app : forall t E1 E2,
  ctx_disjoint E1 E2 ->
  isubst (E1 ++ E2) t = isubst E1 (isubst E2 t).
Proof using.
  hint ctx_disjoint_rem.
  intros t. induction t; introv D; simpl.
  { fequals. }
  { rename v into x. rewrite~ lookup_app.
    case_eq (lookup x E1); introv K1; case_eq (lookup x E2); introv K2.
    { false* D. }
    { simpl. rewrite~ K1. }
    { auto. }
    { simpl. rewrite~ K1. } }
  { fequals. rewrite* rem_app. }
  { fequals. do 2 rewrite* rem_app. }
  { fequals*. }
  { fequals*. }
  { fequals*. { rewrite* rem_app. } }
  { fequals*. }
Qed.

(** We are ready to derive the desired property of [isubst]
    for the soundness proof of [wp_gen]. *)

Lemma isubst_rem : forall x v E t,
  isubst ((x, v)::E) t = subst x v (isubst (rem x E) t).
Proof using.
  intros. rewrite subst_eq_isubst_one. rewrite <- isubst_app.
  { applys isubst_ctx_equiv. intros y. rew_list.
    do 2 rewrite lookup_cons. case_var~.
    { rewrite lookup_rem. case_var~. } }
  { intros y v1 v2 K1 K2. rewrite lookup_cons in K1. case_var.
    { subst. rewrite lookup_rem in K2. case_var~. } }
Qed.


(** TODO: simplify this *)
Lemma isubst_app' : forall t E1 E2,
  isubst (E1 ++ E2) t = isubst E2 (isubst E1 t).
Proof using.
  hint ctx_disjoint_rem.
  intros t. induction t; simpl; intros.
  { fequals. }
  { rename v into x. rewrite~ lookup_app.
    case_eq (lookup x E1); introv K1; case_eq (lookup x E2); introv K2; auto.
    { simpl. rewrite~ K2. }
    { simpl. rewrite~ K2. } }
  { fequals. rewrite* rem_app. }
  { fequals. do 2 rewrite* rem_app. }
  { fequals*. }
  { fequals*. }
  { fequals*. { rewrite* rem_app. } }
  { fequals*. }
Qed.


(* ******************************************************* *)
(** ** Soundness of [wpgen] *)

Definition formula_sound_for (t:trm) (F:formula) : Prop :=
  forall Q, F Q ==> wp t Q.

Lemma wp_sound : forall t,
  formula_sound_for t (wp t).
Proof using. intros. intros Q. applys himpl_refl. Qed.

Lemma mkstruct_sound : forall t F,
  formula_sound_for t F ->
  formula_sound_for t (mkstruct F).
Proof using.
  introv M. intros Q. unfold mkstruct. hsimpl ;=> Q'.
  lets N: M Q'. hchange N. applys wp_ramified.
Qed.

Lemma wpgen_fail_sound : forall t,
  formula_sound_for t wpgen_fail.
Proof using. intros. intros Q. unfold wpgen_fail. hpull. Qed.

Lemma wpgen_val_sound : forall v,
  formula_sound_for (trm_val v) (wpgen_val v).
Proof using. intros. intros Q. unfolds wpgen_val. applys wp_val. Qed.

Lemma wpgen_fun_sound : forall x t,
  formula_sound_for (trm_fun x t) (wpgen_val (val_fun x t)).

Proof using. intros. intros Q. unfolds wpgen_val. applys wp_fun. Qed.
Lemma wpgen_fix_sound : forall f x t,
  formula_sound_for (trm_fix f x t) (wpgen_val (val_fix f x t)).
Proof using. intros. intros Q. unfolds wpgen_val. applys wp_fix. Qed.

Lemma wpgen_seq_sound : forall F1 F2 t1 t2,
  formula_sound_for t1 F1 ->
  formula_sound_for t2 F2 ->
  formula_sound_for (trm_seq t1 t2) (wpgen_seq F1 F2).
Proof using.
  introv S1 S2. intros Q. unfolds wpgen_seq. applys himpl_trans wp_seq.
  applys himpl_trans S1. applys wp_conseq. intros v. applys S2.
Qed.

Lemma wpgen_let_sound : forall F1 F2of x t1 t2,
  formula_sound_for t1 F1 ->
  (forall v, formula_sound_for (subst x v t2) (F2of v)) ->
  formula_sound_for (trm_let x t1 t2) (wpgen_let F1 F2of).
Proof using.
  introv S1 S2. intros Q. unfolds wpgen_let. applys himpl_trans wp_let.
  applys himpl_trans S1. applys wp_conseq. intros v. applys S2.
Qed.

Lemma wpgen_if_sound : forall F1 F2 v0 t1 t2,
  formula_sound_for t1 F1 ->
  formula_sound_for t2 F2 ->
  formula_sound_for (trm_if v0 t1 t2) (wpgen_if v0 F1 F2).
Proof using.
  introv S1 S2. intros Q. unfold wpgen_if. hpull. intros b ->.
  applys himpl_trans wp_if. case_if. { applys S1. } { applys S2. }
Qed.

Lemma wpgen_sound : forall E t,
  formula_sound_for (isubst E t) (wpgen E t).
Proof using.
  intros. gen E. induction t; intros; simpl; 
   applys mkstruct_sound.
  { applys wpgen_val_sound. } 
  { rename v into x. unfold wpgen_var. case_eq (lookup x E).
    { intros v EQ. applys wpgen_val_sound. }
    { intros N. applys wpgen_fail_sound. } }
  { applys wpgen_fun_sound. } 
  { applys wpgen_fix_sound. }
  { applys wp_sound. }
  { applys* wpgen_seq_sound. }
  { rename v into x. applys* wpgen_let_sound.
    { intros v. rewrite* <- isubst_rem. } }
  { case_eq (isubst E t1); simpl; intros; try applys wpgen_fail_sound.
    { applys* wpgen_if_sound. } }
Qed.

Theorem himpl_wpgen_wp : forall t Q,
  wpgen nil t Q ==> wp t Q.
Proof using.
  introv M. lets N: (wpgen_sound nil t). rewrite isubst_nil in N. applys* N.
Qed.

Theorem triple_of_wpgen : forall t H Q,
  H ==> wpgen nil t Q ->
  triple t H Q.
Proof using.
  introv M. rewrite wp_equiv. hchange M. applys himpl_wpgen_wp.
Qed.



(* ####################################################### *)
(** * Practical proofs *)

(* ******************************************************* *)
(** ** Tactics for [wpgen] *)

(** Lemmas *)

Lemma xstruct_lemma : forall F H Q,
  H ==> F Q ->
  H ==> mkstruct F Q.
Proof using. introv M. hchange M. applys mkstruct_erase. Qed.

Lemma xlet_lemma : forall H F1 F2of Q,
  H ==> F1 (fun v => F2of v Q) ->
  H ==> wpgen_let F1 F2of Q.
Proof using. introv M. hchange M. Qed.

Lemma xseq_lemma : forall H F1 F2 Q,
  H ==> F1 (fun v => F2 Q) ->
  H ==> wpgen_seq F1 F2 Q.
Proof using. introv M. hchange M. Qed.

Lemma xapp_lemma : forall t Q1 H1 H Q,
  triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* protect Q) ->
  H ==> wp t Q.
Proof using.
  introv M W. rewrite wp_equiv in M. hchange W. hchange M.
  applys wp_ramified_frame.
Qed.

Lemma xapps_lemma0 : forall t v H1 H Q,
  triple t H1 (fun r => \[r = v]) ->
  H ==> H1 \* (protect (Q v)) ->
  H ==> wp t Q.
Proof using. introv M W. applys xapp_lemma M. hchanges W. intros ? ->. auto. Qed.

Lemma xapps_lemma1 : forall t v H1 H2 H Q,
  triple t H1 (fun r => \[r = v] \* H2) ->
  H ==> H1 \* (H2 \-* protect (Q v)) ->
  H ==> wp t Q.
Proof using. introv M W. applys xapp_lemma M. hchanges W. intros ? ->. auto. Qed.

Lemma xcf_lemma_fun : forall v1 v2 x t H Q,
  v1 = val_fun x t ->
  H ==> wpgen ((x,v2)::nil) t Q ->
  triple (trm_app v1 v2) H Q.
Proof using.
  introv M1 M2. rewrite wp_equiv. hchange M2.
  lets N: wpgen_sound ((x,v2)::nil) t Q. hchange N.
  rewrite <- subst_eq_isubst_one. applys* wp_app_fun.
Qed.

Lemma xcf_lemma_fix : forall v1 v2 f x t H Q,
  v1 = val_fix f x t ->
  H ==> wpgen ((f,v1)::(x,v2)::nil) t Q ->
  triple (trm_app v1 v2) H Q.
Proof using.
  introv M1 M2. rewrite wp_equiv. hchange M2.
  lets N: wpgen_sound (((f,v1)::nil) ++ (x,v2)::nil) t Q.
  hchange N. rewrite isubst_app'.
  do 2 rewrite <- subst_eq_isubst_one.
  applys* wp_app_fix.
Qed.

Lemma xtop_lemma : forall H Q F,
  H ==> mkstruct F (Q \*+ \Top) ->
  H ==> mkstruct F Q.
Proof using.
  introv M. hchange M. 
  lets N: mkstruct_ramified (Q \*+ \Top) Q F. hchanges N.
Qed.

Tactic Notation "hsimpl'" :=
  hsimpl; unfold protect.

(** [xstruct] eliminates the leading [mkstruct]. *)

Tactic Notation "xstruct" :=
  applys xstruct_lemma.

(** [xseq] and [xlet] invoke the corresponding lemma, after
    calling [xstruct] if necessary. *)

Tactic Notation "xstruct_if_needed" :=
  try match goal with |- ?H ==> mkstruct ?F ?Q => xstruct end.

Tactic Notation "xlet" :=
  xstruct_if_needed; applys xlet_lemma.

Tactic Notation "xseq" :=
  xstruct_if_needed; applys xseq_lemma.

(** [xapp] invokes [xapp_lemma], after calling [xseq] or [xlet]
    if necessary. *)

Tactic Notation "xseq_xlet_if_needed" :=
  try match goal with |- ?H ==> mkstruct ?F ?Q => 
  match F with 
  | wpgen_seq ?F1 ?F2 => xseq
  | wpgen_let ?F1 ?F2of => xlet
  end end.

Tactic Notation "xapp_pre" :=
  xseq_xlet_if_needed; xstruct_if_needed.

Tactic Notation "xapp" :=
  xapp_pre; applys xapp_lemma.

Tactic Notation "xapp" constr(E) :=
  xapp_pre; applys xapp_lemma E; hsimpl'.

Tactic Notation "xapps" constr(E) :=
  xapp_pre; first 
  [ applys xapps_lemma0 E
  | applys xapps_lemma1 E ];
  hsimpl'.

(** [xtop] involves [xtop_lemma], exploiting the leading [mkstruct]. *)

Tactic Notation "xtop" :=
  applys xtop_lemma.

(** [xcf] applys [xcf_lemma], then computes [wpgen] to begin the proof. *)

Tactic Notation "xcf" :=
  intros; 
  first [ applys xcf_lemma_fun; [ reflexivity | idtac]
        | applys xcf_lemma_fix; [ reflexivity | idtac] ];
  simpl.


(* ******************************************************* *)
(** ** Notations for triples and [wpgen] *)

Notation "'TRIPLE' t 'PRE' H 'POST' Q" :=
  (triple t H Q)
  (at level 39, t at level 0, only parsing,
  format "'[v' 'TRIPLE'  t  '/' 'PRE'  H  '/' 'POST'  Q ']'") : wp_scope.

Notation "'PRE' H 'CODE' F 'POST' Q" := (H ==> (mkstruct F) Q)
  (at level 8, H, F, Q at level 0,
   format "'[v' 'PRE'  H  '/' 'CODE'  F '/' 'POST'  Q ']'") : wp_scope.

Notation "` F" := (mkstruct F) (at level 10, format "` F") : wp_scope.

Notation "'Fail'" :=
  ((wpgen_fail))
  (at level 69) : wp_scope.

Notation "'Val' v" :=
  ((wpgen_val v))
  (at level 69) : wp_scope.

Notation "'`Let' x ':=' F1 'in' F2" :=
  ((wpgen_let F1 (fun x => F2)))
  (at level 69, x ident, right associativity,
  format "'[v' '[' '`Let'  x  ':='  F1  'in' ']'  '/'  '[' F2 ']' ']'") : wp_scope.

Notation "'Seq' F1 ;;; F2" :=
  ((wpgen_seq F1 F2))
  (at level 68, right associativity,
   format "'[v' 'Seq'  '[' F1 ']'  ;;;  '/'  '[' F2 ']' ']'") : wp_scope.

Notation "'App' f v1 " :=
  ((wp (trm_app f v1)))
  (at level 68, f, v1 at level 0) : wp_scope.

Notation "'If'' v 'Then' F1 'Else' F2" :=
  ((wpgen_if v F1 F2))
  (at level 69) : wp_scope.

Open Scope wp_scope.


(* ******************************************************* *)
(** ** Notation for terms *)

Notation "'If_' t0 'Then' t1 'Else' t2" :=
  (trm_if t0 t1 t2)
  (at level 69, t0 at level 0) : trm_scope.

Notation "'If_' t0 'Then' t1 'End'" :=
  (trm_if t0 t1 val_unit)
  (at level 69, t0 at level 0) : trm_scope.

Notation "'Let' x ':=' t1 'in' t2" :=
  (trm_let x t1 t2)
  (at level 69, x at level 0, right associativity,
  format "'[v' '[' 'Let'  x  ':='  t1  'in' ']'  '/'  '[' t2 ']' ']'") : trm_scope.

Notation "t1 '';' t2" :=
  (trm_seq t1 t2)
  (at level 68, right associativity,
   format "'[v' '[' t1 ']'  '';'  '/'  '[' t2 ']' ']'") : trm_scope.

Notation "'VFix' f x1 ':=' t" :=
  (val_fix f x1 t)
  (at level 69, f, x1 at level 0, format "'VFix'  f  x1  ':='  t") : val_scope.

Notation "'Fix' f x1 ':=' t" :=
  (trm_fix f x1 t)
  (at level 69, f, x1 at level 0) : trm_scope.

Notation "'VFun' x1 ':=' t" :=
  (val_fun x1 t)
  (at level 69, x1 at level 0, format "'VFun'  x1  ':='  t") : val_scope.

Notation "'Fun' x1 ':=' t" :=
  (trm_fun x1 t)
  (at level 69, x1 at level 0, format "'Fun'  x1  ':='  t") : trm_scope.

Notation "'ref t" :=
  (val_ref t)
  (at level 67) : trm_scope.

Notation "'! t" :=
  (val_get t)
  (at level 67) : trm_scope.

Notation "t1 ':= t2" :=
  (val_set t1 t2)
  (at level 67) : trm_scope.

Notation "t1 '+ t2" :=
  (val_add t1 t2)
  (at level 68) : trm_scope.

Open Scope val_scope.
Open Scope trm_scope.

(** We let ['x] be a shortname for [("x":var)], as defined in [Var.v] *)

Import NotationForVariables.


(* ******************************************************* *)
(** ** Example proofs *)

(** Definition and verification of [incr]. *)

Definition incr : val :=
  VFun 'p :=
    (Let 'n := '! 'p in
    Let 'm := 'n '+ 1 in
    'p ':= 'm).

Lemma triple_incr : forall (p:loc) (n:int),
  TRIPLE (trm_app incr p)
    PRE (p ~~~> n)
    POST (fun v => \[v = val_unit] \* (p ~~~> (n+1))).
Proof using.
  xcf.
  xapps triple_get.
  xapps triple_add.
  xapps triple_set.
  hsimpl~.
Qed.

(** Definition and verification of [mysucc]. *)

Definition mysucc : val :=
  VFun 'n :=
    Let 'r := val_ref 'n in
    incr 'r ';
    '! 'r.

Lemma triple_mysucc : forall n,
  TRIPLE (trm_app mysucc n)
    PRE \[]
    POST (fun v => \[v = n+1]).
Proof using.
  xcf.
  xapp triple_ref ;=> ? l ->.
  xapps triple_incr.
  xtop.
  xapps triple_get.
  hsimpl~.
Qed.

