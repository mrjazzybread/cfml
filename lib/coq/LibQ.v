Set Implicit Arguments.
From TLC Require Import LibTactics LibRelation LibEpsilon LibLogic LibInt.
From Coq Require Import Field.
From AAC_tactics Require Import AAC.
From AAC_tactics Require Instances.
Import Instances.Z.
Open Scope Z_scope.
Open Scope Int_scope.


Ltac iff_core H1 H2 :=
  repeat intro;
  try match goal with |- _ = _ :> _ => apply prop_ext end;
  split; [ intros H1 | intros H2 ].

Tactic Notation "iff" simple_intropattern(H1) simple_intropattern(H2) :=
  iff_core H1 H2.
Tactic Notation "iff" simple_intropattern(H) :=
  iff H H.
Tactic Notation "iff" :=
  let H := fresh "H" in iff H.


Lemma exist_eq_exist_eq : forall A (P:A->Prop) (x y:A) (p:P x) (q:P y), 
  (exist P x p = exist P y q) = (x = y).
Proof using. iff M. { inverts* M. } { applys* exist_eq_exist. } Qed.


(* ********************************************************************** *)
(** * LibQuotient *)

Lemma repr_eq_repr_repr : forall A {IA:Inhab A} (R:binary A) (HR:equiv R) (x:A),
  epsilon (R x) = epsilon (R (epsilon (R x))).
Proof using.
  intros. asserts Re: (forall a, exists b, R a b). { intros a. exists a. applys* equiv_refl. }
  apply epsilon_eq. intros y. iff M1.
  { epsilon* x'. intros M2. applys* equiv_trans M1. applys* equiv_sym. }
  { epsilon* x'. intros M2. applys* equiv_trans M2. }
Qed.

Definition quotient A {IA:Inhab A} (R:binary A) : Type :=
  { repr : A | repr = epsilon (R repr) }.

#[global]
Instance Inhab_quotient : forall A {IA:Inhab A} (R:binary A) (HR:equiv R),
  Inhab (quotient R).
Proof using.
  intros. eapply Inhab_of_val. applys exist (epsilon (R (arbitrary (A:=A)))). applys* repr_eq_repr_repr.
Qed.

Definition inject A {IA:Inhab A} (R:binary A) (HR:equiv R) (x:A) : quotient R :=
  exist _ (epsilon (R x)) (repr_eq_repr_repr HR x).

Lemma inject_eq_eq_rel : forall A {IA:Inhab A} (R:binary A) (HR:equiv R) (x y:A),
  (inject HR x = inject HR y) = (R x y).
Proof using.
  intros. asserts Re: (forall a, exists b, R a b). { intros a. exists a. applys* equiv_refl. }
  extens. iff M.
  { inverts M as M'. epsilon* x'. intros Mx. epsilon* y'. intros My. rewrite M' in Mx.
    applys* equiv_trans Mx. applys* equiv_sym My. }
  { applys exist_eq_exist. applys epsilon_eq. intros z. iff M2.
    { applys* equiv_trans M2. applys* equiv_sym. }
    { applys* equiv_trans M. } }
Qed.


(* ********************************************************************** *)
(** * Q and operations *)

(* ---------------------------------------------------------------------- *)
(** ** Notation for type and operation *)

Declare Scope Q_scope.
Delimit Scope Q_scope with Q.
Local Open Scope Q_scope.


(* ---------------------------------------------------------------------- *)
(** ** Type definition *)

(** Supports are pairs of a Z and a nonzero-Z *)

Definition support : Type :=
  { p : Z*Z | let '(n,m) := p in m <> 0 }.

#[local]
Instance Inhab_support : Inhab support.
Proof using.
  asserts E: (1 <> 0). { math. }
  intros. eapply (Inhab_of_val (exist _ (1,1) E)).
Qed.

(** Equivalence of pairs *)

Definition rel (p1 p2 : support) : Prop :=
  let '(n1,m1) := sig_val p1 in
  let '(n2,m2) := sig_val p2 in
  n1 * m2 = n2 * m1.

Require Import  Coq.ZArith.BinInt.

Lemma equiv_rel : equiv rel.
Proof using.
  constructors.
  { intros ((n,m)&H1). unfold rel; simpls. ring. }
  { intros ((n1,m1)&H1) ((n2,m2)&H2) E. unfolds rel; simpls. eauto. }
  { intros ((n1,m1)&H1) ((n2,m2)&H2) ((n3,m3)&H3) E1 E2. unfolds rel; simpls.
    applys* Z.mul_reg_l m1. rewrite Z.mul_shuffle3. rewrite Z.mul_assoc.
    rewrite E1. rewrite <- Z.mul_assoc. rewrite (Z.mul_comm m2).
    rewrite Z.mul_assoc. rewrite E2. rewrite Z.mul_shuffle3. rewrite* Z.mul_assoc. }
Qed.

(** Definition of Q as the quotient *)

Definition Q : Type :=
  quotient rel.

Implicit Types q : Q.

(** Inhabited type *)

#[global]
Instance Inhab_Q : Inhab Q.
Proof using. intros. applys Inhab_quotient equiv_rel. Qed.

(** Constructor from numerator/denominator -- for internal use only *)

Program Definition make (n m : Z) : Q :=
  If m = 0 then arbitrary else inject equiv_rel (n,m).

Local Notation "x '//' y" := (make x y) (at level 39) : Q_scope.

(** Deconstructor for numerator/denominator -- for internal use only *)

Definition Q_to_ZZ (q:Q) : Z*Z :=
  sig_val (sig_val q).


(* ---------------------------------------------------------------------- *)
(** ** Internal operations -- don't use outside this module *)


(** DEPRECATED Proving equalities -- for internal use only 

Lemma Q_eq' : forall q1 q2,
  let '(n1,m1) := Q_to_ZZ q1 in
  let '(n2,m2) := Q_to_ZZ q2 in
  (n1 = n2 /\ m1 = m2) ->
  q1 = q2.
Proof using.
  intros (((n1,m1)&Hm1)&E1) (((n2,m2)&Hm2)&E2) (EQ1&EQ2). simpls.
  applys exist_eq_exist. applys exist_eq_exist. autos*.
Qed.

*)

Section Internal.

Hint Resolve equiv_rel.
Hint Extern 1 (exists _, rel _ _) => eexists; eapply equiv_refl.

Lemma make_eq_make_eq : forall n1 m1 n2 m2,
  m1 <> 0 ->
  m2 <> 0 ->
  (make n1 m1 = make n2 m2) = (n1 * m2 = n2 * m1)%Z.
Proof using.
  introv N1 N2. unfold make.
  destruct (classicT (m1 = 0)); try math.
  destruct (classicT (m2 = 0)); try math.
  unfold Q. rewrite inject_eq_eq_rel. unfold rel; simple*.
Qed.

End Internal.

Ltac make_eq_elim_core tt :=
  match goal with 
  | H: context [ make _ _ = make _ _ ] |- _ => rewrite make_eq_make_eq in H; [ try make_eq_elim_core tt | | ]
  | |- context [ make _ _ = make _ _ ] => rewrite make_eq_make_eq; [ try make_eq_elim_core tt | | ]
  end.

Tactic Notation "make_eq_elim" := 
  make_eq_elim_core tt.

Tactic Notation "make_eq_elim" "*" := 
  make_eq_elim; first [ math | auto_star ].



(* DEPRECATED

Lemma make_eq : forall n1 m1 n2 m2,
  (n1 * m2 = m1 * n2)%Z ->
  m1 <> 0 ->
  m2 <> 0 ->
  make n1 m1 = make n2 m2.

Lema make_eq_make_inv : forall n1 m1 n2 m2,
  make n1 m1 = make n2 m2 ->
  m1 <> 0 ->
  m2 <> 0 ->
  (n1 * m2 = m1 * n2)%Z.

*)

(** Decomposition of a rational [q] into the form [n // m]. *)

Lemma Q_inv_ZZ : forall q,
  exists n m, m <> 0 /\ q = n // m /\ Q_to_ZZ q = (n,m) .
Proof using.
  intros (((n1,m1)&Hm1)&E1). exists n1 m1. splits.
  { auto. }
  { unfold make. destruct (classicT (m1 = 0)). { false. }
    applys exist_eq_exist. auto. }
  { unfold Q_to_ZZ. simple*. }
Qed.

Lemma Q_inv : forall q,
  exists n m, m > 0 /\ q = n // m.
Proof using.
  intros. forwards* (n&m&?&->&_): Q_inv_ZZ q. tests: (m > 0).
  { eauto. }
  { exists (-n) (-m). splits. { math. } { make_eq_elim; try math. } } 
Qed.

Ltac Q_inv :=
  match goal with q: Q |- _ => 
    let n' := fresh "n" q in
    let m' := fresh "m" q in
    let Hm' := fresh "Hm" q in
    lets (n'&m'&Hm'&->): Q_inv q
  end.

Ltac Q_invs :=
  repeat Q_inv.

Lemma Q_to_ZZ_make : forall n m,
  m <> 0 ->
  exists n' m', m' <> 0 
             /\ Q_to_ZZ (n // m) = (n',m')
             /\ (n // m) = (n' // m').
Proof using. introv Hm. lets (n'&m'&Hm'&->&F): Q_inv_ZZ (n // m). exists* n' m'. Qed.

Ltac Q_to_ZZ_make_on n m :=
  let n' := fresh n "'" in
  let m' := fresh m "'" in
  let E := fresh "E" n' in
  let EQ := fresh "EQ" n' in
  let Hm' := fresh "H" m' in
  forwards (n'&m'&Hm'&EQ&E): Q_to_ZZ_make n m;
  [ try assumption
  | rewrite EQ in *; clear EQ ].

Ltac Q_to_ZZ_make :=
  match goal with 
  | |- context [Q_to_ZZ (?n // ?m)] => Q_to_ZZ_make_on n m
  | H: context [Q_to_ZZ (?n // ?m)] |- _ => Q_to_ZZ_make_on n m
  end.

Ltac Q_to_ZZ_makes :=
  repeat Q_to_ZZ_make.

(* DEPRECATED

Lemma Q_inv_ZZ_Z : forall (a:Z),
  exists n m, m <> 0 /\ (Q_to_ZZ (Z_to_Q a)) = (n,m) /\ (a * m = n)%Z.
Proof using.
  intros. lets (n&m&Nm&Em&Fm): Q_inv_ZZ (Z_to_Q a).
  exists n m. splits*. unfolds Z_to_Q.
  forwards E: make_eq_make_inv Fm; try math; auto.
Qed.

Lemma Q_inv_ZZ_make : forall a b,
  b <> 0 ->
  exists n m, m <> 0 /\ Q_to_ZZ (make a b) = (n,m) /\ a * m = b * n.
Proof using.
  introv Hb. lets (n&m&Nm&Em&Fm): Q_inv_ZZ (make a b).
  forwards*: make_eq_make_inv Fm.
Qed.
*)


(* ---------------------------------------------------------------------- *)
(** ** Relationship to Z *)

(** Conversion from Z, registered as coercion *)

Coercion Z_to_Q (n:Z) : Q :=
  n // 1.

Lemma Q_inv_Z : forall (a:Z), (* not used *)
  Z_to_Q a = a // 1.
Proof using. auto. Qed.

(** Zero equality *)

Lemma make_zero_eq : forall n m,
  m <> 0 ->
  ((n // m) = 0) = (n = 0).
Proof. introv Hm. unfold Z_to_Q. rewrite make_eq_make_eq; try math. Qed.

Lemma make_nonzero_eq : forall n m,
  m <> 0 ->
  ((n // m) <> 0) = (n <> 0).
Proof.
  introv Hm. lets R: make_zero_eq n Hm. apply injective_not. rew_logic. rewrite* R.
Qed.


(* ---------------------------------------------------------------------- *)
(** ** Operations *)

(** Binary and unary operations *)

Definition add (q1 q2 : Q) : Q :=
  let '(n1,m1) := Q_to_ZZ q1 in
  let '(n2,m2) := Q_to_ZZ q2 in
  make (n1*m2 + n2*m1) (m1*m2).

Infix "+" := add : Q_scope.

Definition mul (q1 q2 : Q) : Q :=
  let '(n1,m1) := Q_to_ZZ q1 in
  let '(n2,m2) := Q_to_ZZ q2 in
  make (n1*n2) (m1*m2).

Infix "*" := mul : Q_scope.

Definition opp (q1 : Q) : Q :=
  mul (-1) q1.

Notation "- x" := (opp x) : Q_scope.

Definition sub (q1 q2 : Q) : Q :=
  add q1 (opp q2).

Infix "-" := sub : Q_scope.

(* only for internal use *)
Definition inv (q1 : Q) : Q :=
  let '(n1,m1) := Q_to_ZZ q1 in
  make m1 n1.

Definition div (q1 q2 : Q) : Q :=
  mul q1 (inv q2).

Infix "/" := div : Q_scope.

(* ---------------------------------------------------------------------- *)
(** ** Charcterization of operations *)

Ltac ring_hyps_setup :=
  try ring_simplify;
  repeat (
    match goal with H: _ = _ :> Z |- _ => 
      first [ aac_rewrite H; clear H
            | aac_rewrite <- H; clear H
            | clear H ]
    end).

Ltac ring_hyps :=
  ring_hyps_setup; try solve [ ring ].


Lemma add_make : forall n1 m1 n2 m2,
  m1 <> 0 -> 
  m2 <> 0 ->
  add (n1 // m1) (n2 // m2) = (n1*m2 + n2*m1) // (m1*m2).
Proof using.
  introv N1 N2. unfold add. Q_to_ZZ_makes. make_eq_elim*. ring_hyps. Qed.

Lemma mul_make : forall n1 m1 n2 m2,
  m1 <> 0 -> 
  m2 <> 0 ->
  mul (n1 // m1) (n2 // m2) = (n1*n2) // (m1*m2).
Proof using.
  introv N1 N2. unfold mul. Q_to_ZZ_makes. make_eq_elim*. ring_hyps.
  (* details: ring_simplify. aac_rewrite <- En1'. aac_rewrite <- En2'. ring. *)
Qed.

Lemma opp_make : forall n1 m1,
  m1 <> 0 -> 
  opp (n1 // m1) = (-n1) // m1.
Proof using. introv N1. unfold opp, Z_to_Q. rewrite mul_make; try math. make_eq_elim*. Qed.

Lemma sub_make : forall n1 m1 n2 m2,
  m1 <> 0 -> 
  m2 <> 0 ->
  sub (n1 // m1) (n2 // m2) = (n1*m2 - n2*m1) // (m1*m2).
Proof using. introv N1 N2. unfold sub. rewrite opp_make, add_make; try math. make_eq_elim*. Qed.

Lemma inv_make : forall n1 m1,
  n1 <> 0 ->
  m1 <> 0 -> 
  inv (n1 // m1) = (m1 // n1).
Proof using. introv N1 N2. unfold inv. Q_to_ZZ_makes. make_eq_elim*. Qed.

Lemma div_make : forall n1 m1 n2 m2,
  m1 <> 0 -> 
  m2 <> 0 ->
  n2 <> 0 ->
  div (n1 // m1) (n2 // m2) = (n1*m2) // (m1*n2).
Proof using. introv N1 N2 N3. unfold div. rewrite inv_make, mul_make; try math. auto. Qed.

(** Tactic [rew_q_op] *)

#[global] Hint Rewrite make_zero_eq make_nonzero_eq
 add_make mul_make opp_make sub_make inv_make div_make : rew_q_op.

Tactic Notation "rew_q_op" :=
  autorewrite with rew_q_op.

Tactic Notation "rew_q_op" "in" "*" :=
  autorewrite with rew_q_op in *.
  (* DOES NOT WORK BECAUSE SIDE CONDITIONS 
    autorewrite_in_star_patch
    ltac:(fun tt => autorewrite with rew_q_op). *)

Ltac rew_q_ops_core cont := 
  unfold Z_to_Q; rew_q_op; try math.

Ltac rew_q_ops_in_star_core cont := 
  unfolds Z_to_Q; rew_q_op in *; try math.

Tactic Notation "rew_q_ops" :=
  rew_q_ops_core tt.

Tactic Notation "rew_q_ops" "in" "*" :=
  rew_q_ops_in_star_core tt.


(* ********************************************************************** *)
(** * Public properties *)

Ltac q_ops_prove :=
  intros; Q_invs; rew_q_ops in *; try make_eq_elim; try math.

(* ---------------------------------------------------------------------- *)
(** ** Zero inversions *)

Lemma mul_zero_inv : forall q1 q2,
  q1 * q2 = 0 ->
  q1 = 0 \/ q2 = 0.
Proof using.
  introv R. Q_invs. rew_q_ops in *.
  ring_simplify in R. lets [|]: Zmult_integral R; subst.
  { left. ring. } { right. ring. }
Qed.

Lemma mul_zero_inv_nonzero_l : forall q1 q2,
  q1 * q2 = 0 ->
  q1 <> 0 ->
  q2 = 0.
Proof using. introv E N. lets: mul_zero_inv E. autos*. Qed.


(* ---------------------------------------------------------------------- *)
(** ** [add] *)

Lemma add_zero_r : forall q,
  q + 0 = q.
Proof using. q_ops_prove. Qed.

Lemma add_zero_l : forall q,
  0 + q = q.
Proof using. q_ops_prove. Qed.

Lemma comm_add : (* [comm add] *) 
  forall q1 q2,
  q1 + q2 = q2 + q1.
Proof using. q_ops_prove. Qed.

Lemma assoc_add : forall q1 q2 q3,
  q1 + (q2 + q3) = (q1 + q2) + q3.
Proof using. q_ops_prove. Qed.

#[global] Hint Rewrite add_zero_r add_zero_l assoc_add : rew_Q.


(* ---------------------------------------------------------------------- *)
(** ** [opp] and [sub] and [add] *)

Lemma sub_zero_r : forall q,
  q - 0 = q.
Proof using. q_ops_prove. Qed.

Lemma sub_zero_l : forall q,
  0 - q = (- q).
Proof using. q_ops_prove. Qed.

Lemma sub_self : forall q,
  q - q = 0.
Proof using. q_ops_prove. Qed.

Lemma opp_self : forall q,
  - (- q) = q.
Proof using. q_ops_prove. Qed.

Lemma opp_add : forall q1 q2,
  - (q1 + q2) = -q1 - q2.
Proof using. q_ops_prove. Qed.

Lemma opp_sub : forall q1 q2,
  - (q1 - q2) = q2 - q1.
Proof using. q_ops_prove. Qed.


#[global] Hint Rewrite sub_zero_r sub_zero_l sub_self opp_self opp_add opp_sub : rew_Q.

(* ---------------------------------------------------------------------- *)
(** ** [add] and [sub] *)

Lemma sub_add_l : forall q1 q2 q3,
  (q1 + q2) - q3 = q1 + (q2 - q3).
Proof using. q_ops_prove. Qed.

Lemma sub_add_r : forall q1 q2 q3,
  q1 - (q2 + q3) = q1 - q2 - q3.
Proof using. q_ops_prove. Qed.

Lemma add_opp_r : forall q1 q2,
  q1 + (- q2) = q1 - q2.
Proof using. q_ops_prove. Qed.

Lemma add_opp_self_r : forall q,
  q + (- q) = 0.
Proof using. q_ops_prove. Qed.

#[global] Hint Rewrite sub_add_l sub_add_r add_opp_r add_opp_self_r : rew_Q.

Lemma add_sub_l_self : forall q1 q2,
  (q1 - q2) + q2 = q1.
Proof using. q_ops_prove. Qed.

Lemma add_sub_r_self : forall q1 q2,
  q1 + (q2 - q1) = q2.
Proof using. q_ops_prove. Qed.

Lemma sub_add_l_self_r : forall q1 q2,
  (q1 + q2) - q2 = q1.
Proof using. q_ops_prove. Qed.

Lemma sub_add_l_self_l : forall q1 q2,
  (q2 + q1) - q2 = q1.
Proof using. q_ops_prove. Qed.


(* ---------------------------------------------------------------------- *)
(** ** Cancelling with [add] or [sub] *)

Lemma eq_add_same_r_eq : forall q1 q2 q3,
  (q1 + q3 = q2 + q3) = (q1 = q2).
Proof using.
  iff M.
  { intros. asserts E: (q1 + q3 - q3 = q2 + q3 - q3). { rewrite* M. } clear M.
    do 2 rewrite sub_add_l in E. rewrite sub_self in E.
    do 2 rewrite add_zero_r in E. auto. }
  { subst*. }
Qed.

Lemma eq_sub_same_r_eq : forall q1 q2 q3,
  (q1 - q3 = q2 - q3) = (q1 = q2).
Proof using. intros. do 2 rewrite <- add_opp_r. applys eq_add_same_r_eq. Qed.

Lemma sub_eq_zero_eq_same : forall q1 q2,
  (q1 - q2 = 0) = (q1 = q2).
Proof using.
  intros. rewrite <- (eq_add_same_r_eq (q1 - q2) 0 q2).
  rewrite add_zero_l. rewrite add_sub_l_self. auto.
Qed.

(* ---------------------------------------------------------------------- *)
(** ** [mul] *)

Lemma mul_zero_l : forall q,
  0 * q = 0.
Proof using. q_ops_prove. Qed.

Lemma mul_zero_r : forall q,
  q * 0 = 0.
Proof using. q_ops_prove. Qed.

Lemma mul_one_l : forall q,
  1 * q = q.
Proof using. q_ops_prove. Qed.

Lemma mul_one_r : forall q,
  q * 1 = q.
Proof using. q_ops_prove. Qed.

Lemma comm_mul :
  forall q1 q2,
  q1 * q2 = q2 * q1.
Proof using. q_ops_prove. Qed.

Lemma assoc_mul : forall q1 q2 q3,
  q1 * (q2 * q3) = (q1 * q2) * q3.
Proof using. q_ops_prove. Qed.

#[global] Hint Rewrite mul_zero_l mul_zero_r mul_one_l mul_one_r assoc_mul : rew_Q.


(* ---------------------------------------------------------------------- *)
(** ** [mul] and [add] or [sub] or [opp] *)

Lemma mul_add_r : forall q1 q2 q3,
  (q1 + q2) * q3 = (q1 * q3) + (q2 * q3).
Proof using. q_ops_prove. Qed.

Lemma mul_add_l : forall q1 q2 q3,
  q1 * (q2 + q3) = (q1 * q2) + (q1 * q3).
Proof using. q_ops_prove. Qed.

Lemma mul_sub_r : forall q1 q2 q3,
  (q1 - q2) * q3 = (q1 * q3) - (q2 * q3).
Proof using. q_ops_prove. Qed.

Lemma mul_sub_l : forall q1 q2 q3,
  q1 * (q2 - q3) = (q1 * q2) - (q1 * q3).
Proof using. q_ops_prove. Qed.

Lemma opp_mul_l : forall q1 q2,
  - (q1 * q2) = (-q1) * q2.
Proof using. q_ops_prove. Qed.

Lemma opp_mul_r : forall q1 q2,
  - (q1 * q2) = q1 * (-q2).
Proof using. q_ops_prove. Qed.


(* ---------------------------------------------------------------------- *)
(** ** [div] *)

Lemma div_same : forall q,
  q <> 0 ->
  q / q = 1.
Proof using. q_ops_prove. Qed.

#[global] Hint Rewrite div_same : rew_Qx.


(* ---------------------------------------------------------------------- *)
(** ** [div] and [mul] *)

Lemma div_div_l : forall q1 q2 q3,
  q2 <> 0 ->
  q3 <> 0 ->
  (q1 / q2) / q3 = q1 / (q2 * q3).
Proof using. q_ops_prove. Qed.

Lemma div_div_r : forall q1 q2 q3,
  q2 <> 0 ->
  q3 <> 0 ->
  q1 / (q2 / q3) = (q1 * q3) / q2.
Proof using. q_ops_prove. Qed.

Lemma mul_div_l : forall q1 q2 q3,
  q2 <> 0 ->
  (q1 / q2) * q3 = (q1 * q3) / q2.
Proof using. q_ops_prove. Qed.

Lemma mul_div_r : forall q1 q2 q3,
  q2 <> 0 ->
  q3 <> 0 ->
  q1 * (q2 / q3) = (q1 * q2) / q3.
Proof using. q_ops_prove. Qed.

Lemma mul_inv_r : forall q,
  q <> 0 ->
  q * (1 / q) = 1.
Proof using. q_ops_prove. Qed.

Lemma div_mul_cancel_l : forall q1 q2,
  q1 <> 0 ->
  (q1 * q2) / q1 = q2.
Proof using. q_ops_prove. Qed.

Lemma div_mul_cancel_r : forall q1 q2,
  q2 <> 0 ->
  (q1 * q2) / q2 = q1.
Proof using. q_ops_prove. Qed.

Lemma mul_div_cancel_l : forall q1 q2,
  q1 <> 0 ->
  q1 * (q2 / q1) = q2.
Proof using. q_ops_prove. Qed.

Lemma mul_div_cancel_r : forall q1 q2,
  q1 <> 0 ->
  (q2 / q1) * q1 = q2.
Proof using. q_ops_prove. Qed.

#[global] Hint Rewrite div_div_l div_div_r mul_div_l mul_div_r mul_inv_r 
  div_mul_cancel_l div_mul_cancel_r mul_div_cancel_l mul_div_cancel_r : rew_Qx.


(* ---------------------------------------------------------------------- *)
(** ** Distrib operators over [Z_to_Q] *)

Lemma add_Z_to_Q : forall n m,
  ((Z_to_Q n) + (Z_to_Q m))%Q = (Z_to_Q (n + m)%Z).
Proof. q_ops_prove. Qed.

Lemma sub_Z_to_Q : forall n m,
  ((Z_to_Q n) - (Z_to_Q m))%Q = (Z_to_Q (n - m)%Z).
Proof. q_ops_prove. Qed.

Lemma opp_Z_to_Q : forall n,
  (- (Z_to_Q n))%Q = (Z_to_Q (- n)%Z).
Proof. q_ops_prove. Qed.

Lemma mul_Z_to_Q : forall n m,
  ((Z_to_Q n) + (Z_to_Q m))%Q = (Z_to_Q (n + m)%Z).
Proof. q_ops_prove. Qed.

#[global] Hint Rewrite add_Z_to_Q sub_Z_to_Q opp_Z_to_Q mul_Z_to_Q : rew_Q.



(* ---------------------------------------------------------------------- *)
(** ** Simplification tactic *)

(** [rew_Q] performs some basic simplification on
    expressions involving rationals *)

Tactic Notation "rew_Q" :=
  autorewrite with rew_Q.
Tactic Notation "rew_Q" "~" :=
  rew_Q; auto_tilde.
Tactic Notation "rew_Q" "*" :=
  rew_Q; auto_star.
Tactic Notation "rew_Q" "in" "*" :=
  autorewrite_in_star_patch ltac:(fun tt => autorewrite with rew_Q).
  (* autorewrite with rew_Q in *. *)
Tactic Notation "rew_Q" "~" "in" "*" :=
  rew_Q in *; auto_tilde.
Tactic Notation "rew_Q" "*" "in" "*" :=
  rew_Q in *; auto_star.
Tactic Notation "rew_Q" "in" hyp(H) :=
  autorewrite with rew_Q in H.
Tactic Notation "rew_Q" "~" "in" hyp(H) :=
  rew_Q in H; auto_tilde.
Tactic Notation "rew_Q" "*" "in" hyp(H) :=
  rew_Q in H; auto_star.

(** [rew_Qx] performs some basic simplification on
    expressions involving divisions
    TODO: include also all other rewrite rules? *)

Tactic Notation "rew_Qx" :=
  autorewrite with rew_Qx.
Tactic Notation "rew_Qx" "~" :=
  rew_Qx; auto_tilde.
Tactic Notation "rew_Qx" "*" :=
  rew_Qx; auto_star.
Tactic Notation "rew_Qx" "in" "*" :=
  (*  autorewrite_in_star_patch ltac:(fun tt => autorewrite with rew_Qx). *)
  autorewrite with rew_Qx in *. 
Tactic Notation "rew_Qx" "~" "in" "*" :=
  rew_Qx in *; auto_tilde.
Tactic Notation "rew_Qx" "*" "in" "*" :=
  rew_Qx in *; auto_star.
Tactic Notation "rew_Qx" "in" hyp(H) :=
  autorewrite with rew_Qx in H.
Tactic Notation "rew_Qx" "~" "in" hyp(H) :=
  rew_Qx in H; auto_tilde.
Tactic Notation "rew_Qx" "*" "in" hyp(H) :=
  rew_Qx in H; auto_star.




(* ********************************************************************** *)
(** * Comparisons *)

(* TODO; move *)

#[global]
Instance int_le_total_order : Le_total_order (A:=int).
Proof using.
  constructor. constructor.
  { constructor; unfolds; math. }
  { intros x y. tests: (x <= y). { left*. } { right. math. } }
Qed.


(* ---------------------------------------------------------------------- *)
(** ** [Q_nonneg] *)

Definition Q_nonneg (q : Q) : Prop :=
  let '(n,m) := Q_to_ZZ q in
  (n * m)%Z >= 0.

Lemma Q_nonneg_make_pos : forall n m,
  m > 0 ->
  (Q_nonneg (make n m)) = (n >= 0).
Proof using.
  intros. unfold Q_nonneg. Q_to_ZZ_makes; try math. make_eq_elim; try math. iff M.
  { forwards [(?&?)|(?&?)]: Z.le_0_mul n' m'; try math;
     tests: (n >= 0); tests: (m >= 0); try math. }
  { tests: (n' = 0); tests: (m' = 0); try math. } 
Qed.

Lemma Q_nonneg_total : forall d,
  Q_nonneg d \/ Q_nonneg (- d).
Proof using.
  intros. Q_inv. rewrite Q_nonneg_make_pos; try math. tests: (nd >= 0).
  { left. math. }
  { right. rew_q_op; try math. rewrite Q_nonneg_make_pos; try math. }
Qed.

Lemma Q_nonneg_antisym : forall d,
  Q_nonneg d ->
  Q_nonneg (- d) ->
  d = 0.
Proof using.
  introv M1 M2. Q_inv. rew_q_op in *; try math. 
  rewrite Q_nonneg_make_pos in *; try math.
Qed.


(* ---------------------------------------------------------------------- *)
(** ** [Q_le] *)

Definition Q_le (q1 q2 : Q) : Prop :=
  Q_nonneg (q2 - q1).

Open Scope comp_scope.

#[global] Instance le_Q_inst : Le Q := Build_Le Q_le.

Lemma le_eq : forall q1 q2,
  (q1 <= q2) = (Q_le q1 q2).
Proof using. auto. Qed.

Lemma make_le_make_eq_pos : forall n1 m1 n2 m2,
  m1 > 0 ->
  m2 > 0 ->
  (make n1 m1 <= make n2 m2) = (n1 * m2 <= n2 * m1)%Z.
Proof using.
  introv N1 N2. rewrite le_eq. unfold Q_le. rew_q_op; try math.
  rewrite Q_nonneg_make_pos; try math.
Qed.

Ltac Q_to_ZZ_make_on n m ::=
  first [
    let n' := fresh n "'" in
    let m' := fresh m "'" in
    let E := fresh "E" n' in
    let EQ := fresh "EQ" n' in
    let Hm' := fresh "H" m' in
    forwards (n'&m'&Hm'&EQ&E): Q_to_ZZ_make n m;
    [ try assumption
    | rewrite EQ in *; clear EQ ]
  | let EQ := fresh "EQ" in 
    forwards (?&?&?&EQ&?): Q_to_ZZ_make n m;
    [ try assumption
    | rewrite EQ in *; clear EQ ] ].


(* ---------------------------------------------------------------------- *)
(** ** [Total_order] *)

#[global] Instance Q_le_total_order : Le_total_order (A:=Q).
Proof using.
  constructors. constructors.
  { constructors.
    { intros q. rewrite le_eq. unfolds. rew_Q. unfolds.
      unfold Z_to_Q. Q_to_ZZ_make; try math. make_eq_elim; try math.  
      (* why not q_ops_prove. ? *) }
    { skip. }
    { intros q1 q2 M1 M2. rewrite le_eq in *. unfolds Q_le.
      rewrite <- sub_eq_zero_eq_same.
      set (d := q1 - q2) in *. replace (q2 - q1) with (-d) in M1.
      { clearbody d. applys* Q_nonneg_antisym. }
      { subst d. rew_Q*. } } }
  { intros q1 q2. rewrite le_eq. rewrite (le_eq q2 q1). unfolds Q_le.
     lets [|]: Q_nonneg_total (q2 - q1); rew_Q* in *. }
Qed.


(* ---------------------------------------------------------------------- *)
(** ** Inequalities *)

Lemma le_mul_mul : forall q1 q2 q3 q4,
  q1 <= q2 ->
  q3 <= q4 ->
  q1 * q3 >= q2 * q4.
Proof using. skip. Qed.

Lemma le_mul_same_r : forall q1 q2 q3,
  q1 <= q2 ->
  q3 >= 0 ->
  q1 * q3 <= q2 * q3.
Proof using. skip. Qed.



(* ********************************************************************** *)
(** * Conversions of operations from [int] to [Q] and back *)

(* ---------------------------------------------------------------------- *)
(** ** Lifting of comparisons *)

Lemma eq_int_of_eq_Q : forall (n1 n2:Z),
  (n1:Q) = (n2:Q) ->
  n1 = n2.
Proof using. q_ops_prove. Qed.

Lemma neq_int_of_neq_Q : forall (n1 n2:Z),
  (n1:Q) <> (n2:Q) ->
  n1 <> n2.
Proof using. q_ops_prove. Qed.

Lemma eq_Q_of_eq_Z : forall (n1 n2:Z),
  n1 = n2 ->
  (n1:Q) = (n2:Q).
Proof using. q_ops_prove. Qed.

Lemma neq_Q_of_neq_Z : forall (n1 n2:Z),
  n1 <> n2 ->
  (n1:Q) <> (n2:Q).
Proof using. q_ops_prove. Qed.


(* ---------------------------------------------------------------------- *)
(** ** Lifting of inequalities from [nat] to [int] *)

Lemma le_int_eq_le_Q : forall (n1 n2:Z),
  ((n1:Q) <= (n2:Q)) = (n1 <= n2)%Z.
Proof using. intros. unfolds Z_to_Q. rewrite make_le_make_eq_pos; try math. Qed.

Lemma le_int_of_le_Q : forall (n1 n2:Z),
  (n1:Q) <= (n2:Q) ->
  (n1 <= n2).
Proof using. intros. rewrite* <- le_int_eq_le_Q. Qed.

Lemma le_Q_of_le_int : forall (n1 n2:int),
  (n1 <= n2) ->
  (n1:Q) <= (n2:Q).
Proof using. intros. rewrite* le_int_eq_le_Q. Qed.

Lemma ge_int_of_ge_Q : forall (n1 n2:int),
  (n1:Q) >= (n2:Q) ->
  (n1 >= n2).
Proof using. intros. rewrite ge_as_sle in *. applys* le_int_of_le_Q. Qed.

Lemma ge_Q_of_ge_int : forall (n1 n2:int),
  (n1 >= n2) ->
  (n1:Q) >= (n2:Q).
Proof using. intros. rewrite ge_as_sle in *. applys* le_Q_of_le_int. Qed.

Lemma lt_int_of_lt_Q : forall (n1 n2:int),
  (n1:Q) < (n2:Q) ->
  (n1 < n2).
Proof using.
  intros. rewrite <- @nge_as_lt in *; try typeclass. (*  fix implicits *)
  (* rewrite <- nge_as_lt in H. *) lets*: ge_Q_of_ge_int n1 n2.
Qed.

Lemma lt_Q_of_lt_int : forall (n1 n2:int),
  (n1 < n2) ->
  (n1:Q) < (n2:Q).
Proof using.
  intros. rewrite <- @nge_as_lt in *; try typeclass. (*  fix implicits *)
  (* rewrite <- nge_as_lt in H. *) lets*: ge_int_of_ge_Q n1 n2.
Qed.

Lemma gt_int_of_gt_Q : forall (n1 n2:int),
  (n1:Q) > (n2:Q) ->
  (n1 > n2).
Proof using. intros. rewrite gt_as_slt in *. applys* lt_int_of_lt_Q. Qed.

Lemma gt_Q_of_gt_int : forall (n1 n2:int),
  (n1 > n2) ->
  (n1:Q) > (n2:Q).
Proof using. intros. rewrite gt_as_slt in *. applys* lt_Q_of_lt_int. Qed.



(* ********************************************************************** *)
(** * Ring and Field *)


Definition ring_theory_Q : ring_theory (Z_to_Q 0) (Z_to_Q 1) add mul sub opp (eq(A:=Q)).
Proof.
  constructor.
  { exact add_zero_l. }
  { applys comm_add. }
  { applys assoc_add. }
  { exact mul_one_l. }
  { applys comm_mul. }
  { applys assoc_mul. }
  { applys mul_add_r. }
  { reflexivity. }
  { applys add_opp_self_r. }
Qed.

Add Ring ring_Q : ring_theory_Q.

Definition field_theory_Q :
  field_theory (Z_to_Q 0) (Z_to_Q 1)  add mul sub opp div inv (eq(A:=Q)).
Proof.
  constructor.
  { exact ring_theory_Q. }
  { applys neq_Q_of_neq_Z. math. } 
  { reflexivity. }
  { q_ops_prove. }
Qed.

Add Field field_Q : field_theory_Q.

(* see also https://coq.inria.fr/library/Coq.QArith.Qfield.html# for bonuses *)