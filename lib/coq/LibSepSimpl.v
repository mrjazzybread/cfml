(**

This file provides the essential tactics for manipulation of
Separation Logic formulae.

The functor in this file assumes:
- definitions for Separation Logic operators
- a minimal set of properties of theses operators.

It provides the following tactics:
- [xsimpl] simplifies heap entailments
- [xpull] is a restricted version of [xsimpl] that only act over the LHS
- [xchange] performs transitivity steps in entailments, modulo frame
- [rew_heap] normalizes heap predicate expressions

For documentation on Qc, see file [Coq.QArith.Qcanon].

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)

Set Implicit Arguments.
From TLC Require Export LibCore.
From CFML Require Export LibSepTLCbuffer.
From Coq Require Export Qcanon.
Local Open Scope Qc_scope.
From Coq Require Export Field. (* for the [field] tactic *)


(* ********************************************************************** *)
(** * Assumptions of the functor *)

Module Type XsimplParams.


(* ---------------------------------------------------------------------- *)
(* ** Operators *)

Parameter hprop : Type.

Parameter himpl : hprop -> hprop -> Prop.

Definition qimpl A (Q1 Q2:A->hprop) :=
  forall r, himpl (Q1 r) (Q2 r).

Parameter hempty : hprop.

Parameter hstar : hprop -> hprop -> hprop.

Parameter hpure : Prop -> hprop.

Parameter htop : hprop.

Parameter hgc : hprop.

Parameter hwand : hprop -> hprop -> hprop.

Parameter qwand : forall A, (A->hprop) -> (A->hprop) -> hprop.

Parameter hexists : forall A, (A->hprop) -> hprop.

Parameter hforall : forall A, (A->hprop) -> hprop.

Parameter haffine : hprop -> Prop.


(* ---------------------------------------------------------------------- *)
(* ** Notations *)

Declare Scope heap_scope.

Notation "H1 ==> H2" := (himpl H1 H2)
  (at level 55) : heap_scope.

Notation "Q1 ===> Q2" := (qimpl Q1 Q2)
  (at level 55) : heap_scope.

Notation "\[]" := (hempty)
  (at level 0) : heap_scope.

Notation "\[ P ]" := (hpure P)
  (at level 0, format "\[ P ]") : heap_scope.

Notation "\Top" := (htop) : heap_scope.

Notation "\GC" := (hgc) : heap_scope.

Notation "H1 '\*' H2" := (hstar H1 H2)
  (at level 41, right associativity) : heap_scope.

Notation "Q \*+ H" := (fun x => hstar (Q x) H)
  (at level 40) : heap_scope.

Notation "H1 \-* H2" := (hwand H1 H2)
  (at level 43, right associativity) : heap_scope.

Notation "Q1 \--* Q2" := (qwand Q1 Q2)
  (at level 43) : heap_scope.

Notation "'\exists' x1 .. xn , H" :=
  (hexists (fun x1 => .. (hexists (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\exists' '/ '  x1  ..  xn , '/ '  H ']'") : heap_scope.

Notation "'\forall' x1 .. xn , H" :=
  (hforall (fun x1 => .. (hforall (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\forall' '/ '  x1  ..  xn , '/ '  H ']'") : heap_scope.

Local Open Scope heap_scope.


(* ---------------------------------------------------------------------- *)
(* ** Properties *)

Implicit Types P : Prop.
Implicit Types H : hprop.

(** Entailment is an order *)

Parameter himpl_refl : forall H,
  H ==> H.

Parameter himpl_trans : forall H2 H1 H3,
  (H1 ==> H2) ->
  (H2 ==> H3) ->
  (H1 ==> H3).

Parameter himpl_antisym : forall H1 H2,
  (H1 ==> H2) ->
  (H2 ==> H1) ->
  (H1 = H2).

(** Commutative monoid *)

Parameter hstar_hempty_l : forall H,
  \[] \* H = H.

Parameter hstar_hempty_r : forall H,
  H \* \[] = H.

Parameter hstar_comm : forall H1 H2,
   H1 \* H2 = H2 \* H1.

Parameter hstar_assoc : forall H1 H2 H3,
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).

(** The frame property for entailment *)

Parameter himpl_frame_lr : forall H1 H1' H2 H2',
  H1 ==> H1' ->
  H2 ==> H2' ->
  (H1 \* H2) ==> (H1' \* H2').

Parameter himpl_hstar_trans_l : forall H1 H2 H3 H4,
  H1 ==> H2 ->
  H2 \* H3 ==> H4 ->
  H1 \* H3 ==> H4.

(** Characterization of hpure *)

Parameter himpl_hempty_hpure : forall P,
  P ->
  \[] ==> \[P].

Parameter himpl_hstar_hpure_l : forall P H H',
  (P -> H ==> H') ->
  (\[P] \* H) ==> H'.

(** Characterization of hexists *)

Parameter himpl_hexists_l : forall A H (J:A->hprop),
  (forall x, J x ==> H) ->
  (hexists J) ==> H.

Parameter himpl_hexists_r : forall A (x:A) H J,
  (H ==> J x) ->
  H ==> (hexists J).

Parameter hstar_hexists : forall A (J:A->hprop) H,
  (hexists J) \* H = hexists (fun x => (J x) \* H).

(** Characterization of hforall *)

Parameter himpl_hforall_r : forall A (J:A->hprop) H,
  (forall x, H ==> J x) ->
  H ==> (hforall J).

Parameter hstar_hforall : forall H A (J:A->hprop),
  (hforall J) \* H ==> hforall (J \*+ H).

(** Properties of hwand *)

Parameter hwand_equiv : forall H0 H1 H2,
  (H0 ==> H1 \-* H2) <-> (H1 \* H0 ==> H2).

Parameter hwand_curry_eq : forall H1 H2 H3,
  (H1 \* H2) \-* H3 = H1 \-* (H2 \-* H3).

Parameter hwand_hempty_l : forall H,
  (\[] \-* H) = H.

(** Properties of qwand *)

Parameter qwand_equiv : forall H A (Q1 Q2:A->hprop),
  H ==> (Q1 \--* Q2) <-> (Q1 \*+ H) ===> Q2.

Parameter hwand_cancel : forall H1 H2,
  H1 \* (H1 \-* H2) ==> H2.

Parameter qwand_specialize : forall A (x:A) (Q1 Q2:A->hprop),
  (Q1 \--* Q2) ==> (Q1 x \-* Q2 x).

(** Characterization of htop *)

Parameter himpl_htop_r : forall H,
  H ==> \Top.

Parameter hstar_htop_htop :
  \Top \* \Top = \Top.

(** Characterization of hgc *)

Parameter haffine_hempty :
  haffine \[].

Parameter himpl_hgc_r : forall H,
  haffine H ->
  H ==> \GC.

Parameter hstar_hgc_hgc :
  \GC \* \GC = \GC.

End XsimplParams.

(* ---------------------------------------------------------------------- *)
(** * Assumptions of the functor with credits *)

Module Type XsimplParamsCredits.

Include XsimplParams.

Parameter use_credits : bool.

Notation "'credits'" := Qcanon.Qc.
Local Open Scope Qc_scope.
Delimit Scope Qc_scope with cr.

Parameter hcredits : credits -> hprop.

Notation "'\$' n" := (hcredits (Z2Qc n))
  (at level 40,
   n at level 0,
   format "\$ n") : heap_scope.

Notation "'\$$' n" := (hcredits n)
  (at level 40,
   n at level 0,
   format "\$$  n") : heap_scope.

Open Scope heap_scope.

Parameter hcredits_skip :
  use_credits = false ->
  forall (n:credits), \$$ n = \[].

Parameter hcredits_zero :
  \$$ (0%cr) = \[].

Parameter hcredits_add : forall n m,
  \$$ (n+m)%cr = \$$ n \* \$$ m.

Parameter hwand_hcredits_l : forall H n,
  (\$$n \-* H) = (\$$(-n)%cr \* H).

Parameter haffine_hcredits : forall n,
  n >= 0 ->
  haffine (\$$ n).

End XsimplParamsCredits.


(* ********************************************************************** *)
(** * Body of the functor *)

Module XsimplSetupCredits (HPC : XsimplParamsCredits).
Import HPC.

Local Open Scope heap_scope.

Implicit Types H : hprop.
Implicit Types P : Prop.

Hint Resolve himpl_refl.


(* ********************************************************************** *)
(** * Derived properties of operators *)

(* ---------------------------------------------------------------------- *)
(* ** Properties of [himpl] *)

Lemma himpl_of_eq : forall H1 H2,
  H1 = H2 ->
  H1 ==> H2.
Proof. intros. subst. applys~ himpl_refl. Qed.

Lemma himpl_of_eq_sym : forall H1 H2,
  H1 = H2 ->
  H2 ==> H1.
Proof. intros. subst. applys~ himpl_refl. Qed.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [qimpl] *)

Lemma qimpl_refl : forall A (Q:A->hprop),
  Q ===> Q.
Proof using. intros. hnfs*. Qed.

Hint Resolve qimpl_refl.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [hstar] *)

Lemma hstar_comm_assoc : forall H1 H2 H3,
  H1 \* H2 \* H3 = H2 \* H1 \* H3.
Proof using.
  intros. rewrite <- hstar_assoc.
  rewrite (@hstar_comm H1 H2). rewrite~ hstar_assoc.
Qed.



(* ********************************************************************** *)
(** * Representation predicates *)

(* ---------------------------------------------------------------------- *)
(* ** Notation for representation predicates *)

(** The arrow notation typically takes the form [x ~> R x],
   to indicate that [X] is the logical value that describes the
   heap structure [x], according to the representation predicate [R].
   It is just a notation for the heap predicate [R X x]. *)

Definition repr (A:Type) (S:A->hprop) (x:A) : hprop :=
  S x.

Notation "x '~>' S" := (repr S x)
  (at level 33, no associativity) : heap_scope.

Lemma repr_eq : forall (A:Type) (S:A->hprop) (x:A),
  (x ~> S) = (S x).
Proof using. auto. Qed.

(** [x ~> Id X] holds when [x] is equal to [X] in the empty heap.
   [Id] is called the identity representation predicate. *)

Definition Id {A:Type} (X:A) (x:A) :=
  \[ X = x ].

(** [xrepr_clean] simplifies instances of
   [p ~> (fun _ => _)] by unfolding the arrow,
   but only when the body does not captures
   mklocally-bound variables. This tactic should
   normally not be used directly *)

Ltac xrepr_clean_core tt :=
  repeat match goal with |- context C [?p ~> ?E] =>
   match E with (fun _ => _) =>
     let E' := eval cbv beta in (E p) in
     let G' := context C [E'] in
     let G := match goal with |- ?G => G end in
     change G with G' end end.

Tactic Notation "xrepr_clean" :=
  xrepr_clean_core tt.

Lemma repr_id : forall A (x X:A),
  (x ~> Id X) = \[X = x].
Proof using. intros. unfold Id. xrepr_clean. auto. Qed.


(* ---------------------------------------------------------------------- *)
(* ** [rew_heap] tactic to normalize expressions with [hstar] *)

(** [rew_heap] removes empty heap predicates, and normalizes w.r.t.
    associativity of star.

    [rew_heap_assoc] only normalizes w.r.t. associativity.
    (It should only be used internally for tactic implementation. *)

Lemma star_post_empty : forall B (Q:B->hprop),
  Q \*+ \[] = Q.
Proof using. extens. intros. rewrite* hstar_hempty_r. Qed.

Hint Rewrite hstar_hempty_l hstar_hempty_r
             hstar_assoc star_post_empty hwand_hempty_l
             hcredits_zero hcredits_add : rew_heap.

Tactic Notation "rew_heap" :=
  autorewrite with rew_heap.
Tactic Notation "rew_heap" "in" "*" :=
  autorewrite with rew_heap in *.
Tactic Notation "rew_heap" "in" hyp(H) :=
  autorewrite with rew_heap in H.

Tactic Notation "rew_heap" "~" :=
  rew_heap; auto_tilde.
Tactic Notation "rew_heap" "~" "in" "*" :=
  rew_heap in *; auto_tilde.
Tactic Notation "rew_heap" "~" "in" hyp(H) :=
  rew_heap in H; auto_tilde.

Tactic Notation "rew_heap" "*" :=
  rew_heap; auto_star.
Tactic Notation "rew_heap" "*" "in" "*" :=
  rew_heap in *; auto_star.
Tactic Notation "rew_heap" "*" "in" hyp(H) :=
  rew_heap in H; auto_star.

Hint Rewrite hstar_assoc : rew_heap_assoc.

Tactic Notation "rew_heap_assoc" :=
  autorewrite with rew_heap_assoc.


(* ---------------------------------------------------------------------- *)
(** Auxiliary tactics used by [xpull] and [xsimpl] *)

Ltac remove_empty_heaps_from H :=
  match H with context[ ?H1 \* \[] ] =>
    match is_evar_as_bool H1 with
    | false => rewrite (@hstar_hempty_r H1)
    | true => let X := fresh in
              set (X := H1);
              rewrite (@hstar_hempty_r X);
              subst X
    end end.

Ltac remove_empty_heaps_haffine tt :=
  repeat match goal with |- haffine ?H => remove_empty_heaps_from H end.

Ltac remove_empty_heaps_left tt :=
  repeat match goal with |- ?H1 ==> _ => remove_empty_heaps_from H1 end.

Ltac remove_empty_heaps_right tt :=
  repeat match goal with |- _ ==> ?H2 => remove_empty_heaps_from H2 end.



(* ********************************************************************** *)
(* * Tactic [xsimpl] for heap entailments *)

(* ---------------------------------------------------------------------- *)
(** [xsimpl_beautify_credits] for beautifying arithmetics involved in credits *)


(** [xsimpl_beautify_credits] applies in every credit expression:
    - Gather and compute the sum of numbers.
    - Separate positives and negatives expressions in two groups.
    - Cancel each pair (n,-n) of expressions.
    - Pretty-print the result.
   It applies this process both to credits in Z and in Qc. To that end:
    - it isolates credits in Z
    - it cleans up credits in Qc, the result might end up in Z
    - it cleans up the Z part
    - it produces the sum of the two parts, cleaning up the zeros if any.
*)

Definition xsimpl_hcredits_protect (n:credits) : hprop :=
  \$$n.

Ltac xsimpl_beautify_credits_is_const_Z n :=
  (* note: we purposely don't recurse over binary operators such as Z.add *)
  match n with
  | Z0 => constr:(true)
  | Zneg _ => constr:(true)
  | Zpos _ => constr:(true)
  | Z.opp ?n' => xsimpl_beautify_credits_is_const_Z n'
  | _ => constr:(false)
  end.

Ltac xsimpl_beautify_credits_is_const_Qc n :=
  (* TODO: this implementation is somewhat approximative *)
  match n with
  | Z2Qc ?m => xsimpl_beautify_credits_is_const_Z m
  | _ =>
     match n with
     | 0%Qc => constr:(true)
     | 1%Qc => constr:(true)
     | (-1)%Qc => constr:(true)
     (* TODO: incomplete... *)
     | Qcmake (Coq.QArith.QArith_base.Qmake ?a ?b) =>
       match xsimpl_beautify_credits_is_const_Z a with
       | false => constr:(false)
       | true =>
         match b with
         | Coq.Numbers.BinNums.xI => constr:(true)
         | Coq.Numbers.BinNums.xO => constr:(true)
         | Coq.Numbers.BinNums.xH => constr:(true)
         end
       end
     | _ => constr:(false)
     end
   end.

Lemma xsimpl_beautify_credits_is_const_demo : forall (m:Z) (n:Qc), True.
  intros.
  let x := xsimpl_beautify_credits_is_const_Z 0%Z in pose x.
  let x := xsimpl_beautify_credits_is_const_Z 3%Z in pose x.
  let x := xsimpl_beautify_credits_is_const_Z (- 3)%Z in pose x.
  let x := xsimpl_beautify_credits_is_const_Z (- (3))%Z in pose x.
  let x := xsimpl_beautify_credits_is_const_Z (3 + 4)%Z in pose x.
  let x := xsimpl_beautify_credits_is_const_Z (- m)%Z in pose x.
  let x := xsimpl_beautify_credits_is_const_Qc 0%Qc in pose x.
  let x := xsimpl_beautify_credits_is_const_Qc (- 3)%Qc in pose x.
  let x := xsimpl_beautify_credits_is_const_Qc (- n)%Qc in pose x.
  (* compute on Qc does not seem to work well
    let y := (eval compute in (1 / Z2Qc 4)) in set (a := y). *)
  let x := xsimpl_beautify_credits_is_const_Qc (1 / 1)%Qc in pose x.
Abort.

(* Auxiliary *)
Ltac ltac_neg pos :=
  match pos with
  | true => constr:(false)
  | false => constr:(true)
  end.

(* [xsimpl_beautify_split_Z_and_Qc n] takes a term in [Qc] and
   returns a pair of lists [(Lz,Lq)] such that
   [n = Z2Qc (fold Z.add Lz) + (fold Qc.add Lq)]. *)

Ltac xsimpl_beautify_split_Z_and_Qc n :=
  let rec auxZ acc pos m := (* this function expects (m:Z) *)
    match m with
    | (?n1 + ?n2)%Z =>
      let R := auxZ acc pos n1 in
      auxZ R pos n2
    | (?n1 - ?n2)%Z =>
      let R := auxZ acc pos n1 in
      let posneg := ltac_neg pos in
      auxZ R posneg n2
    | (- ?n1)%Z =>
      let posneg := ltac_neg pos in
      auxZ acc posneg n1
    | 0%Z => constr:(acc)
    | _ =>
       let m' :=
          match pos with
          | true => constr:(m)
          | false => constr:((-m)%Z)
          end in
        match acc with (?Lz,?Lq) =>
          constr:(((m' :: Lz), Lq)) end
    end in
  let rec aux acc pos n := (* this function expects (n:Qc) *)
      match n with
      | Z2Qc ?m => auxZ acc pos m
      | (?n1 + ?n2)%Qc =>
        let R := aux acc pos n1 in
        aux R pos n2
      | (?n1 - ?n2)%Qc =>
        let R := aux acc pos n1 in
        let posneg := ltac_neg pos in
        aux R posneg n2
      | (- ?n1)%Qc =>
        let posneg := ltac_neg pos in
        aux acc posneg n1
      | 0%Qc => constr:(acc)
      | _ =>
        let n' :=
          match pos with
          | true => constr:(n)
          | false => constr:((-n)%Qc)
          end in
         match acc with (?Lz,?Lq) =>
          constr:((Lz, (n' :: Lq))) end
      end in
  aux (@nil Z, @nil Qc) true n.

Lemma xsimpl_beautify_split_Z_and_Qc_demo : forall (m1 m2 m3 m4:Z) (n1 n2 n3 n4:Qc), True.
  intros.
  let x := xsimpl_beautify_split_Z_and_Qc
    (n1 + Z2Qc 4%Z - (n2 + n3) - Z2Qc (m1 - (m2 - m3))%Z - Z2Qc 3%Z - n4 + Z2Qc m4)%Qc in pose x.
Abort.

(* [xsimpl_beautify_credits_sort_cst_neg_pos_Z L] takes a list of
   Z values, and returns a triple of the form [(C,Ln,Lp)]
   such that [(sum Z.add L) = C - (sum Z.add Ln) + (sum Z.add Lp)].
    where
   - C is a term of type int made exactly of actual numbers in n.
   - Ln is a list of negatives variables in n.
   - Lp is a list of positives variables in n.
     Nonnegative evars are in the last positions of Lp. *)
Ltac xsimpl_beautify_credits_sort_cst_neg_pos_Z L :=
  let rec aux acc L :=
    match L with
    | nil => constr:(acc)
    | ?m::?L' =>
        let acc' :=
          match acc with (?C, ?Ln, ?Lp) =>
            match xsimpl_beautify_credits_is_const_Z m with
            | true =>
                constr:( ((m + C)%Z, Ln, Lp) )
            | false =>
                match m with
                | (- ?m1)%Z => constr:( (C, (m1::Ln), Lp) )
                | _ =>
                    let Lp' :=
                      match is_evar_as_bool m with
                      | false => constr:(m::Lp)
                      | true => list_snoc m Lp
                      end in
                    constr:( (C,Ln,Lp') )
                end
            end
          end in
        aux acc' L'
    end in
  aux (0%Z, @nil Z, @nil Z) L.

Lemma xsimpl_beautify_credits_sort_cst_neg_pos_Z_demo : forall (m1 m2 m3 m4:Z), True.
  intros.
  let x := xsimpl_beautify_credits_sort_cst_neg_pos_Z
    (m1 :: -m2 :: m2 :: 0 :: -m3 :: -3 :: m3 :: m3 :: -2 :: 4 :: nil)%Z in pose x.
  let x := xsimpl_beautify_credits_sort_cst_neg_pos_Z
    (( (- (5))%Z :: (- m1)%Z :: (- (2))%Z :: (- m2)%Z :: m3 :: m2 :: nil))%Z in pose x.
Abort.

(* [xsimpl_beautify_credits_sort_cst_neg_pos_Qc L] takes a list of
   Qc values, and returns a triple of the form [(C,Ln,Lp)]
   such that [(sum Qc.add L) = C - (sum Qc.add Ln) + (sum Qc.add Lp)]. *)
Ltac xsimpl_beautify_credits_sort_cst_neg_pos_Qc L :=
  let rec aux acc L :=
    match L with
    | nil => constr:(acc)
    | ?m::?L' =>
        let acc' :=
          match acc with (?C, ?Ln, ?Lp) =>
            match xsimpl_beautify_credits_is_const_Qc m with
            | true =>
                (* TEMPORARY: dont accumulate the initial zero because we don't simplify it later *)
                match C with
                | 0%Qc => constr:( (m, Ln, Lp) )
                | _ => constr:( ((m + C)%Qc, Ln, Lp) )
                end
            | false =>
                match m with
                | (- ?m1)%Qc => constr:( (C, (m1::Ln), Lp) )
                | _ =>
                    let Lp' :=
                      match is_evar_as_bool m with
                      | false => constr:(m::Lp)
                      | true => list_snoc m Lp
                      end in
                    constr:( (C,Ln,Lp') )
                end
            end
          end in
        aux acc' L'
    end in
  aux (0%Qc, @nil Qc, @nil Qc) L.

Lemma xsimpl_beautify_credits_sort_cst_neg_pos_Qc_demo : forall (n1 n2 n3 n4:Qc), True.
  intros.
  let x := xsimpl_beautify_credits_sort_cst_neg_pos_Qc
    (n1 :: -n2 :: n2 :: -n3 :: 1%Qc :: n3 :: n3 :: (Z2Qc (-2)) :: (Z2Qc 4) :: nil)%Qc in pose x.
Abort.

(* [xsimpl_beautify_find_and_remove x L]
   that returns [None] if [x] is not in [L], and [Some L'] where
   [L'] is [L] minus one occurence of [x] if there is one occurence
   of [x] in [L]. *)
Ltac xsimpl_beautify_find_and_remove x L :=
  match L with
  | @nil ?T => constr:(@None (list T))
  | @cons ?T x ?L' => constr:(Some L')
  | @cons ?T ?a ?L' => (* applies when x <> a *)
    let acc := xsimpl_beautify_find_and_remove x L' in
    match acc with
    | None => constr:(@None (list T))
    | Some ?L'' => constr:(Some (a::L''))
    end
  end.

(* Takes two lists [Ln] and [Lp], and returns a pair [Ln',Lp']
   where matching elements in [Ln] and [Lp] are cancelled out
   from the two lists. *)
Ltac xsimpl_beautify_credits_simpl_list Ln Lp :=
  let rec aux Ln Lp :=
      match Ln with
      | nil => constr:((Ln,Lp))
      | ?x::?Ln' =>
        match xsimpl_beautify_find_and_remove x Lp with
        | None =>
          match aux Ln' Lp with
          | (?LL,?LR) => constr:((x::LL,LR))
          end
        | Some ?Lp' => aux Ln' Lp'
       end
     end in
  aux Ln Lp.

Lemma xsimpl_beautify_credits_simpl_list : forall (m1 m2 m3 m4:Z), True.
  intros.
  let x := xsimpl_beautify_credits_simpl_list (m1::m2::m3::m3::nil) (m3::m4::m2::nil) in pose x.
Abort.

(* Computer a prettified version of [C + sum Z.add Lp - sum Z.add Ln]
   with values in Z *)
Ltac xsimpl_beautify_credits_list_to_arith_Z Ln Lp C :=
  let add x y := constr:((x + y)%Z) in
  let sub x y := constr:((x - y)%Z) in
  (* LATER: vm_compute was done before, so we should be able to test if C = 0%Z *)
  let t := (eval vm_compute in (C =? 0)%Z) in
  match t with
  | true =>
    match constr:((Ln,Lp)) with
    | (nil, nil) => constr:(0%Z)
    | (?a::?Ln', nil) => fold_left sub (-a)%Z Ln'
    | (_, ?a::?Lp') =>
      let p := fold_left add a Lp' in
      fold_left sub p Ln
    end
  | false =>
    let p := fold_left add C Lp in
    fold_left sub p Ln
  end.

Lemma xsimpl_beautify_credits_list_to_arith_Z_demo : forall (m1 m2 m3 m4:Z), True.
  intros.
  let x := xsimpl_beautify_credits_list_to_arith_Z (m1::m2::m3::nil) (m4::nil) 2%Z in pose x.
  let x := xsimpl_beautify_credits_list_to_arith_Z (m1::m2::m3::nil) (m4::nil) 0%Z in pose x.
  let x := xsimpl_beautify_credits_list_to_arith_Z (m1::m2::m3::nil) (@nil Z) 0%Z in pose x.
  let x := xsimpl_beautify_credits_list_to_arith_Z (@nil Z) (m1::m2::m3::nil) 2%Z in pose x.
  let x := xsimpl_beautify_credits_list_to_arith_Z (@nil Z) (m1::m2::m3::nil) 0%Z in pose x.
  let x := xsimpl_beautify_credits_list_to_arith_Z (@nil Z) (@nil Z) 2%Z in pose x.
Abort.

(* Computer a prettified version of [C + sum Qc.add Lp - sum Qc.add Ln]
   with values in Qc *)
Ltac xsimpl_beautify_credits_list_to_arith_Qc Ln Lp C :=
  let add x y := constr:((x + y)%Qc) in
  let sub x y := constr:((x - y)%Qc) in
  (* TEMPORARY: deactivate computation in C *)
  (*let t := (eval vm_compute in (C ?= 0)%Qc) in
  match t with
  | true => *)
  match C with
  | 0%Qc =>
    match constr:((Ln,Lp)) with
    | (nil, nil) => constr:(0%Qc)
    | (?a::?Ln', nil) => fold_left sub (-a)%Qc Ln'
    | (_, ?a::?Lp') =>
      let p := fold_left add a Lp' in
      fold_left sub p Ln
    end
  | _ =>
    let p := fold_left add C Lp in
    fold_left sub p Ln
  end.

Lemma xsimpl_beautify_credits_list_to_arith_Qc_demo : forall (n1 n2 n3 n4 c:Qc), True.
  intros.
  let x := xsimpl_beautify_credits_list_to_arith_Qc (n1::n2::n3::nil) (n4::nil) c in pose x.
  let x := xsimpl_beautify_credits_list_to_arith_Qc (n1::n2::n3::nil) (n4::nil) c in pose x.
  let x := xsimpl_beautify_credits_list_to_arith_Qc (n1::n2::n3::nil) (@nil Z) 0%Qc in pose x.
  let x := xsimpl_beautify_credits_list_to_arith_Qc (@nil Z) (n1::n2::n3::nil) c in pose x.
  let x := xsimpl_beautify_credits_list_to_arith_Qc (@nil Z) (n1::n2::n3::nil) 0%Qc in pose x.
  let x := xsimpl_beautify_credits_list_to_arith_Qc (@nil Z) (@nil Z) c in pose x.
Abort.

(* .. list_rev *)

(* [xsimpl_beautify_credits_core_Z L] takes [L] a list of Z values,
   and returns a beautified Z value. *)
Ltac xsimpl_beautify_credits_core_Z L :=
  match xsimpl_beautify_credits_sort_cst_neg_pos_Z L with (?C, ?Ln, ?Lp) =>
   let C' := (eval vm_compute in C) in
   match xsimpl_beautify_credits_simpl_list Ln Lp with (?Ln', ?Lp') =>
    xsimpl_beautify_credits_list_to_arith_Z Ln' Lp' C'
   end end.

(* [xsimpl_beautify_credits_core_Qc L] takes [L] a list of Qc values,
   and returns a beautified Qc value. *)
Ltac xsimpl_beautify_credits_core_Qc L :=
  match xsimpl_beautify_credits_sort_cst_neg_pos_Qc L with (?C, ?Ln, ?Lp) =>
   (* let C' := (eval vm_compute in C) in TEMPORARY NOT DONE *)
   let C' := constr:(C) in
   match xsimpl_beautify_credits_simpl_list Ln Lp with (?Ln', ?Lp') =>
    xsimpl_beautify_credits_list_to_arith_Qc Ln' Lp' C'
   end end.

Lemma xsimpl_beautify_credits_core_demo : forall (m1 m2 m3 m4:Z) (n1 n2 n3 n4:Qc), True.
  intros.
  let x := xsimpl_beautify_credits_core_Z (m1::m3::m2::(-m3)::m3::(-m4)::3::(-m2)::0::nil)%Z in pose x.
  let x := xsimpl_beautify_credits_core_Qc (n1::n3::n2::(-n3)::n3::(-n4)::1%Qc::(-n2)::0%Qc::nil)%Qc in pose x.
Abort.

(* [xsimpl_beautify_credits_core n] takes an argument [n:Qc]
   and returns a beautified version of it. *)
Ltac xsimpl_beautify_credits_core n :=
  match xsimpl_beautify_split_Z_and_Qc n with (?Lz,?Lq) =>
    let Vz := xsimpl_beautify_credits_core_Z Lz in
    let Vq := xsimpl_beautify_credits_core_Qc Lq in
    match constr:( (Vz, Vq) ) with
    | (0%Z, _) => constr:(Vq)
    | (_, 0%Qc) => constr:(Z2Qc Vz)
    | (_, (- 0)%Qc) => constr:(Z2Qc Vz)
    | (_, _) => constr:( (Z2Qc Vz + Vq)%Qc ) (* LATER: if Vq starts with a negative value, we get Vz+(-Vq) *)
    end
  end.

Lemma xsimpl_beautify_credits_core_demo : forall (m1 m2 m3 m4:Z) (n1 n2 n3 n4:Qc), True.
  intros.
  let n := constr:(((Z2Qc 0) + Z2Qc m2 - (n1 - n3) - Z2Qc (- m3 + m2) - Z2Qc 2 - (n2 + Z2Qc m1) + (n3 + n4) + 1%Qc - Z2Qc 5)%Qc) in
  let x := xsimpl_beautify_credits_core n in pose x.
Abort.

(* [xsimpl_beautify_credits_solver tt] is invoked on a goal of the form [n1 = n2]
   to prove that [n2] is a simplified version of [n1] .*)
Ltac xsimpl_beautify_credits_solver tt :=
  unfold xsimpl_hcredits_protect;
  try match goal with |- hcredits _ = hcredits _ => fequal end; 
  try match goal with |- Z2Qc _ = Z2Qc _ => fequal end;
   try solve [ math | ring ].

(* [xsimpl_beautify_credits_using replacer n] applies the operation
   [replacer] to reclace occurrences of [\$$ n] in specific locations
   with [\$$ n'], where [n'] is a beautified version of [n]. *)
Ltac xsimpl_beautify_credits_using replacer n :=
  let n' := xsimpl_beautify_credits_core n in
  replacer (\$$n) (xsimpl_hcredits_protect n');
  [ | xsimpl_beautify_credits_solver tt ].

Ltac xsimpl_beautify_credits_once_hyp tt :=
  match goal with
  | H: context [ \$$ ?n ] |- _ =>
    let replacer a b := replace a with b in H in
    xsimpl_beautify_credits_using replacer n
  end.

Ltac xsimpl_beautify_credits_once_goal tt :=
  match goal with
  | |- context [ \$$ ?n ] =>
    let replacer a b := (replace a with b) in
    xsimpl_beautify_credits_using replacer n
  end.

Ltac xsimpl_beautify_credits_goal tt :=
  rew_qc in *;
  repeat (xsimpl_beautify_credits_once_goal tt);
  unfolds xsimpl_hcredits_protect.

Ltac xsimpl_beautify_credits_everywhere tt :=
  rew_qc;
  repeat (xsimpl_beautify_credits_once_goal tt);
  repeat (xsimpl_beautify_credits_once_hyp tt);
  unfolds xsimpl_hcredits_protect.

Tactic Notation "xsimpl_beautify_credits" :=
  xsimpl_beautify_credits_everywhere tt.

(* Unit tests for auxiliary functions *)

Example ring_tactic_demo : (forall a b c:Z,
    (a + b + c) ^ 2 =
     a * a + b ^ 2 + c * c + 2 * a * b + 2 * a * c + 2 * b * c)%Z.
Proof. intros. ring. Abort.

Example ring_tactic_demo : (forall a b:Z,
    (a + b) ^ 2 - a * a - b * b - 2 * a * b = 0)%Z.
Proof. intros. ring. Abort.

Example field_tactic_demo : (forall x y : Qc, y<>0 -> (x/y)*y = x)%Qc.
Proof. intros. field. auto. Abort.


Lemma xsimpl_hcredits_beautify_demo_Z : forall (n1 n2 n3 n4 n5:int),
  \$ (- (n3 + 2 - 4 - n4)) ==> \$(2 - (n3 + n4) - n5) ->
  \$ (0 + n1 - 2 - n2 + (n3 + n4) - n5 - 5) ==> \$ (- (n3 + n4) - n5 - 7).
Proof using.
  intros. dup 2.
  { xsimpl_beautify_credits_once_goal tt.
    xsimpl_beautify_credits_once_goal tt.
    unfolds xsimpl_hcredits_protect. demo. }
  { rew_qc in *;
    repeat (xsimpl_beautify_credits_once_goal tt);
    unfolds xsimpl_hcredits_protect. demo. }
Abort.

Lemma xsimpl_hcredits_beautify_demo_Qc : forall (n1 n2 n3 n4 n5:credits),
  \$$ (- (n3 + Z2Qc 2 - Z2Qc 4 - n4))%cr ==> \$$(Z2Qc 2 - (n3 + n4) - n5)%cr ->
  \$$ (Z2Qc 0 + n1 - Z2Qc 2 - n2 + (n3 + n4) - n5 - Z2Qc 5)%cr ==> \$$ (- (n3 + n4) - n5 - Z2Qc 7)%cr.
Proof using.
  intros.
  { xsimpl_beautify_credits_once_goal tt.
    xsimpl_beautify_credits_once_goal tt.
    unfolds xsimpl_hcredits_protect. demo. demo. demo. }
Abort.


(* ---------------------------------------------------------------------- *)
(** [xsimpl_beautify_nonneg_and_eqzero_goal] simplifies proof obligations of the
    form [n >= 0] or [n = 0], which typically arise from [xsimpl] *)

Delimit Scope comp_scope with C.

Notation "'0%Qc'" := (Q2Qc {| QArith_base.Qnum := 0; QArith_base.Qden := 1 |}) : Qc_scope.
Notation "'1%Qc'" := (Q2Qc {| QArith_base.Qnum := 1; QArith_base.Qden := 1 |}) : Qc_scope.

Axiom Qc2Q_Z2Qc : forall (n:Z),  (* TODO: move *)
  Qcanon.this (Z2Qc n) = {| QArith_base.Qnum := n; QArith_base.Qden := 1 |}.
(*Proof using.
  intros n. simpl. Locate ggcdn.
Qed. *)

Lemma xsimpl_hcredits_Z : forall (n:Z),
  (n >= 0%Z)%C ->
  (Z2Qc n >= 0)%Qc.
Proof using.
  introv M. asserts N: (0 <= n)%Z. { math. }
  rewrite QArith_base.Zle_Qle in N. rewrite Qc2Q_Z2Qc.
  simpl. applys N.
Qed.

Axiom xsimpl_hcredits_Z' : forall (n:Z),
  (n >= 0%Z)%C ->
  (QArith_base.Qle (Q2Qc {| QArith_base.Qnum := 0; QArith_base.Qden := 1 |}) (Z2Qc n))%Qc.


Axiom xsimpl_hcredits_ZZ : forall (n m:Z),
  (n >= m)%C ->
  (QArith_base.Qle (Z2Qc m) (Z2Qc n))%Qc.


Axiom Z2QC_eq_zero : forall (n:Z),
  n = 0%Z ->
  Z2Qc n = 0%Qc.


Axiom zero_eq_Z2QC : forall (n:Z),
  n = 0%Z ->
  0%Qc = Z2Qc n.



Axiom Z2Qc_add' : forall (n1 n2:Z),
  Z2Qc n1 + Z2Qc n2 = Z2Qc (n1 + n2)%Z.
Axiom Z2Qc_sub' : forall (n1 n2:Z),
  Z2Qc n1 - Z2Qc n2 = Z2Qc (n1 - n2)%Z.
Axiom Z2Qc_opp' : forall (n1:Z),
  - Z2Qc n1 = Z2Qc (- n1)%Z.
Axiom Z2Qc_zero' :
  0%Qc = Z2Qc 0%Z.
Axiom Z2Qc_zero :
  Z2Qc 0%Z = 0%Qc.

Hint Rewrite Z2Qc_add' Z2Qc_sub' Z2Qc_opp' Z2Qc_zero' Z2Qc_zero' : Z2QC_gather.

Ltac Z2Qc_gather tt :=
  autorewrite with Z2QC_gather.

Ltac Z2QC_restore_zero tt :=
  autorewrite with Z2QC_restore_zero.

Hint Rewrite Z2Qc_zero : Z2QC_restore_zero.


Lemma xsimpl_hcredits_zero :
  (0 >= 0)%Qc.
Proof using. applys QArith_base.Qle_refl. Qed.

Lemma xsimpl_hcredits_nonneg_inst_evar : forall n,
  n - n >= 0.
Proof using.  Admitted. (* TODO *)

Ltac xsimpl_hcredits_nonneg_custom := fail.


Ltac xsimpl_beautify_nonneg_and_eqzero_toZ tt :=
  first 
  [ apply Z2QC_eq_zero
  | apply zero_eq_Z2QC
  | apply xsimpl_hcredits_zero
  | solve [ apply xsimpl_hcredits_nonneg_inst_evar ]
  | apply xsimpl_hcredits_ZZ; try xsimpl_hcredits_nonneg_custom tt
  | apply xsimpl_hcredits_Z'; try xsimpl_hcredits_nonneg_custom tt
  | try xsimpl_hcredits_nonneg_custom tt ].

(* DEPRECATED
Ltac xsimpl_beautify_nonneg_and_eqzero_toZ tt :=
  match goal with
  (* TODO: cleanup *)
  | |- QArith_base.Qle (Qcanon.this (Z2Qc ?m)) (Qcanon.this (Z2Qc ?n)) => apply xsimpl_hcredits_ZZ; try xsimpl_hcredits_nonneg_custom tt
  | |- QArith_base.Qle (Qcanon.this (Q2Qc {| QArith_base.Qnum := 0; QArith_base.Qden := 1 |})) (Qcanon.this (Z2Qc ?n)) =>
       apply xsimpl_hcredits_Z'; try xsimpl_hcredits_nonneg_custom tt
  | |- (Z2Qc ?n >= 0)%Qc => apply xsimpl_hcredits_Z; try xsimpl_hcredits_nonneg_custom tt
  | |- (Z2Qc ?m) = 0%cr => apply Z2QC_eq_zero
  | |- Z2Qc ?m = Z2Qc 0%Z => apply Z2QC_eq_zero
  | |- Z2Qc ?m = Q2Qc {| QArith_base.Qnum := 0; QArith_base.Qden := 1 |} => apply Z2QC_eq_zero
  (* | |- (?n >= 0)%Qc => try xsimpl_hcredits_nonneg_custom tt *)
  | _ => xsimpl_hcredits_nonneg_custom tt (* might fail *)
  end.
*)

Ltac xsimpl_beautify_nonneg_and_eqzero_goal_core tt :=
  let beautify n :=
    let n' := xsimpl_beautify_credits_core n in
    replace n with n'; [ | xsimpl_beautify_credits_solver tt ] in
(* LATER: tag the goals of the form [n>=0] produced by [xsimpl], so that only those 
   are simplified by the tactic. *)
  match goal with 
  (* particular cases *)
  | |- (0 >= 0)%Qc => apply xsimpl_hcredits_zero
  | |- (?n1 - ?n2 >= 0)%Qc => apply xsimpl_hcredits_nonneg_inst_evar (* fallthrough otherwise *)
  (* goal is: [?n >= 0%Qc] *) 
  | |- 
     QArith_base.Qle (Qcanon.this (Q2Qc {| QArith_base.Qnum := 0; QArith_base.Qden := 1 |})) (Qcanon.this ?n) =>
        try beautify n 
  | |- QArith_base.Qle (Qcanon.this (Z2Qc 0%Z)) (Qcanon.this ?n) =>
        try beautify n 
  | |- (fun _ _ : credits => QArith_base.Qle _ _) (?n) _ =>
        try beautify n 
  (* goal is  [?n = 0%Qc] *)
  | |- ?n = 0%cr => try beautify n
  | |- ?n = (Z2Qc 0%Z) => try beautify n
  end.

Ltac xsimpl_beautify_nonneg_and_eqzero_goal tt :=
  Z2Qc_gather tt;
  try xsimpl_beautify_nonneg_and_eqzero_goal_core tt;
  try xsimpl_beautify_nonneg_and_eqzero_toZ tt;
  Z2QC_restore_zero tt.


Lemma xsimpl_beautify_nonneg_and_eqzero_goal_demo1 : forall (n:Qc),
  ((0%Qc + Z2Qc 4 - Z2Qc 2 - n) >= 0%Qc)%cr.
Proof using.
  intros. xsimpl_beautify_nonneg_and_eqzero_goal tt. demo. 
Abort.

Lemma xsimpl_beautify_nonneg_and_eqzero_goal_demo2 : forall (n:Qc),
  ((0%Qc - n + Z2Qc 4 - Z2Qc 4 + n) = 0%Qc)%cr.
Proof using.
  intros. xsimpl_beautify_nonneg_and_eqzero_goal tt. auto. demo.
Abort.

Lemma xsimpl_beautify_nonneg_and_eqzero_goal_demo3 :
  ((0%Qc - Z2Qc 1 + Z2Qc 3) >= 0%Qc)%cr.
Proof using.
  intros. xsimpl_beautify_nonneg_and_eqzero_goal tt. math.
Abort.

Lemma xsimpl_beautify_nonneg_and_eqzero_goal_demo4 : forall (n:Z),
  Z2Qc n = 0%Qc.
Proof using.
  intros. xsimpl_beautify_nonneg_and_eqzero_goal tt. demo.
Abort.


(* ---------------------------------------------------------------------- *)
(* [xaffine] placeholder *)

Ltac xaffine_core tt := (* to be generalized lated *)
  try solve [ assumption | apply haffine_hempty ].

Tactic Notation "xaffine" :=
  xaffine_core tt.


(* ---------------------------------------------------------------------- *)
(* Hints for tactics such as [xsimpl] *)

Inductive Xsimpl_hint : list Boxer -> Type :=
  | xsimpl_hint : forall (L:list Boxer), Xsimpl_hint L.

Ltac xsimpl_hint_put L :=
  let H := fresh "Hint" in
  generalize (xsimpl_hint L); intros H.

Ltac xsimpl_hint_next cont :=
  match goal with H: Xsimpl_hint ((boxer ?x)::?L) |- _ =>
    clear H; xsimpl_hint_put L; cont x end.

Ltac xsimpl_hint_remove tt :=
  match goal with H: Xsimpl_hint _ |- _ => clear H end.


(* ---------------------------------------------------------------------- *)
(* Lemmas [hstars_reorder_..] to flip an iterated [hstar]. *)

(** [hstars_flip tt] applies to a goal of the form [H1 \* .. \* Hn \* \[] = ?H]
    and instantiates [H] with [Hn \* ... \* H1 \* \[]].
    If [n > 12], the maximum arity supported, the tactic unifies [H] with
    the original LHS. *)

Lemma hstars_flip_0 :
  \[] = \[].
Proof using. auto. Qed.

Lemma hstars_flip_1 : forall H1,
  H1 \* \[] = H1 \* \[].
Proof using. auto. Qed.

Lemma hstars_flip_2 : forall H1 H2,
  H1 \* H2 \* \[] = H2 \* H1 \* \[].
Proof using. intros. rew_heap. rewrite (hstar_comm H2). rew_heap~. Qed.

Lemma hstars_flip_3 : forall H1 H2 H3,
  H1 \* H2 \* H3 \* \[] = H3 \* H2 \* H1 \* \[].
Proof using. intros. rewrite <- (hstars_flip_2 H1). rew_heap. rewrite (hstar_comm H3). rew_heap~. Qed.

Lemma hstars_flip_4 : forall H1 H2 H3 H4,
  H1 \* H2 \* H3 \* H4 \* \[] = H4 \* H3 \* H2 \* H1 \* \[].
Proof using. intros. rewrite <- (hstars_flip_3 H1). rew_heap. rewrite (hstar_comm H4). rew_heap~. Qed.

Lemma hstars_flip_5 : forall H1 H2 H3 H4 H5,
  H1 \* H2 \* H3 \* H4 \* H5 \* \[] = H5 \* H4 \* H3 \* H2 \* H1 \* \[].
Proof using. intros. rewrite <- (hstars_flip_4 H1). rew_heap. rewrite (hstar_comm H5). rew_heap~. Qed.

Lemma hstars_flip_6 : forall H1 H2 H3 H4 H5 H6,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* \[]
  = H6 \* H5 \* H4 \* H3 \* H2 \* H1 \* \[].
Proof using. intros. rewrite <- (hstars_flip_5 H1). rew_heap. rewrite (hstar_comm H6). rew_heap~. Qed.

Lemma hstars_flip_7 : forall H1 H2 H3 H4 H5 H6 H7,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* \[]
  = H7 \* H6 \* H5 \* H4 \* H3 \* H2 \* H1 \* \[].
Proof using. intros. rewrite <- (hstars_flip_6 H1). rew_heap. rewrite (hstar_comm H7). rew_heap~. Qed.

Lemma hstars_flip_8 : forall H1 H2 H3 H4 H5 H6 H7 H8,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* H8 \* \[]
  = H8 \* H7 \* H6 \* H5 \* H4 \* H3 \* H2 \* H1 \* \[].
Proof using. intros. rewrite <- (hstars_flip_7 H1). rew_heap. rewrite (hstar_comm H8). rew_heap~. Qed.

Lemma hstars_flip_9 : forall H1 H2 H3 H4 H5 H6 H7 H8 H9,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* H8 \* H9 \* \[]
  = H9 \* H8 \* H7 \* H6 \* H5 \* H4 \* H3 \* H2 \* H1 \* \[].
Proof using. intros. rewrite <- (hstars_flip_8 H1). rew_heap. rewrite (hstar_comm H9). rew_heap~. Qed.

Lemma hstars_flip_10 : forall H1 H2 H3 H4 H5 H6 H7 H8 H9 H10,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* H8 \* H9 \* H10 \* \[]
  = H10 \* H9 \* H8 \* H7 \* H6 \* H5 \* H4 \* H3 \* H2 \* H1 \* \[].
Proof using. intros. rewrite <- (hstars_flip_9 H1). rew_heap. rewrite (hstar_comm H10). rew_heap~. Qed.

Lemma hstars_flip_11 : forall H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* H8 \* H9 \* H10 \* H11 \* \[]
  = H11 \* H10 \* H9 \* H8 \* H7 \* H6 \* H5 \* H4 \* H3 \* H2 \* H1 \* \[].
Proof using. intros. rewrite <- (hstars_flip_10 H1). rew_heap. rewrite (hstar_comm H11). rew_heap~. Qed.

Ltac hstars_flip_lemma i :=
  match number_to_nat i with
  | 0%nat => constr:(hstars_flip_0)
  | 1%nat => constr:(hstars_flip_1)
  | 2%nat => constr:(hstars_flip_2)
  | 3%nat => constr:(hstars_flip_3)
  | 4%nat => constr:(hstars_flip_4)
  | 5%nat => constr:(hstars_flip_5)
  | 6%nat => constr:(hstars_flip_6)
  | 7%nat => constr:(hstars_flip_7)
  | 8%nat => constr:(hstars_flip_8)
  | 9%nat => constr:(hstars_flip_9)
  | 10%nat => constr:(hstars_flip_10)
  | 11%nat => constr:(hstars_flip_11)
  | _ => constr:(hstars_flip_1) (* unsupported *)
  end.

Ltac hstars_arity i Hs :=
  match Hs with
  | \[] => constr:(i)
  | ?H1 \* ?H2 => hstars_arity (S i) H2
  end.

Ltac hstars_flip_arity tt :=
  match goal with |- ?HL = ?HR => hstars_arity 0%nat HL end.

Ltac hstars_flip tt :=
  let i := hstars_flip_arity tt in
  let L := hstars_flip_lemma i in
  eapply L.



(* ---------------------------------------------------------------------- *)
(* Lemmas [hstars_pick_...] to extract hyps in depth. *)

(** [hstars_search Hs test] applies to an expression [Hs]
    of the form either [H1 \* ... \* Hn \* \[]]
    or [H1 \* ... \* Hn]. It invokes the function [test i Hi]
    for each of the [Hi] in turn until the tactic succeeds.
    In the particular case of invoking [test n Hn] when there
    is no trailing [\[]], the call is of the form [test (hstars_last n) Hn]
    where [hstars_last] is an identity tag. *)

Definition hstars_last (A:Type) (X:A) := X.

Ltac hstars_search Hs test :=
  let rec aux i Hs :=
    first [ match Hs with ?H \* _ => test i H end
          | match Hs with _ \* ?Hs' => aux (S i) Hs' end
          | match Hs with ?H => test (hstars_last i) H end ] in
  aux 1%nat Hs.

(** [hstars_pick_lemma i] returns one of the lemma below,
    which enables reordering in iterated stars, by extracting
    the i-th item to bring it to the front. *)

Lemma hstars_pick_1 : forall H1 H,
  H1 \* H = H1 \* H.
Proof using. auto. Qed.

Lemma hstars_pick_2 : forall H1 H2 H,
  H1 \* H2 \* H = H2 \* H1 \* H.
Proof using. intros. rewrite~ (hstar_comm_assoc H1). Qed.

Lemma hstars_pick_3 : forall H1 H2 H3 H,
  H1 \* H2 \* H3 \* H = H3 \* H1 \* H2 \* H.
Proof using. intros. rewrite~ (hstar_comm_assoc H2). applys hstars_pick_2. Qed.

Lemma hstars_pick_4 : forall H1 H2 H3 H4 H,
  H1 \* H2 \* H3 \* H4 \* H = H4 \* H1 \* H2 \* H3 \* H.
Proof using. intros. rewrite~ (hstar_comm_assoc H3). applys hstars_pick_3. Qed.

Lemma hstars_pick_5 : forall H1 H2 H3 H4 H5 H,
  H1 \* H2 \* H3 \* H4 \* H5 \* H = H5 \* H1 \* H2 \* H3 \* H4 \* H.
Proof using. intros. rewrite~ (hstar_comm_assoc H4). applys hstars_pick_4. Qed.

Lemma hstars_pick_6 : forall H1 H2 H3 H4 H5 H6 H,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H
  = H6 \* H1 \* H2 \* H3 \* H4 \* H5 \* H.
Proof using. intros. rewrite~ (hstar_comm_assoc H5). applys hstars_pick_5. Qed.

Lemma hstars_pick_7 : forall H1 H2 H3 H4 H5 H6 H7 H,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* H
  = H7 \* H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H.
Proof using. intros. rewrite~ (hstar_comm_assoc H6). applys hstars_pick_6. Qed.

Lemma hstars_pick_8 : forall H1 H2 H3 H4 H5 H6 H7 H8 H,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* H8 \* H
  = H8 \* H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* H.
Proof using. intros. rewrite~ (hstar_comm_assoc H7). applys hstars_pick_7. Qed.

Lemma hstars_pick_9 : forall H1 H2 H3 H4 H5 H6 H7 H8 H9 H,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* H8 \* H9 \* H
  = H9 \* H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* H8 \* H.
Proof using. intros. rewrite~ (hstar_comm_assoc H8). applys hstars_pick_8. Qed.

Lemma hstars_pick_10 : forall H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* H8 \* H9 \* H10 \* H
  = H10 \* H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* H8 \* H9 \* H.
Proof using. intros. rewrite~ (hstar_comm_assoc H9). applys hstars_pick_9. Qed.

Lemma hstars_pick_11 : forall H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* H8 \* H9 \* H10 \* H11 \* H
  = H11 \* H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* H8 \* H9 \* H10 \* H.
Proof using. intros. rewrite~ (hstar_comm_assoc H10). applys hstars_pick_10. Qed.

Lemma hstars_pick_last_1 : forall H1,
  H1 = H1.
Proof using. auto. Qed.

Lemma hstars_pick_last_2 : forall H1 H2,
  H1 \* H2 = H2 \* H1.
Proof using. intros. rewrite~ (hstar_comm). Qed.

Lemma hstars_pick_last_3 : forall H1 H2 H3,
  H1 \* H2 \* H3 = H3 \* H1 \* H2.
Proof using. intros. rewrite~ (hstar_comm H2). applys hstars_pick_2. Qed.

Lemma hstars_pick_last_4 : forall H1 H2 H3 H4,
  H1 \* H2 \* H3 \* H4 = H4 \* H1 \* H2 \* H3.
Proof using. intros. rewrite~ (hstar_comm H3). applys hstars_pick_3. Qed.

Lemma hstars_pick_last_5 : forall H1 H2 H3 H4 H5,
  H1 \* H2 \* H3 \* H4 \* H5 = H5 \* H1 \* H2 \* H3 \* H4.
Proof using. intros. rewrite~ (hstar_comm H4). applys hstars_pick_4. Qed.

Lemma hstars_pick_last_6 : forall H1 H2 H3 H4 H5 H6,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6
  = H6 \* H1 \* H2 \* H3 \* H4 \* H5.
Proof using. intros. rewrite~ (hstar_comm H5). applys hstars_pick_5. Qed.

Lemma hstars_pick_last_7 : forall H1 H2 H3 H4 H5 H6 H7,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7
  = H7 \* H1 \* H2 \* H3 \* H4 \* H5 \* H6.
Proof using. intros. rewrite~ (hstar_comm H6). applys hstars_pick_6. Qed.

Lemma hstars_pick_last_8 : forall H1 H2 H3 H4 H5 H6 H7 H8,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* H8
  = H8 \* H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7.
Proof using. intros. rewrite~ (hstar_comm H7). applys hstars_pick_7. Qed.

Lemma hstars_pick_last_9 : forall H1 H2 H3 H4 H5 H6 H7 H8 H9,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* H8 \* H9
  = H9 \* H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* H8.
Proof using. intros. rewrite~ (hstar_comm H8). applys hstars_pick_8. Qed.

Lemma hstars_pick_last_10 : forall H1 H2 H3 H4 H5 H6 H7 H8 H9 H10,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* H8 \* H9 \* H10
  = H10 \* H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* H8 \* H9.
Proof using. intros. rewrite~ (hstar_comm H9). applys hstars_pick_9. Qed.

Lemma hstars_pick_last_11 : forall H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11,
    H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* H8 \* H9 \* H10 \* H11
  = H11 \* H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* H7 \* H8 \* H9 \* H10.
Proof using. intros. rewrite~ (hstar_comm H10). applys hstars_pick_10. Qed.

Ltac hstars_pick_lemma i :=
  let unsupported tt := fail 100 "hstars_pick supports only arity up to 11" in
  match i with
  | hstars_last ?j => match number_to_nat j with
    | 1%nat => constr:(hstars_pick_last_1)
    | 2%nat => constr:(hstars_pick_last_2)
    | 3%nat => constr:(hstars_pick_last_3)
    | 4%nat => constr:(hstars_pick_last_4)
    | 5%nat => constr:(hstars_pick_last_5)
    | 6%nat => constr:(hstars_pick_last_6)
    | 7%nat => constr:(hstars_pick_last_7)
    | 8%nat => constr:(hstars_pick_last_8)
    | 9%nat => constr:(hstars_pick_last_9)
    | 10%nat => constr:(hstars_pick_last_10)
    | 11%nat => constr:(hstars_pick_last_11)
    | _ => unsupported tt
    end
  | ?j => match number_to_nat j with
    | 1%nat => constr:(hstars_pick_1)
    | 2%nat => constr:(hstars_pick_2)
    | 3%nat => constr:(hstars_pick_3)
    | 4%nat => constr:(hstars_pick_4)
    | 5%nat => constr:(hstars_pick_5)
    | 6%nat => constr:(hstars_pick_6)
    | 7%nat => constr:(hstars_pick_7)
    | 8%nat => constr:(hstars_pick_8)
    | 9%nat => constr:(hstars_pick_9)
    | 10%nat => constr:(hstars_pick_10)
    | 11%nat => constr:(hstars_pick_11)
    | _ => unsupported tt
    end
  end.



(* ---------------------------------------------------------------------- *)
(* Tactic [xsimpl] *)

(** ... doc for [xsimpl] to update

   At the end, there remains a heap entailment with a simplified
   LHS and a simplified RHS, with items not cancelled out.
   At this point, if the goal is of the form [H ==> \GC] or [H ==> \Top] or
   [H ==> ?H'] for some evar [H'], then [xsimpl] solves the goal.
   Else, it leaves whatever remains.

   For the cancellation part, [xsimpl] cancels out [H] from the LHS
   with [H'] from the RHS if either [H'] is syntactically equal to [H],
   or if [H] and [H'] both have the form [x ~> ...] for the same [x].
   Note that, in case of a mismatch with [x ~> R X] on the LHS and
   [x ~> R' X'] on the RHS, [xsimpl] will produce a goal of the form
   [(x ~> R X) = (x ~> R' X')] which will likely be unsolvable.
   It is the user's responsability to perform the appropriate conversion
   steps prior to calling [xsimpl].

   Remark: the reason for the special treatment of [x ~> ...] is that
   it is very useful to be able to automatically cancel out
   [x ~> R X] from the LHS with [x ~> R ?Y], for some evar [?Y] which
   typically is introduced from an existential, e.g. [\exists Y, x ~> R Y].

   Remark: importantly, [xsimpl] does not attempt any simplification on
   a representation predicate of the form [?x ~> ...], when the [?x]
   is an uninstantiated evar. Such situation may arise for example
   with the following RHS: [\exists p, (r ~> Ref p) \* (p ~> Ref 3)].

   As a special feature, [xsimpl] may be provided optional arguments
   for instantiating the existentials (instead of introducing evars).
   These optional arguments need to be given in left-right order,
   and are used on a first-match basis: the head value is used if its
   type matches the type expected by the existential, else an evar
   is introduced for that existential. *)


(** [Xsimpl (Nc, Hla, Hlw, Hlt) (Hra, Hrg, Hrt)] is interepreted as
    the entailment [\$$Nc \* Hla \* Hlw \* Hlt ==> Hra \* Hrg \* Hrt] where
    - |Nc] denotes a number of time credits
    - [Hla] denotes "cleaned up" items from the left hand side
    - [Hlw] denotes the [H1 \-* H2] and [Q1 \--* Q2] items from the left hand side
    - [Hlt] denotes the remaining items to process  items from the left hand side
    - [Hra] denotes "cleaned up" items from the right hand side
    - [Hrg] denotes the [\GC] and [\Top] items from the right hand side
    - [Hrt] denotes the remaining items to process from the right hand side

    Note: we assume that all items consist of iterated hstars, and are
    always terminated by an empty heap. *)

Definition Xsimpl (HL:credits*hprop*hprop*hprop) (HR:hprop*hprop*hprop) :=
  let '(Nc,Hla,Hlw,Hlt) := HL in
  let '(Hra,Hrg,Hrt) := HR in
  \$$Nc \* Hla \* Hlw\* Hlt ==> Hra \* Hrg \* Hrt.

(** [protect X] is use to prevent [xsimpl] from investigating inside [X] *)

Definition protect (A:Type) (X:A) : A := X.

(** Auxiliary lemmas to prove lemmas for [xsimpl] implementation. *)

Lemma Xsimpl_trans_l : forall Nc1 Hla1 Hlw1 Hlt1 Nc2 Hla2 Hlw2 Hlt2 HR,
  Xsimpl (Nc2,Hla2,Hlw2,Hlt2) HR ->
  \$$Nc1 \* Hla1 \* Hlw1 \* Hlt1 ==> \$$Nc2 \* Hla2 \* Hlw2 \* Hlt2 ->
  Xsimpl (Nc1,Hla1,Hlw1,Hlt1) HR.
Proof using.
  introv M1 E. destruct HR as [[Hra Hrg] Hrt]. unfolds Xsimpl.
  applys* himpl_trans M1.
Qed.

Lemma Xsimpl_trans_r : forall Hra1 Hrg1 Hrt1 Hra2 Hrg2 Hrt2 HL,
  Xsimpl HL (Hra2,Hrg2,Hrt2) ->
  Hra2 \* Hrg2 \* Hrt2 ==> Hra1 \* Hrg1 \* Hrt1 ->
  Xsimpl HL (Hra1,Hrg1,Hrt1).
Proof using.
  introv M1 E. destruct HL as [[[Nc1 Hln] Hlw] Hlt]. unfolds Xsimpl.
  applys* himpl_trans M1.
Qed.

Lemma Xsimpl_trans : forall Nc1 Hla1 Hlw1 Hlt1 Nc2 Hla2 Hlw2 Hlt2 Hra1 Hrg1 Hrt1 Hra2 Hrg2 Hrt2,
  Xsimpl (Nc2,Hla2,Hlw2,Hlt2) (Hra2,Hrg2,Hrt2) ->
  (\$$Nc2 \* Hla2 \* Hlw2 \* Hlt2 ==> Hra2 \* Hrg2 \* Hrt2 ->
   \$$Nc1 \* Hla1 \* Hlw1 \* Hlt1 ==> Hra1 \* Hrg1 \* Hrt1) ->
  Xsimpl (Nc1,Hla1,Hlw1,Hlt1) (Hra1,Hrg1,Hrt1).
Proof using. introv M1 E. unfolds Xsimpl. eauto. Qed.

(* DEPRECATED
Lemma Xsimpl_trans_l' : forall Hla1 Hlw1 Hlt1 Hla2 Hlw2 Hlt2 HR,
  (forall Hra Hrg Hrt,
    Xsimpl (Hla2,Hlw2,Hlt2) (Hra,Hrg,Hrt) ->
  Hla1 \* Hlw1 \* Hlt1 ==> Hla2 \* Hlw2 \* Hlt2 ->

[[Hla Hlw] Hlt]

  Xsimpl (Hla1,Hlw1,Hlt1) HR.
Proof using.
  introv M1 E. destruct HR as [[Hra Hrg] Hrt]. unfolds Xsimpl.
  applys* himpl_trans M1.
Qed.
*)

(* ---------------------------------------------------------------------- *)
(** ** Basic cancellation tactic used to establish lemmas used by [xsimpl] *)

Lemma hstars_simpl_start : forall H1 H2,
  H1 \* \[] ==> \[] \* H2 \* \[] ->
  H1 ==> H2.
Proof using. introv M. rew_heap~ in *. Qed.

Lemma hstars_simpl_keep : forall H1 Ha H Ht,
  H1 ==> (H \* Ha) \* Ht ->
  H1 ==> Ha \* H \* Ht.
Proof using. introv M. rew_heap in *. rewrite~ hstar_comm_assoc. Qed.

Lemma hstars_simpl_cancel : forall H1 Ha H Ht,
  H1 ==> Ha \* Ht ->
  H \* H1 ==> Ha \* H \* Ht.
Proof using. introv M. rewrite hstar_comm_assoc. applys~ himpl_frame_lr. Qed.

Lemma hstars_simpl_pick_lemma : forall H1 H1' H2,
  H1 = H1' ->
  H1' ==> H2 ->
  H1 ==> H2.
Proof using. introv M. subst~. Qed.

Ltac hstars_simpl_pick i :=
  (* Remark: the [hstars_pick_last] lemmas should never be needed here *)
  let L := hstars_pick_lemma i in
  eapply hstars_simpl_pick_lemma; [ apply L | ].

Ltac hstars_simpl_start tt :=
  match goal with |- ?H1 ==> ?H2 => idtac end;
  applys hstars_simpl_start;
  rew_heap_assoc.

Ltac hstars_simpl_step tt :=
  match goal with |- ?Hl ==> ?Ha \* ?H \* ?H2 =>
    first [
      hstars_search Hl ltac:(fun i H' =>
        match H' with H => hstars_simpl_pick i end);
      apply hstars_simpl_cancel
    | apply hstars_simpl_keep ]
  end.

Ltac hstars_simpl_post tt :=
  rew_heap; try apply himpl_refl.

Ltac hstars_simpl_core tt :=
  hstars_simpl_start tt;
  repeat (hstars_simpl_step tt);
  hstars_simpl_post tt.

Tactic Notation "hstars_simpl" :=
  hstars_simpl_core tt.


(* ---------------------------------------------------------------------- *)
(** ** Transition lemmas *)

(** Transition lemmas to start the process *)

Lemma xpull_protect : forall H1 H2,
  H1 ==> protect H2 ->
  H1 ==> H2.
Proof using. auto. Qed.

Lemma xsimpl_start : forall H1 H2,
  Xsimpl (0%cr, \[], \[], (H1 \* \[])) (\[], \[], (H2 \* \[])) ->
  H1 ==> H2.
Proof using. introv M. unfolds Xsimpl. rew_heap~ in *. Qed.
(* Note: [repeat rewrite hstar_assoc] after applying this lemma *)

(** Transition lemmas for LHS extraction operations *)

Ltac xsimpl_l_start M :=
  introv M;
  match goal with HR: hprop*hprop*hprop |- _ =>
    destruct HR as [[Hra Hrg] Hrt]; unfolds Xsimpl end.

Ltac xsimpl_l_start' M :=
  xsimpl_l_start M; applys himpl_trans (rm M); hstars_simpl.

Lemma xsimpl_l_hempty : forall Nc Hla Hlw Hlt HR,
  Xsimpl (Nc, Hla, Hlw, Hlt) HR ->
  Xsimpl (Nc, Hla, Hlw, (\[] \* Hlt)) HR.
Proof using. xsimpl_l_start' M. Qed.

Lemma xsimpl_l_hpure : forall P Nc Hla Hlw Hlt HR,
  (P -> Xsimpl (Nc, Hla, Hlw, Hlt) HR) ->
  Xsimpl (Nc, Hla, Hlw, (\[P] \* Hlt)) HR.
Proof using.
  xsimpl_l_start M. rewrite hstars_pick_4. applys* himpl_hstar_hpure_l.
Qed.

Lemma xsimpl_l_hexists : forall A (J:A->hprop) Nc Hla Hlw Hlt HR,
  (forall x, Xsimpl (Nc, Hla, Hlw, (J x \* Hlt)) HR) ->
  Xsimpl (Nc, Hla, Hlw, (hexists J \* Hlt)) HR.
Proof using.
  xsimpl_l_start M. rewrite hstars_pick_4. rewrite hstar_hexists.
  applys* himpl_hexists_l. intros. rewrite~ <- hstars_pick_4.
Qed.

Lemma xsimpl_l_acc_hwand : forall H Nc Hla Hlw Hlt HR,
  Xsimpl (Nc, Hla, (H \* Hlw), Hlt) HR ->
  Xsimpl (Nc, Hla, Hlw, (H \* Hlt)) HR.
Proof using. xsimpl_l_start' M. Qed.

Lemma xsimpl_l_hcredits : forall n Nc Hla Hlw Hlt HR,
  Xsimpl ((Nc+n)%cr, Hla, Hlw, Hlt) HR ->
  Xsimpl (Nc, Hla, Hlw, (\$$n \* Hlt)) HR.
Proof using. xsimpl_l_start' M. Qed.

Lemma xsimpl_l_acc_other : forall H Nc Hla Hlw Hlt HR,
  Xsimpl (Nc, (H \* Hla), Hlw, Hlt) HR ->
  Xsimpl (Nc, Hla, Hlw, (H \* Hlt)) HR.
Proof using. xsimpl_l_start' M. Qed.

(** Transition lemmas for LHS cancellation operations
    ---Hlt is meant to be empty there *)

Lemma xsimpl_l_cancel_hwand_hempty : forall H2 Nc Hla Hlw Hlt HR,
  Xsimpl (Nc, Hla, Hlw, (H2 \* Hlt)) HR ->
  Xsimpl (Nc, Hla, ((\[] \-* H2) \* Hlw), Hlt) HR.
Proof using. xsimpl_l_start' M. Qed.

Lemma xsimpl_l_hwand_hcredits : forall n H2 Nc Hla Hlw Hlt HR,
  Xsimpl ((Nc - n)%cr, Hla, Hlw, (H2 \* Hlt)) HR ->
  Xsimpl (Nc, Hla, ((\$$n \-* H2) \* Hlw), Hlt) HR.
Proof using.
  xsimpl_l_start' M. rewrite hwand_hcredits_l.
  asserts_rewrite (Nc - n = Nc + (-n)). field.
  rewrite hcredits_add. hstars_simpl.
Qed.

(* DEPRECATED
Lemma xsimpl_l_cancel_hwand : forall H1 H2 Hla Hlw Hlt HR,
  Xsimpl (Hla, Hlw, (H2 \* Hlt)) HR ->
  Xsimpl ((H1 \* Hla), ((H1 \-* H2) \* Hlw), Hlt) HR.
Proof using. xsimpl_l_start' M. applys hwand_cancel. Qed.

Lemma xsimpl_l_cancel_qwand : forall A (x:A) (Q1 Q2:A->hprop) Hla Hlw Hlt HR,
  Xsimpl (Hla, Hlw, (Q2 x \* Hlt)) HR ->
  Xsimpl ((Q1 x \* Hla), ((Q1 \--* Q2) \* Hlw), Hlt) HR.
Proof using.
  xsimpl_l_start' M. applys himpl_trans.
  applys himpl_frame_lr. applys qwand_specialize x.
  applys hwand_cancel.
Qed.
*)

Lemma xsimpl_l_cancel_hwand : forall H1 H2 Nc Hla Hlw Hlt HR,
  Xsimpl (Nc, \[], Hlw, (Hla \* H2 \* Hlt)) HR ->
  Xsimpl (Nc, (H1 \* Hla), ((H1 \-* H2) \* Hlw), Hlt) HR.
Proof using. xsimpl_l_start' M. applys~ hwand_cancel. Qed.

Lemma xsimpl_l_cancel_qwand : forall A (x:A) (Q1 Q2:A->hprop) Nc Hla Hlw Hlt HR,
  Xsimpl (Nc, \[], Hlw, (Hla \* Q2 x \* Hlt)) HR ->
  Xsimpl (Nc, (Q1 x \* Hla), ((Q1 \--* Q2) \* Hlw), Hlt) HR.
Proof using.
  xsimpl_l_start' M. rewrite hstar_comm. applys himpl_hstar_trans_l.
  applys qwand_specialize x. rewrite hstar_comm. applys hwand_cancel.
Qed.

Lemma xsimpl_l_keep_wand : forall H Nc Hla Hlw Hlt HR,
  Xsimpl (Nc, (H \* Hla), Hlw, Hlt) HR ->
  Xsimpl (Nc, Hla, (H \* Hlw), Hlt) HR.
Proof using. xsimpl_l_start' M. Qed.

Lemma xsimpl_l_hwand_reorder : forall H1 H1' H2 Nc Hla Hlw Hlt HR,
  H1 = H1' ->
  Xsimpl (Nc, Hla, ((H1' \-* H2) \* Hlw), Hlt) HR ->
  Xsimpl (Nc, Hla, ((H1 \-* H2) \* Hlw), Hlt) HR.
Proof using. intros. subst*. Qed.

Lemma xsimpl_l_cancel_hwand_hstar : forall H1 H2 H3 Nc Hla Hlw Hlt HR,
  Xsimpl (Nc, Hla, Hlw, ((H2 \-* H3) \* Hlt)) HR ->
  Xsimpl (Nc, (H1 \* Hla), (((H1 \* H2) \-* H3) \* Hlw), Hlt) HR.
Proof using.
  xsimpl_l_start' M. rewrite hwand_curry_eq. applys hwand_cancel.
Qed.

Lemma xsimpl_l_cancel_hwand_hstar_hempty : forall H2 H3 Nc Hla Hlw Hlt HR,
  Xsimpl (Nc, Hla, Hlw, ((H2 \-* H3) \* Hlt)) HR ->
  Xsimpl (Nc, Hla, (((\[] \* H2) \-* H3) \* Hlw), Hlt) HR.
Proof using. xsimpl_l_start' M. Qed.

(** Transition lemmas for RHS extraction operations *)

Ltac xsimpl_r_start M :=
  introv M;
  match goal with HL: credits*hprop*hprop*hprop |- _ =>
    destruct HL as [[[Nc Hla] Hlw] Hlt]; unfolds Xsimpl end.

Ltac xsimpl_r_start' M :=
  xsimpl_r_start M; applys himpl_trans (rm M); hstars_simpl.

Lemma xsimpl_r_hempty : forall Hra Hrg Hrt HL,
  Xsimpl HL (Hra, Hrg, Hrt) ->
  Xsimpl HL (Hra, Hrg, (\[] \* Hrt)).
Proof using. xsimpl_r_start' M. Qed.

Lemma xsimpl_r_hwand_same : forall H Hra Hrg Hrt HL,
  Xsimpl HL (Hra, Hrg, Hrt) ->
  Xsimpl HL (Hra, Hrg, ((H \-* H) \* Hrt)).
Proof using. xsimpl_r_start' M. rewrite hwand_equiv. rew_heap~. Qed.

Lemma xsimpl_r_hwand_hcredits : forall n H2 Nc Hla Hlw Hlt Hra Hrg Hrt,
  Xsimpl ((Nc + n)%cr, Hla, Hlw, Hlt) (Hra, Hrg, H2 \* Hrt) ->
  Xsimpl (Nc, Hla, Hlw, Hlt) (Hra, Hrg, ((\$$n \-* H2) \* Hrt)).
Proof using.
  introv M. unfolds Xsimpl. rewrite hwand_hcredits_l.
  asserts_rewrite (Nc = (Nc + n) + (- n)). field. rewrite hcredits_add.
  sets X: (Nc + n). hstars_simpl. hstars_simpl. auto.
Qed.

Lemma xsimpl_r_hpure : forall P Hra Hrg Hrt HL,
  P ->
  Xsimpl HL (Hra, Hrg, Hrt) ->
  Xsimpl HL (Hra, Hrg, (\[P] \* Hrt)).
Proof using.
  introv HP. xsimpl_r_start' M. applys* himpl_hempty_hpure.
Qed.

Lemma xsimpl_r_hcredits : forall n Nc Hla Hlw Hlt Hra Hrg Hrt,
  Xsimpl (Nc - n, Hla, Hlw, Hlt) (Hra, Hrg, Hrt) ->
  Xsimpl (Nc, Hla, Hlw, Hlt) (Hra, Hrg, (\$$n \* Hrt)).
Proof using.
  introv HP. unfolds Xsimpl. asserts_rewrite (Nc = (Nc - n) + n). field.
  rewrite hcredits_add. rew_heap. hstars_simpl. hstars_simpl. auto.
Qed.

Lemma xsimpl_r_hexists : forall A (x:A) (J:A->hprop) Hra Hrg Hrt HL,
  Xsimpl HL (Hra, Hrg, (J x \* Hrt)) ->
  Xsimpl HL (Hra, Hrg, (hexists J \* Hrt)).
Proof using. xsimpl_r_start' M. applys* himpl_hexists_r. Qed.

Lemma xsimpl_r_id : forall A (x X:A) Hra Hrg Hrt HL,
  (X = x) ->
  Xsimpl HL (Hra, Hrg, Hrt) ->
  Xsimpl HL (Hra, Hrg, (x ~> Id X \* Hrt)).
Proof using.
  introv ->. xsimpl_r_start' M. rewrite repr_id.
  applys* himpl_hempty_hpure.
Qed.

Lemma xsimpl_r_id_unify : forall A (x:A) Hra Hrg Hrt HL,
  Xsimpl HL (Hra, Hrg, Hrt) ->
  Xsimpl HL (Hra, Hrg, (x ~> Id x \* Hrt)).
Proof using. introv M. applys~ xsimpl_r_id. Qed.

Lemma xsimpl_r_keep : forall H Hra Hrg Hrt HL,
  Xsimpl HL ((H \* Hra), Hrg, Hrt) ->
  Xsimpl HL (Hra, Hrg, (H \* Hrt)).
Proof using. xsimpl_r_start' M. Qed.

(** Transition lemmas for [\Top] and [\GC] cancellation *)

  (* [H] meant to be [\GC] or [\Top] *)
Lemma xsimpl_r_hgc_or_htop : forall H Hra Hrg Hrt HL,
  Xsimpl HL (Hra, (H \* Hrg), Hrt) ->
  Xsimpl HL (Hra, Hrg, (H \* Hrt)).
Proof using. xsimpl_r_start' M. Qed.

Lemma xsimpl_r_htop_replace_hgc : forall Hra Hrg Hrt HL,
  Xsimpl HL (Hra, (\Top \* Hrg), Hrt) ->
  Xsimpl HL (Hra, (\GC \* Hrg), (\Top \* Hrt)).
Proof using. xsimpl_r_start' M. applys himpl_hgc_r. xaffine. Qed.

Lemma xsimpl_r_hgc_drop : forall Hra Hrg Hrt HL,
  Xsimpl HL (Hra, Hrg, Hrt) ->
  Xsimpl HL (Hra, Hrg, (\GC \* Hrt)).
Proof using. xsimpl_r_start' M. applys himpl_hgc_r. xaffine. Qed.

Lemma xsimpl_r_htop_drop : forall Hra Hrg Hrt HL,
  Xsimpl HL (Hra, Hrg, Hrt) ->
  Xsimpl HL (Hra, Hrg, (\Top \* Hrt)).
Proof using. xsimpl_r_start' M. applys himpl_htop_r. Qed.

(** Transition lemmas for LHS/RHS cancellation
    --- meant to be applied when Hlw and Hlt are empty *)

Ltac xsimpl_lr_start M :=
  introv M; unfolds Xsimpl; rew_heap in *.

Ltac xsimpl_lr_start' M :=
  xsimpl_lr_start M; hstars_simpl;
  try (applys himpl_trans (rm M); hstars_simpl).

Lemma xsimpl_lr_cancel_same : forall H Nc Hla Hlw Hlt Hra Hrg Hrt,
  Xsimpl (Nc, Hla, Hlw, Hlt) (Hra, Hrg, Hrt) ->
  Xsimpl (Nc, (H \* Hla), Hlw, Hlt) (Hra, Hrg, (H \* Hrt)).
Proof using. xsimpl_lr_start' M. Qed.

Lemma xsimpl_lr_cancel_htop : forall H Nc Hla Hlw Hlt Hra Hrg Hrt,
  Xsimpl (Nc, Hla, Hlw, Hlt) (Hra, (\Top \* Hrg), Hrt) ->
  Xsimpl (Nc, (H \* Hla), Hlw, Hlt) (Hra, (\Top \* Hrg), Hrt).
Proof using.
  xsimpl_lr_start M. rewrite <- hstar_assoc. rewrite (hstar_comm (\$$Nc)).
  rewrite hstar_assoc. rewrite <- (hstar_assoc Hra). rewrite (hstar_comm Hra).
  rewrite <- hstar_htop_htop. rew_heap. applys~ himpl_frame_lr.
  applys himpl_htop_r. rewrite <- (hstar_assoc \Top).
  rewrite (hstar_comm \Top). rew_heap*.
Qed. (* LATER: simplify *)

Lemma xsimpl_lr_cancel_hgc : forall Nc Hla Hlw Hlt Hra Hrg Hrt,
  Xsimpl (Nc, Hla, Hlw, Hlt) (Hra, (\GC \* Hrg), Hrt) ->
  Xsimpl (Nc, (\GC \* Hla), Hlw, Hlt) (Hra, (\GC \* Hrg), Hrt).
Proof using.
  xsimpl_lr_start M. rewrite <- hstar_assoc. rewrite (hstar_comm (\$$Nc)).
  rewrite hstar_assoc. rewrite <- (hstar_assoc Hra). rewrite (hstar_comm Hra).
  rewrite <- hstar_hgc_hgc at 2. rew_heap. applys~ himpl_frame_lr.
  rewrite <- (hstar_assoc \GC). rewrite (hstar_comm \GC). rewrite* hstar_assoc.
Qed. (* LATER: simplify *)

(* NOT NEEDED? *)
Lemma xsimpl_lr_cancel_eq : forall H1 H2 Nc Hla Hlw Hlt Hra Hrg Hrt,
  (H1 = H2) ->
  Xsimpl (Nc, Hla, Hlw, Hlt) (Hra, Hrg, Hrt) ->
  Xsimpl (Nc, (H1 \* Hla), Hlw, Hlt) (Hra, Hrg, (H2 \* Hrt)).
Proof using. introv ->. apply~ xsimpl_lr_cancel_same. Qed.

Lemma xsimpl_lr_cancel_eq_repr : forall A p (E1 E2:A->hprop) Nc Hla Hlw Hlt Hra Hrg Hrt,
  E1 = E2 ->
  Xsimpl (Nc, Hla, Hlw, Hlt) (Hra, Hrg, Hrt) ->
  Xsimpl (Nc, ((p ~> E1) \* Hla), Hlw, Hlt) (Hra, Hrg, ((p ~> E2) \* Hrt)).
Proof using. introv M. subst. apply~ xsimpl_lr_cancel_same. Qed.

Lemma xsimpl_lr_hwand : forall H1 H2 Nc Hla,
  Xsimpl (Nc, \[], \[], (H1 \* Hla)) (\[], \[], H2 \* \[]) ->
  Xsimpl (Nc, Hla, \[], \[]) ((H1 \-* H2) \* \[], \[], \[]).
Proof using.
  xsimpl_lr_start' M. rewrite hwand_equiv.
  applys himpl_trans (rm M). hstars_simpl.
Qed.

Lemma xsimpl_lr_hwand_hfalse : forall Hla H1 Nc,
  Xsimpl (Nc, Hla, \[], \[]) ((\[False] \-* H1) \* \[], \[], \[]).
Proof using. (* TODO: could be generalized in LHS *)
  intros. generalize True. xsimpl_lr_start M. rewrite hwand_equiv.
  applys himpl_hstar_hpure_l. auto_false.
Qed.

Lemma xsimpl_lr_qwand : forall A (Q1 Q2:A->hprop) Hla Nc,
  (forall x, Xsimpl (Nc, \[], \[], (Q1 x \* Hla)) (\[], \[], Q2 x \* \[])) ->
  Xsimpl (Nc, Hla, \[], \[]) ((Q1 \--* Q2) \* \[], \[], \[]).
Proof using.
  xsimpl_lr_start M. rewrite qwand_equiv. intros x.
  specializes M x. rew_heap~ in M. rewrite* hstar_comm_assoc.
Qed.

Lemma xsimpl_lr_qwand_unit : forall (Q1 Q2:unit->hprop) Hla Nc,
  Xsimpl (Nc, \[], \[], (Q1 tt \* Hla)) (\[], \[], (Q2 tt \* \[])) ->
  Xsimpl (Nc, Hla, \[], \[]) ((Q1 \--* Q2) \* \[], \[], \[]).
Proof using. introv M. applys xsimpl_lr_qwand. intros []. applys M. Qed.

Lemma xsimpl_lr_hforall : forall A (J:A->hprop) Hla Nc,
  (forall x, Xsimpl (Nc, \[], \[], Hla) (\[], \[], J x \* \[])) ->
  Xsimpl (Nc, Hla, \[], \[]) ((hforall J) \* \[], \[], \[]).
Proof using.
  xsimpl_lr_start M. applys himpl_hforall_r. intros x.
  specializes M x. rew_heap~ in M.
Qed.

Lemma xsimpl_lr_refl_nocredits : forall Hla,
  Xsimpl (0, Hla, \[], \[]) (Hla, \[], \[]).
Proof using. intros. unfolds Xsimpl. hstars_simpl. Qed.

Lemma xsimpl_lr_refl : forall Hla Nc,
  Xsimpl (Nc, Hla, \[], \[]) (\$$Nc \* Hla, \[], \[]).
Proof using. intros. unfolds Xsimpl. hstars_simpl. Qed.

(* NEEDED?
Lemma xsimpl_lr_refl_hempty_r : forall Hla,
  Xsimpl (Hla, \[], \[]) (Hla \* \[], \[], \[]).
Proof using. intros. unfolds Xsimpl. hstars_simpl. Qed.
*)

(* Lemma to instantiate [H ==> Q \--* ?Q'] *)
Lemma xsimpl_lr_qwand_unify : forall A (Q:A->hprop) Nc Hla,
  Xsimpl (Nc, Hla, \[], \[]) ((Q \--* (Q \*+ (\$$Nc \* Hla))) \* \[], \[], \[]).
Proof using. intros. unfolds Xsimpl. hstars_simpl. rewrite~ qwand_equiv. Qed.

(* Note that top makes no sense in a world with credits *)
Lemma xsimpl_lr_htop : forall Hla Hrg Nc, (* TODO: should keep only top *)
  Xsimpl (0, \[], \[], \[]) (\[], Hrg, \[]) ->
  Xsimpl (Nc, Hla, \[], \[]) (\[], (\Top \* Hrg), \[]).
Proof using.
  xsimpl_lr_start M. rewrite <- (hstar_hempty_l (\$$Nc \* Hla)).
  applys himpl_hstar_trans_l M. hstars_simpl. apply himpl_htop_r.
Qed.

(* optional
Lemma xsimpl_lr_hgc_hempty : forall Hla Hrg,
  Xsimpl (\[], \[], \[]) (\[], Hrg), \[]) ->
  Xsimpl (\[], \[], \[]) (\[], (\GC \* Hrg), \[]).
Proof using. apply haffine_hempty. Qed.
*)

Lemma xsimpl_lr_hgc : forall Nc Hla Hrg,
  Nc >= 0 -> (* TODO: use [use_credits] as tactics to avoid generating this *)
  haffine Hla ->
  Xsimpl (0, \[], \[], \[]) (\[], Hrg, \[]) ->
  Xsimpl (Nc, Hla, \[], \[]) (\[], (\GC \* Hrg), \[]).
Proof using.
  introv HNc N. xsimpl_lr_start M.
  rewrite <- hstar_hgc_hgc.
  applys himpl_hstar_trans_l \GC. { apply himpl_hgc_r. apply* haffine_hcredits. }
  hstars_simpl.
  rewrite <- (hstar_hempty_l Hla). applys himpl_hstar_trans_l M.
  hstars_simpl. apply* himpl_hgc_r.
Qed.

Lemma xsimpl_lr_hgc_nocredits : forall Hla Hrg,
  haffine Hla ->
  Xsimpl (0, \[], \[], \[]) (\[], Hrg, \[]) ->
  Xsimpl (0, Hla, \[], \[]) (\[], (\GC \* Hrg), \[]).
Proof using.
  introv N. xsimpl_lr_start M. rewrite <- (hstar_hempty_l Hla).
  applys himpl_hstar_trans_l M. hstars_simpl. apply* himpl_hgc_r.
Qed.

Lemma xsimpl_lr_exit_nogc_nocredits : forall Hla Hra,
  Hla ==> Hra ->
  Xsimpl (0, Hla, \[], \[]) (Hra, \[], \[]).
Proof using. introv M. unfolds Xsimpl. hstars_simpl. auto. Qed.

Lemma xsimpl_lr_exit_credits_to_hempty : forall Nc,
  Nc = 0 ->
  Xsimpl (Nc, \[], \[], \[]) (\[], \[], \[]).
Proof using. introv M. unfolds Xsimpl. subst. hstars_simpl. Qed.

Lemma xsimpl_lr_exit_nogc : forall Hla Hra Nc,
  \$$ Nc \* Hla ==> Hra ->
  Xsimpl (Nc, Hla, \[], \[]) (Hra, \[], \[]).
Proof using. introv M. unfolds Xsimpl. hstars_simpl. auto. Qed.

Lemma xsimpl_lr_exit_nocredits : forall Hla Hra Hrg,
  Hla ==> Hra \* Hrg ->
  Xsimpl (0, Hla, \[], \[]) (Hra, Hrg, \[]).
Proof using. introv M. unfolds Xsimpl. hstars_simpl. rewrite~ hstar_comm. Qed.

Lemma xsimpl_lr_exit : forall Hla Hra Hrg Nc,
  \$$Nc \* Hla ==> Hra \* Hrg ->
  Xsimpl (Nc, Hla, \[], \[]) (Hra, Hrg, \[]).
Proof using. introv M. unfolds Xsimpl. hstars_simpl. rewrite~ (hstar_comm Hrg). Qed.

(* Lemma to instantiate goals of the form [Hla ==> ?H \* \GC] *)
Lemma xsimpl_lr_exit_instantiate : forall Nc Hla,
  Xsimpl (Nc, Hla, \[], \[]) ((\$$Nc \* Hla) \* \[], \GC \* \[], \[]).
Proof using.
  intros. applys xsimpl_lr_exit. rew_heap.
  (* inlined proof of himpl_same_hstar_hgc_r *)
  rewrite (hstar_comm Hla).  rewrite <- (hstar_hempty_l Hla) at 1.
  do 2 applys* himpl_frame_lr. applys himpl_hgc_r. applys haffine_hempty.
Qed.

Lemma xsimpl_lr_exit_instantiate_nocredits : forall Hla,
  Xsimpl (0, Hla, \[], \[]) (Hla \* \[], \GC \* \[], \[]).
Proof using.
  intros. applys_eq xsimpl_lr_exit_instantiate.
  rewrite hcredits_zero. rew_heap*.
Qed.

(** Lemmas to flip accumulators back in place *)

Lemma xsimpl_flip_acc_l : forall Nc Hla Hra Hla' Hrg,
  Hla = Hla' ->
  Xsimpl (Nc, Hla', \[], \[]) (Hra, Hrg, \[]) ->
  Xsimpl (Nc, Hla, \[], \[]) (Hra, Hrg, \[]).
Proof using. introv E1 M. subst*. Qed.

Lemma xsimpl_flip_acc_r : forall Nc Hla Hra Hra' Hrg,
  Hra = Hra' ->
  Xsimpl (Nc, Hla, \[], \[]) (Hra', Hrg, \[]) ->
  Xsimpl (Nc, Hla, \[], \[]) (Hra, Hrg, \[]).
Proof using. introv E1 M. subst*. Qed.

Ltac xsimpl_flip_acc_l tt :=
  eapply xsimpl_flip_acc_l; [ hstars_flip tt | ].

Ltac xsimpl_flip_acc_r tt :=
  eapply xsimpl_flip_acc_r; [ hstars_flip tt | ].

Ltac xsimpl_flip_acc_lr tt :=
  xsimpl_flip_acc_l tt; xsimpl_flip_acc_r tt.

(* NOT NEEDED
Lemma xsimpl_lr_exit : forall Hla Hlw Hlt Hra Hrg Hrt,
  Hla \* Hlw \* Hlt ==> Hra \* Hrg \* Hrt ->
  Xsimpl (Hla, Hlw, Hlt) (Hra, Hrg, Hrt).
Proof using. auto. Qed.
*)

(* ---------------------------------------------------------------------- *)
(** ** Lemmas to pick the hypothesis to cancel *)

(** [xsimpl_pick i] applies to a goal of the form
    [Xsimpl (Nc, (H1 \* .. \* Hi \* .. \* Hn), Hlw, Hlt) HR] and turns it into
    [Xsimpl (Nc, (Hi \* H1 .. \* H{i-1} \* H{i+1} \* .. \* Hn), Hlw, Hlt) HR]. *)

Lemma xsimpl_pick_lemma : forall Hla1 Hla2 Nc Hlw Hlt HR,
  Hla1 = Hla2 ->
  Xsimpl (Nc, Hla2, Hlw, Hlt) HR ->
  Xsimpl (Nc, Hla1, Hlw, Hlt) HR.
Proof using. introv M. subst~. Qed.

Ltac xsimpl_pick i :=
  let L := hstars_pick_lemma i in
  eapply xsimpl_pick_lemma; [ apply L | ].

(** [xsimpl_pick_st f] applies to a goal of the form
    [Xsimpl (Nc, (H1 \* .. \* Hi \* .. \* Hn), Hlw, Hlt) HR] and turns it into
    [Xsimpl (Nc, (Hi \* H1 .. \* H{i-1} \* H{i+1} \* .. \* Hn), Hlw, Hlt) HR]
    for the first [i] such that [f Hi] returns [true]. *)

Ltac xsimpl_pick_st f :=
  match goal with |- Xsimpl (?Nc, ?Hla, ?Hlw, ?Hlt) ?HR =>
    hstars_search Hla ltac:(fun i H =>
      match f H with true => xsimpl_pick i end)
  end.

(** [xsimpl_pick_syntactically H] is a variant of the above that only
    checks for syntactic equality, not unifiability. *)

Ltac xsimpl_pick_syntactically H :=
  xsimpl_pick_st ltac:(fun H' =>
    match H' with H => constr:(true) end).

(** [xsimpl_pick_unifiable H] applies to a goal of the form
    [Xsimpl (Hla, Hlw, Hlt) HR], where [Hla] is of the form
    [H1 \* .. \* Hn \* \[]]. It searches for [H] among the [Hi].
    If it finds it, it moves this [Hi] to the front, just before [H1].
    Else, it fails. *)

Ltac xsimpl_pick_unifiable H :=
  match goal with |- Xsimpl (?Nc, ?Hla, ?Hlw, ?Hlt) ?HR =>
    hstars_search Hla ltac:(fun i H' =>
      unify H H'; xsimpl_pick i)
  end.

(** [xsimpl_pick_same H] is a choice for one of the above two,
    it is the default version used by [xsimpl].
    Syntactic matching is faster but less expressive. *)

Ltac xsimpl_pick_same H :=
  xsimpl_pick_unifiable H.

(** [xsimpl_pick_applied Q] applies to a goal of the form
    [Xsimpl (Nc, Hla, Hlw, Hlt) HR], where [Hla] is of the form
    [H1 \* .. \* Hn \* \[]]. It searches for [Q ?x] among the [Hi].
    If it finds it, it moves this [Hi] to the front, just before [H1].
    Else, it fails. *)

Ltac xsimpl_pick_applied Q :=
  xsimpl_pick_st ltac:(fun H' =>
    match H' with Q _ => constr:(true) end).

(** [repr_get_predicate H] applies to a [H] of the form [p ~> R _ ... _]
    and it returns [R]. *)

Ltac repr_get_predicate H :=
  match H with ?p ~> ?E => get_head E end.

(** [xsimpl_pick_repr H] applies to a goal of the form
    [Xsimpl (Nc, Hla, Hlw, Hlt) HR], where [Hla] is of the form
    [H1 \* .. \* Hn \* \[]], and where [H] is of the form [p ~> R _]
    (same as [repr _ p]). It searches for [p ~> R _] among the [Hi].
    If it finds it, it moves this [Hi] to the front, just before [H1].
    Else, it fails. *)

Ltac xsimpl_pick_repr H :=
  match H with ?p ~> ?E =>
    let R := get_head E in
    xsimpl_pick_st ltac:(fun H' =>
      match H' with (p ~> ?E') =>
        let R' := get_head E' in
        match R' with R => constr:(true) end end)
  end.


(* ---------------------------------------------------------------------- *)
(** ** Tactic start and stop *)

Opaque Xsimpl.

(** Handle [Q1 ===> Q2], in particular on [unit->hprop].
    Also handle [Q1 ===> ?Q2] and [H1 ==> ?H2] *)

Ltac xsimpl_handle_qimpl tt :=
  match goal with
  | |- @qimpl _ _ ?Q2 => is_evar Q2; apply qimpl_refl
  | |- @qimpl unit ?Q1 ?Q2 => let t := fresh "_tt" in intros t; destruct t
  | |- @qimpl _ _ _ => let r := fresh "r" in intros r
  | |- himpl _ ?H2 => is_evar H2; apply himpl_refl
  | |- himpl _ _ => idtac
  | |- @eq hprop _ _ => applys himpl_antisym
  | |- @eq (_ -> hprop) _ _ => applys fun_ext_1; applys himpl_antisym
  | _ => fail 1 "not a goal for xsimpl/xpull"
  end.

Ltac xsimpl_intro tt :=
  applys xsimpl_start.

Ltac xpull_start tt :=
  pose ltac_mark;
  intros;
  xsimpl_handle_qimpl tt;
  applys xpull_protect;
  xsimpl_intro tt.

Ltac xsimpl_start tt :=
  pose ltac_mark;
  intros;
  xsimpl_handle_qimpl tt;
  xsimpl_intro tt.

Ltac xsimpl_post_before_generalize tt :=
  idtac.

Ltac xsimpl_post_after_generalize tt :=
  idtac.

Ltac himpl_post_processing_for_hyp H :=
  idtac.

Ltac xsimpl_handle_false_subgoals tt :=
  tryfalse.

(* DEPRECATED
Ltac xsimpl_handle_haffine_subgoals tt :=
  match goal with |- haffine _ =>
    try solve [ xaffine ] end.
*)

Ltac xsimpl_clean tt :=
  try remove_empty_heaps_right tt;
  try remove_empty_heaps_left tt;
  try xsimpl_hint_remove tt;
  try xsimpl_beautify_credits_goal tt;
  try xsimpl_beautify_nonneg_and_eqzero_goal tt.

(* --LATER: might move to TLC *)
Ltac gen_until_mark_with_processing_and_cleaning cont :=
  match goal with H: ?T |- _ =>
  match T with
  | ltac_Mark => clear H
  | _ => cont H;
         let T := type of H in
         generalize H; clear H;
         (* discard non-dependent hyps that are not of type Prop *)
         try (match goal with |- _ -> _ =>
              match type of T with
              | Prop => idtac
              | _ => intros _
              end end);
         gen_until_mark_with_processing cont
  end end.

Ltac xsimpl_generalize tt :=
  xsimpl_post_before_generalize tt;
  xsimpl_handle_false_subgoals tt;
  gen_until_mark_with_processing_and_cleaning
    ltac:(himpl_post_processing_for_hyp);
  xsimpl_post_after_generalize tt.
  (* Note: was
     [gen_until_mark_with_processing
       ltac:(himpl_post_processing_for_hyp)]. *)

Ltac xsimpl_post tt :=
  xsimpl_clean tt;
  xsimpl_generalize tt.

Ltac xpull_post tt :=
  xsimpl_clean tt;
  unfold protect;
  xsimpl_generalize tt.


(* ---------------------------------------------------------------------- *)
(** ** Auxiliary functions step *)

(** [xsimpl_lr_cancel_eq_repr_post tt] is meant to simplify goals of the form [E1 = E2]
   that arises from cancelling [p ~> E1] with [p ~> E2] in the case where [E1] and [E2]
   share the same head symbol, that is, the same representation predicate [R]. *)

Ltac xsimpl_lr_cancel_eq_repr_post tt :=
  try fequal; try reflexivity.
  (* Later refined for records *)

(* DEPRECATED
  try solve
   [ reflexivity
   | fequal; fequal; first [ eassumption | symmetry; eassumption ] ];
      try match goal with |- repr ?X ?l = repr ?Y ?l => match constr:((X,Y)) with
      | (?F1 _, ?F1 _) => fequal; fequal
      | (?F1 ?F2 _, ?F1 ?F2 _) => fequal; fequal
      | (?F1 ?F2 ?F3 _, ?F1 ?F2 ?F3 _) => fequal; fequal
      | (?F1 ?F2 ?F3 ?F4 _, ?F1 ?F2 ?F3 ?F4 _) => fequal; fequal
      | (?F1 ?F2 ?F3 ?F4 ?F5 _, ?F1 ?F2 ?F3 ?F4 ?F5 _) => fequal; fequal
      | (?F1 ?F2 ?F3 ?F4 ?F5 ?F6 _, ?F1 ?F2 ?F3 ?F4 ?F5 ?F6 _) => fequal; fequal
      | (?F1 ?F2 ?F3 ?F4 ?F5 ?F6 ?F7 _, ?F1 ?F2 ?F3 ?F4 ?F5 ?F6 ?F7 _) => fequal; fequal
      | (?F1 ?F2 ?F3 ?F4 ?F5 ?F6 ?F7 ?F8 _, ?F1 ?F2 ?F3 ?F4 ?F5 ?F6 ?F7 ?F8 _) => fequal; fequal
      | (?F1 ?F2 ?F3 ?F4 ?F5 ?F6 ?F7 ?F8 ?F9 _, ?F1 ?F2 ?F3 ?F4 ?F5 ?F6 ?F7 ?F8 ?F9 _) => fequal; fequal
      end end.
*)

(** [xsimpl_r_hexists_apply tt] is a tactic to apply [xsimpl_r_hexists]
    by exploiting a hint if one is available (see the hint section above)
    to specify the instantiation of the existential. *)

(* Note: need to use [nrapply] instead of [eapply] to correctly handle [\exists (EA:Enc ?A)] *)
Ltac xsimpl_r_hexists_apply tt :=
  first [
    xsimpl_hint_next ltac:(fun x =>
      match x with
      | __ => nrapply xsimpl_r_hexists
      | _ => apply (@xsimpl_r_hexists _ x)
      end)
  | nrapply xsimpl_r_hexists ].

(** [xsimpl_hook H] can be customize to handle cancellation of specific
    kind of heap predicates (e.g., [hsingle]). *)

Ltac xsimpl_hook H := fail.


(* ---------------------------------------------------------------------- *)
(** ** Tactic step *)

Ltac xsimpl_hwand_hstars_l tt :=
  match goal with |- Xsimpl (?Nc, ?Hla, ((?H1s \-* ?H2) \* ?Hlw), \[]) ?HR =>
    hstars_search H1s ltac:(fun i H =>
      let L := hstars_pick_lemma i in
      eapply xsimpl_l_hwand_reorder;
      [ apply L
      | match H with
        | \[] => apply xsimpl_l_cancel_hwand_hstar_hempty
        | _ => xsimpl_pick_same H; apply xsimpl_l_cancel_hwand_hstar
        end
      ])
  end.

Ltac xsimpl_step_l tt :=
  match goal with |- Xsimpl ?HL ?HR =>
  match HL with
  | (?Nc, ?Hla, ?Hlw, (?H \* ?Hlt)) =>
    match H with
    | \[] => apply xsimpl_l_hempty
    | \[?P] => apply xsimpl_l_hpure; intro
    | \$$ ?n => apply xsimpl_l_hcredits
    | ?H1 \* ?H2 => rewrite (@hstar_assoc H1 H2)
    | hexists ?J => apply xsimpl_l_hexists; intro
    | ?H1 \-* ?H2 => apply xsimpl_l_acc_hwand
    | ?Q1 \--* ?Q2 => apply xsimpl_l_acc_hwand
    | _ => apply xsimpl_l_acc_other
    end
  | (?Nc, ?Hla, ((?H1 \-* ?H2) \* ?Hlw), \[]) =>
      match H1 with
      | \[] => apply xsimpl_l_cancel_hwand_hempty
      | \$$ ?n => apply xsimpl_l_hwand_hcredits
      | (_ \* _) => xsimpl_hwand_hstars_l tt
      | _ => first [ xsimpl_pick_same H1; apply xsimpl_l_cancel_hwand
                   | apply xsimpl_l_keep_wand ]
      end
  | (?Nc, ?Hla, ((?Q1 \--* ?Q2) \* ?Hlw), \[]) =>
      first [ xsimpl_pick_applied Q1; eapply xsimpl_l_cancel_qwand
            | apply xsimpl_l_keep_wand ]
  end end.

(* Limitation: [((Q1 \*+ H) \--* Q2) \* H] is not automatically
   simplified to [Q1 \--* Q2]. *)

Ltac xsimpl_hgc_or_htop_cancel cancel_item cancel_lemma :=
  (* match goal with |- Xsimpl (?Nc, ?Hla, \[], \[]) (?Hra, (?H \* ?Hrg), ?Hrt) => *)
  repeat (xsimpl_pick_same cancel_item; apply cancel_lemma).

Ltac xsimpl_hgc_or_htop_step tt :=
  match goal with |- Xsimpl (?Nc, ?Hla, \[], \[]) (?Hra, ?Hrg, (?H \* ?Hrt)) =>
    match constr:((Hrg,H)) with
    | (\[], \GC) => applys xsimpl_r_hgc_or_htop;
                    xsimpl_hgc_or_htop_cancel (\GC) xsimpl_lr_cancel_hgc
    | (\[], \Top) => applys xsimpl_r_hgc_or_htop;
                    xsimpl_hgc_or_htop_cancel (\GC) xsimpl_lr_cancel_htop;
                    xsimpl_hgc_or_htop_cancel (\Top) xsimpl_lr_cancel_htop
    | (\GC \* \[], \Top) => applys xsimpl_r_htop_replace_hgc;
                            xsimpl_hgc_or_htop_cancel (\Top) xsimpl_lr_cancel_htop
    | (\GC \* \[], \GC) => applys xsimpl_r_hgc_drop
    | (\Top \* \[], \GC) => applys xsimpl_r_hgc_drop
    | (\Top \* \[], \Top) => applys xsimpl_r_htop_drop
    end end.

Ltac xsimpl_cancel_same H :=
  xsimpl_pick_same H; apply xsimpl_lr_cancel_same.

Ltac xsimpl_step_r tt :=
  match goal with |- Xsimpl (?Nc, ?Hla, \[], \[]) (?Hra, ?Hrg, (?H \* ?Hrt)) =>
  match H with
  | ?H' => xsimpl_hook H (* else continue *)
  | \[] => apply xsimpl_r_hempty
  | \[?P] => apply xsimpl_r_hpure
  | \$$ ?n => apply xsimpl_r_hcredits
  | ?H1 \* ?H2 => rewrite (@hstar_assoc H1 H2)
  | ?H \-* ?H'eqH =>
      match H with
      | \[?P] => fail 1 (* don't cancel out cause [P] might contain a contradiction *)
      | \$$ ?n => (* simplify the [\$$n \-* H] to [$$\(-n) \* H] *)
        apply xsimpl_r_hwand_hcredits
      | _ => (* simplify the special case [H \-* H] *)
        match H'eqH with
        | H => apply xsimpl_r_hwand_same
        (* | protect H => apply xsimpl_r_hwand_same  --NOTE: purposely refuse to unify this*)
        end
      end
  | hexists ?J => xsimpl_r_hexists_apply tt
  | \GC => xsimpl_hgc_or_htop_step tt
  | \Top => xsimpl_hgc_or_htop_step tt
  | protect ?H' => apply xsimpl_r_keep
  | protect ?Q' _ => apply xsimpl_r_keep
  | ?H' => is_not_evar H;  xsimpl_cancel_same H (* else continue *)
  | ?p ~> _ => xsimpl_pick_repr H; apply xsimpl_lr_cancel_eq_repr;
               [ xsimpl_lr_cancel_eq_repr_post tt | ]  (* else continue *)
  | ?x ~> Id ?X => has_no_evar x; apply xsimpl_r_id
  (* --TODO DEPRECATED? | ?x ~> ?T _ => has_no_evar x;
                  let M := fresh in assert (M: T = Id); [ reflexivity | clear M ];
                  apply xsimpl_r_id; [ try reflexivity |  ] *)
  | ?x ~> ?T_evar ?X_evar => has_no_evar x; is_evar T_evar; is_evar X_evar;
                           apply xsimpl_r_id_unify
  | _ => apply xsimpl_r_keep
  end end.

(* [xsimpl_use_credits tt] should return [true] or [false]. *)
(* TODO: probably in fact we don't need this at all.
   if we see a credit, we can assume [xsimpl_use_credits] is true. *)

Ltac xsimpl_use_credits tt :=
  constr:(false).

Ltac xsimpl_step_lr tt :=
  match goal with |- Xsimpl (?Nc, ?Hla, \[], \[]) (?Hra, ?Hrg, \[]) =>
    match Hrg with
    | \[] =>
       match Hra with
       | ?H1 \* \[] =>
         match H1 with
         | ?Hra_evar => is_evar Hra_evar; (* handle [ H1 => ?H2 ] *)
            rew_heap;
            first [ apply xsimpl_lr_refl_nocredits
                  | apply xsimpl_lr_refl ]
            (* else continue *)
         | ?Q1 \--* ?Q2 => is_evar Q2; eapply xsimpl_lr_qwand_unify
         | \[False] \-* ?H2 => apply xsimpl_lr_hwand_hfalse
         | ?H1 \-* ?H2 => xsimpl_flip_acc_l tt; apply xsimpl_lr_hwand
         | ?Q1 \--* ?Q2 =>
             xsimpl_flip_acc_l tt;
             match H1 with
             | @qwand unit ?Q1' ?Q2' => apply xsimpl_lr_qwand_unit
             | _ => apply xsimpl_lr_qwand; intro
             end
         | hforall _ => xsimpl_flip_acc_l tt; apply xsimpl_lr_hforall; intro
                        (* --TODO: optimize for iterated \forall bindings *)
         end
       | \[] =>
          first [ apply xsimpl_lr_refl_nocredits (* handle [ \[] ==> \[] ] *)
                | apply xsimpl_lr_exit_credits_to_hempty; [ (*xsimpl_beautify_nonneg_and_eqzero_goal tt*) ] ] (* handle [ \$$n ==> \[] ] *)
       | _ => xsimpl_flip_acc_lr tt;
              first [ apply xsimpl_lr_exit_nogc_nocredits
                    | apply xsimpl_lr_exit_nogc ]
       end
    | (\Top \* _) => apply xsimpl_lr_htop
    | (\GC \* _) =>
        first
        [ match Hra with ?Hra1 \* \[] => is_evar Hra1;  (* when Hra1 is an evar *)
            first [ apply xsimpl_lr_exit_instantiate_nocredits
                  | apply xsimpl_lr_exit_instantiate ]
          end
        | (* General case, Hra not just reduced to an evar *)
          let xsimpl_xaffine tt := try remove_empty_heaps_haffine tt; xaffine in
          first [ apply xsimpl_lr_hgc_nocredits; [ xsimpl_xaffine tt | ]
                | apply xsimpl_lr_hgc; [ (*xsimpl_beautify_nonneg_and_eqzero_goal tt*) | xsimpl_xaffine tt | ] ]
        ]
    | ?Hrg' => xsimpl_flip_acc_lr tt;
               first [ apply xsimpl_lr_exit_nocredits
                     | apply xsimpl_lr_exit ]
  end end.

  (* --TODO: handle [?HL (?Hra_evar, (\GC \* ..), \[])] *)

Ltac xsimpl_step tt :=
  first [ xsimpl_step_l tt
        | xsimpl_step_r tt
        | xsimpl_step_lr tt ].


(* ---------------------------------------------------------------------- *)
(** ** Tactic notation *)

Ltac xpull_core tt :=
  xpull_start tt;
  repeat (xsimpl_step tt);
  xpull_post tt.

Tactic Notation "xpull" := xpull_core tt.
Tactic Notation "xpull" "~" := xpull; auto_tilde.
Tactic Notation "xpull" "*" := xpull; auto_star.

Ltac xsimpl_core tt :=
  xsimpl_start tt;
  repeat (xsimpl_step tt);
  xsimpl_post tt.

Tactic Notation "xsimpl" := xsimpl_core tt.
Tactic Notation "xsimpl" "~" := xsimpl; auto_tilde.
Tactic Notation "xsimpl" "*" := xsimpl; auto_star.

Tactic Notation "xsimpl" constr(L) :=
  match type of L with
  | list Boxer => xsimpl_hint_put L
  | _ => xsimpl_hint_put (boxer L :: nil)
  end; xsimpl.
Tactic Notation "xsimpl" constr(X1) constr(X2) :=
  xsimpl (>> X1 X2).
Tactic Notation "xsimpl" constr(X1) constr(X2) constr(X3) :=
  xsimpl (>> X1 X2 X3).

Tactic Notation "xsimpl" "~" constr(L) :=
  xsimpl L; auto_tilde.
Tactic Notation "xsimpl" "~" constr(X1) constr(X2) :=
  xsimpl X1 X2; auto_tilde.
Tactic Notation "xsimpl" "~" constr(X1) constr(X2) constr(X3) :=
  xsimpl X1 X2 X3; auto_tilde.

Tactic Notation "xsimpl" "*" constr(L) :=
  xsimpl L; auto_star.
Tactic Notation "xsimpl" "*" constr(X1) constr(X2) :=
  xsimpl X1 X2; auto_star.
Tactic Notation "xsimpl" "*" constr(X1) constr(X2) constr(X3) :=
  xsimpl X1 X2 X3; auto_star.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xchange] *)

(** [xchange] performs rewriting on the LHS of an entailment.
  Essentially, it applies to a goal of the form [H1 \* H2 ==> H3],
  and exploits an entailment [H1 ==> H1'] to replace the goal with
  [H1' \* H2 ==> H3].

  The tactic is actually a bit more flexible in two respects:
  - it does not force the LHS to be exactly of the form [H1 \* H2]
  - it takes as argument any lemma, whose instantiation result in
    a heap entailment of the form [H1 ==> H1'].

  Concretely, the tactic is just a wrapper around an application
  of the lemma called [xchange_lemma], which appears below.

  [xchanges] combines a call to [xchange] with calls to [xsimpl]
  on the subgoals. *)

Lemma xchange_lemma : forall H1 H2 H3 H4,
  H1 ==> H2 ->
  H3 ==> H1 \* (H2 \-* protect H4) ->
  H3 ==> H4.
Proof using.
  introv M1 M2. applys himpl_trans (rm M2).
  applys himpl_hstar_trans_l (rm M1). applys hwand_cancel.
Qed.

Ltac xchange_apply L :=
  eapply xchange_lemma; [ eapply L | ].

(* Below, the modifier is either [__] or [himpl_of_eq]
   or [himpl_of_eq_sym] *)

Ltac xchange_build_entailment modifier K :=
  match modifier with
  | __ =>
     match type of K with
     | _ = _ => constr:(@himpl_of_eq _ _ K)
     | _ => constr:(K)
     end
  | _ => constr:(@modifier _ _ K)
  end.

Ltac xchange_perform L modifier cont :=
  forwards_nounfold_then L ltac:(fun K =>
    let X := fresh "TEMP" in
    set (X := K); (* intermediate [set] seems necessary *)
    let M := xchange_build_entailment modifier K in
    clear X;
    xchange_apply M;
    cont tt).

Ltac xchange_core L modifier cont :=
  pose ltac_mark;
  intros;
  match goal with
  | |- _ ==> _ => idtac
  | |- _ ===> _ => let x := fresh "r" in intros x
  end;
  xchange_perform L modifier cont;
  gen_until_mark.

(** Error reporting support for [xchange] (not for [xchanges]) *)

Definition xchange_hidden (P:Type) (e:P) := e.

Notation "'__XCHANGE_FAILED_TO_MATCH_PRECONDITION__'" :=
  (@xchange_hidden _ _).

Ltac xchange_report_error tt :=
  match goal with |- context [?H1 \-* protect ?H2] =>
    change (H1 \-* protect H2) with (@xchange_hidden _ (H1 \-* protect H2)) end.

Ltac xchange_xpull_cont tt :=
  xsimpl; first
  [ xchange_report_error tt
  | unfold protect; try solve [ apply himpl_refl ] ].

Ltac xchange_xpull_cont_basic tt := (* version without error reporting *)
  xsimpl; unfold protect; try solve [ apply himpl_refl ].

Ltac xchange_xsimpl_cont tt :=
  unfold protect; xsimpl; try solve [ apply himpl_refl ].

Ltac xchange_nosimpl_base E modifier :=
  xchange_core E modifier ltac:(idcont).

Tactic Notation "xchange_nosimpl" constr(E) :=
  xchange_nosimpl_base E __.
Tactic Notation "xchange_nosimpl" "->" constr(E) :=
  xchange_nosimpl_base E himpl_of_eq.
Tactic Notation "xchange_nosimpl" "<-" constr(E) :=
  xchange_nosimpl_base E himpl_of_eq_sym.

Ltac xchange_base E modif :=
  xchange_core E modif ltac:(xchange_xpull_cont).

Tactic Notation "xchange" constr(E) :=
  xchange_base E __.
Tactic Notation "xchange" "~" constr(E) :=
  xchange E; auto_tilde.
Tactic Notation "xchange" "*" constr(E) :=
  xchange E; auto_star.

Tactic Notation "xchange" "->" constr(E) :=
  xchange_base E himpl_of_eq.
Tactic Notation "xchange"  "~" "->" constr(E) :=
  xchange -> E; auto_tilde.
Tactic Notation "xchange" "*" "->" constr(E) :=
  xchange -> E; auto_star.

Tactic Notation "xchange" "<-" constr(E) :=
  xchange_base E himpl_of_eq_sym.
Tactic Notation "xchange" "~" "<-" constr(E) :=
  xchange <- E; auto_tilde.
Tactic Notation "xchange" "*" "<-" constr(E) :=
  xchange <- E; auto_star.

Ltac xchanges_base E modif :=
  xchange_core E modif ltac:(xchange_xsimpl_cont).

Tactic Notation "xchanges" constr(E) :=
  xchanges_base E __.
Tactic Notation "xchanges" "~" constr(E) :=
  xchanges E; auto_tilde.
Tactic Notation "xchanges" "*" constr(E) :=
  xchanges E; auto_star.

Tactic Notation "xchanges" "->" constr(E) :=
  xchanges_base E himpl_of_eq.
Tactic Notation "xchanges"  "~" "->" constr(E) :=
  xchanges -> E; auto_tilde.
Tactic Notation "xchanges" "*" "->" constr(E) :=
  xchanges -> E; auto_star.

Tactic Notation "xchanges" "<-" constr(E) :=
  xchanges_base E himpl_of_eq_sym.
Tactic Notation "xchanges" "~" "<-" constr(E) :=
  xchanges <- E; auto_tilde.
Tactic Notation "xchanges" "*" "<-" constr(E) :=
  xchanges <- E; auto_star.

Tactic Notation "xchange" constr(E1) "," constr(E2) :=
  xchange E1; try xchange E2.
Tactic Notation "xchange" constr(E1) "," constr(E2) "," constr(E3) :=
  xchange E1; try xchange E2; try xchange E3.
Tactic Notation "xchange" constr(E1) "," constr(E2) "," constr(E3) "," constr(E4) :=
  xchange E1; try xchange E2; try xchange E3; try xchange E4.



(* ********************************************************************** *)
(** * Demos *)


(* ---------------------------------------------------------------------- *)
(** [rew_heap] demos *)

Lemma rew_heap_demo_with_evar : forall H1 H2 H3,
  (forall H, H1 \* (H \* H2) \* \[] = H3 -> True) -> True.
Proof using.
  introv M. dup 3.
  { eapply M. rewrite hstar_assoc. rewrite hstar_assoc. demo. }
  { eapply M. rew_heap_assoc. demo. }
  { eapply M. rew_heap. demo. }
Abort.


(* ---------------------------------------------------------------------- *)
(** [hstars] demos *)

Lemma hstars_flip_demo : forall H1 H2 H3 H4,
  (forall H, H1 \* H2 \* H3 \* H4 \* \[] = H -> H = H -> True) -> True.
Proof using.
  introv M. eapply M. hstars_flip tt.
Abort.

Lemma hstars_flip_demo_0 :
  (forall H, \[] = H -> H = H -> True) -> True.
Proof using.
  introv M. eapply M. hstars_flip tt.
Abort.


(* ---------------------------------------------------------------------- *)
(** [xsimpl_hint] demos *)

Lemma xsimpl_demo_hints : exists n, n = 3.
Proof using.
  xsimpl_hint_put (>> 3 true).
  xsimpl_hint_next ltac:(fun x => exists x).
  xsimpl_hint_remove tt.
Abort.


(* ---------------------------------------------------------------------- *)
(** [hstars_pick] demos *)

Lemma demo_hstars_pick_1 : forall H1 H2 H3 H4 Hresult,
  (forall H, H1 \* H2 \* H3 \* H4 = H -> H = Hresult -> True) -> True.
Proof using.
  introv M. dup 2.
  { eapply M. let L := hstars_pick_lemma 3 in eapply L. demo. }
  { eapply M. let L := hstars_pick_lemma (hstars_last 4) in eapply L. demo. }
Qed.


(* ---------------------------------------------------------------------- *)
(** [hstars_simpl] demos *)

Lemma demo_hstars_simpl_1 : forall H1 H2 H3 H4 H5,
  H2 ==> H5 ->
  H1 \* H2 \* H3 \* H4 ==> H4 \* H5 \* H3 \* H1.
Proof using.
  intros. dup.
  { hstars_simpl_start tt.
    hstars_simpl_step tt.
    hstars_simpl_step tt.
    hstars_simpl_step tt.
    hstars_simpl_step tt.
    hstars_simpl_post tt. auto. }
  { hstars_simpl. auto. }
Qed.

Lemma demo_hstars_simpl_2 : forall H1 H2 H3 H4 H5,
  (forall H, H \* H2 \* H3 \* H4 ==> H4 \* H5 \* H3 \* H1 -> True) -> True.
Proof using.
  introv M. eapply M. hstars_simpl.
Abort.


(* ---------------------------------------------------------------------- *)
(** [xsimpl_pick] demos *)

Lemma xsimpl_pick_demo : forall (Q:bool->hprop) (P:Prop) Nc H1 H2 H3 Hlw Hlt Hra Hrg Hrt,
  (forall HX HY,
    Xsimpl (Nc, (H1 \* H2 \* H3 \* Q true \* (\[P] \-* HX) \* HY \* \[]), Hlw, Hlt)
           (Hra, Hrg, Hrt)
  -> True) -> True.
Proof using.
  introv M. applys (rm M).
  let L := hstars_pick_lemma 2%nat in set (X:=L).
  eapply xsimpl_pick_lemma. apply X.
  xsimpl_pick 2%nat.
  xsimpl_pick_same H3.
  xsimpl_pick_applied Q.
  xsimpl_pick_same H2.
  xsimpl_pick_unifiable H3.
  xsimpl_pick_unifiable \[True].
  xsimpl_pick_unifiable (\[P] \-* H1).
Abort.


(* ---------------------------------------------------------------------- *)
(** [xpull] and [xsimpl] demos *)

Tactic Notation "xpull0" := xpull_start tt.
Tactic Notation "xsimpl0" := xsimpl_start tt.
Tactic Notation "xsimpl1" := xsimpl_step tt.
Tactic Notation "xsimpl2" := xsimpl_post tt.
Tactic Notation "xsimpll" := xsimpl_step_l tt.
Tactic Notation "xsimplr" := xsimpl_step_r tt.
Tactic Notation "xsimpllr" := xsimpl_step_lr tt.

Declare Scope xsimpl_scope.

Notation "'HSIMPL' Hla Hlw Hlt =====> Hra Hrg Hrt" := (Xsimpl (Hla, Hlw, Hlt) (Hra, Hrg, Hrt))
  (at level 69, Hla, Hlw, Hlt, Hra, Hrg, Hrt at level 0,
   format "'[v' 'HSIMPL' '/' Hla  '/' Hlw  '/' Hlt  '/' =====> '/' Hra  '/' Hrg  '/' Hrt ']'")
  : xsimpl_scope.

Local Open Scope xsimpl_scope.

Lemma xpull_demo : forall H1 H2 H3 H,
  (H1 \* \[] \* (H2 \* \exists (y z:int) (n:nat), \[y = (y + z + n)%Z]) \* H3) ==> H.
Proof using.
  dup.
  { intros. xpull0. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1.
    xsimpl1. xsimpl1. xsimpl2. demo. }
  { xpull. intros. demo. }
Abort.

Lemma xsimpl_demo_stars : forall H1 H2 H3 H4 H5,
  H1 \* H2 \* H3 \* H4 ==> H4 \* H3 \* H5 \* H2.
Proof using.
  dup 3.
  { xpull. demo. }
  { intros. xsimpl0. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1.
    xsimpl1. xsimpl1. xsimpl1. xsimpl1. demo. }
  { intros. xsimpl. demo. }
Abort. (* --TODO: coq bug, abort should be required, not qed allowed *)

Lemma xsimpl_demo_keep_order : forall H1 H2 H3 H4 H5 H6 H7,
  H1 \* H2 \* H3 \* H4 ==> H5 \* H3 \* H6 \* H7.
Proof using. intros. xsimpl. demo. Abort.

Lemma xsimpl_demo_stars_top : forall H1 H2 H3 H4 H5,
  H1 \* H2 \* H3 \* H4 \* H5 ==> H3 \* H1 \* H2 \* \Top.
Proof using.
  dup.
  { intros. xsimpl0. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1.
    xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1.
    xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. }
  { intros. xsimpl. }
Abort.

Lemma xsimpl_demo_hint : forall H1 (Q:int->hprop),
  Q 4 ==> Q 3 ->
  H1 \* Q 4 ==> \exists x, Q x \* H1.
Proof using.
  introv W. dup.
  { intros. xsimpl_hint_put (>> 3).
    xsimpl0. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1.
    xsimpl1. xsimpl1. xsimpl2. auto. }
  { xsimpl 3. auto. }
Qed.

Lemma xsimpl_demo_stars_gc : forall H1 H2,
  haffine H2 ->
  H1 \* H2 ==> H1 \* \GC.
Proof using.
  dup.
  { intros. xsimpl0. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1.
    xsimpl1. xsimpl1. xsimpl1. }
  { intros. xsimpl~. }
Abort.

Lemma xsimpl_demo_evar_1 : forall H1 H2,
  (forall H, H1 \* H2 ==> H -> True) -> True.
Proof using. intros. eapply H. xsimpl. Abort.

Lemma xsimpl_demo_evar_2 : forall H1,
  (forall H, H1 ==> H1 \* H -> True) -> True.
Proof using.
  introv M. dup.
  { eapply M. xsimpl0. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. }
  { eapply M. xsimpl~. }
Abort.

Lemma xsimpl_demo_htop_both_sides : forall H1 H2,
  H1 \* H2 \* \Top ==> H1 \* \Top.
Proof using.
  dup.
  { intros. xsimpl0. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1.
    xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. }
  { intros. xsimpl~. }
Abort.

Lemma xsimpl_demo_htop_multiple : forall H1 H2,
  H1 \* H2 \* \Top ==> H1 \* \Top \* \Top.
Proof using. intros. xsimpl~. Abort.

Lemma xsimpl_demo_hgc_multiple : forall H1 H2,
  haffine H2 ->
  H1 \* H2 \* \GC ==> H1 \* \GC \* \GC.
Proof using. intros. xsimpl~. Qed.

Lemma xsimpl_demo_hwand : forall H1 H2 H3 H4,
  (H1 \-* (H2 \-* H3)) \* H1 \* H4 ==> (H2 \-* (H3 \* H4)).
Proof using.
  dup.
  { intros. xsimpl0. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1.
    xsimpl1. xsimpl1. xsimpl1.
    xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1.
    xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1.
    xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. }
  { intros. xsimpl~. }
Qed.

Lemma xsimpl_demo_qwand : forall A (x:A) (Q1 Q2:A->hprop) H1,
  H1 \* (H1 \-* (Q1 \--* Q2)) \* (Q1 x) ==> (Q2 x).
Proof using. intros. xsimpl~. Qed.

Lemma xsimpl_demo_hwand_r : forall H1 H2 H3,
  H1 \* H2 ==> H1 \* (H3 \-* (H2 \* H3)).
Proof using. intros. xsimpl~. Qed.

Lemma xsimpl_demo_qwand_r : forall A (x:A) (Q1 Q2:A->hprop) H1 H2,
  H1 \* H2 ==> H1 \* (Q1 \--* (Q1 \*+ H2)).
Proof using. intros. xsimpl. Qed.

Lemma xsimpl_demo_hwand_multiple_1 : forall H1 H2 H3 H4 H5,
  H1 \-* H4 ==> H5 ->
  (H2 \* ((H1 \* H2 \* H3) \-* H4)) \* H3 ==> H5.
Proof using. introv M. xsimpl. auto. Qed.

Lemma xsimpl_demo_hwand_multiple_2 : forall H1 H2 H3 H4 H5,
  (H1 \* H2 \* ((H1 \* H3) \-* (H4 \-* H5))) \* (H2 \-* H3) \* H4 ==> H5.
Proof using. intros. xsimpl. Qed.

Lemma xsimpl_demo_hwand_hempty : forall H1 H2 H3,
  (\[] \-* H1) \* H2 ==> H3.
Proof using. intros. xsimpl. Abort.

Lemma xsimpl_demo_hwand_hstar_hempty : forall H0 H1 H2 H3,
  ((H0 \* \[]) \-* \[] \-* H1) \* H2 ==> H3.
Proof using. intros. xsimpl. rew_heap. Abort.
(* [xsimpl] does not simplify inner [\[] \-* H1], known limitation. *)

Lemma xsimpl_demo_hwand_iter : forall H1 H2 H3 H4 H5,
  H1 \* H2 \* ((H1 \* H3) \-* (H4 \-* H5)) \* H4 ==> ((H2 \-* H3) \-* H5).
Proof using.
  intros. dup.
  { xsimpl0. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1.
    xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1.
    xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1.
    xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1.
    xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. }
  { xsimpl. }
Qed.

Lemma xsimpl_demo_repr_1 : forall p q (R:int->int->hprop),
  p ~> R 3 \* q ~> R 4 ==> \exists n m, p ~> R n \* q ~> R m.
Proof using.
  intros. dup.
  { xsimpl0. xsimpl1. xsimpl1. xsimpl1. xsimpl1.
    xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. }
  { xsimpl~. }
Qed.

Lemma xsimpl_demo_repr_2 : forall p (R R':int->int->hprop),
  R = R' ->
  p ~> R' 3 ==> \exists n, p ~> R n.
Proof using. introv E. xsimpl. subst R'. xsimpl. Qed.

Lemma xsimpl_demo_repr_3 : forall p (R:int->int->hprop),
  let R' := R in
  p ~> R' 3 ==> \exists n, p ~> R n.
Proof using.
  intros. dup.
  { xsimpl0. xsimpl1. xsimpl1. xsimpl1. xsimpl1. }
  { xsimpl~. }
Qed.

Lemma xsimpl_demo_repr_4 : forall p n m (R:int->int->hprop),
  n = (m + 0)%Z ->
  p ~> R n ==> p ~> R m.
Proof using. intros. xsimpl. math. Qed.

(* NOTE: in the presence of [let R' := R], it is possible that R'
   is renamed into R during a call to [xsimpl], because
   [remove_empty_heaps_right tt] called from [xsimpl_clean tt]
   invokes [rewrite] which performs a matching upto unification,
   and not syntactically. *)

Lemma xsimpl_demo_gc_0 : forall H1 H2,
  H1 ==> H2 \* \GC \* \GC.
Proof using. intros. xsimpl. Abort.

Lemma xsimpl_demo_gc_1 : forall H1 H2,
  H1 ==> H2 \* \GC \* \Top \* \Top \* \GC.
Proof using.
  intros. dup.
  { xsimpl0. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1. xsimpl1.
    xsimpl1. xsimpl1. xsimpl1. xsimpl2. demo. }
  { xsimpl~. demo. }
Abort.

Lemma xsimpl_demo_gc_2 : forall H1 H2 H3,
  H1 \* H2 \* \Top \* \GC \* \Top ==> H3 \* \GC \* \GC.
Proof using. intros. xsimpl. Abort.
  (* Remark: no attempt to collapse [\Top] or [\GC] on the RHS is performed,
     they are dealt with only by cancellation from the LHS *)

Lemma xsimpl_demo_gc_3 : forall H1 H2,
  H1 \* H2 \* \GC \* \GC ==> H2 \* \GC \* \GC \* \GC.
Proof using. intros. xsimpl. xaffine. Abort.

Lemma xsimpl_demo_gc_4 : forall H1 H2,
  H1 \* H2 \* \GC  ==> H2 \* \GC \* \Top \* \Top \* \GC.
Proof using. intros. xsimpl. Abort.

Lemma xsimpl_demo_evar_gc : (forall H, \[] ==> (H \* \GC) -> True) -> True.
Proof using. introv M. eapply M. xsimpl. Qed.


(* ---------------------------------------------------------------------- *)
(** [xsimpl] with credits demos *)

(** Start using credits -- TODO: use new "local ltac rebind" feature *)
Ltac xsimpl_use_credits tt ::=
  constr:(true).

Lemma xsimpl_hcredits_gather : forall H1 H2 H3 H4 H5 n1 n2 n3 n4,
  H1 \* \$$n1 \* H2 \* H3 \* \$$n2 \* H4 ==> H4 \* H3 \* \$$n3 \* H5 \* \$$n4 \* H2.
Proof using. intros. xsimpl. Abort.

Lemma xsimpl_hcredits_gather : forall (n:Z),
  (n >= 0%Z)%C ->
  \[] ==> (\$(- n - 1) \* \GC) \* \$1.
Proof using. intros. xsimpl. auto. Abort.

Lemma xsimpl_hcredits_hwand : forall H1 H2 H3 H4 H5 n1 n2 n3 n4 n5,
  H1 \* \$$n1 \* H2 \* H3 \* (\$$n2 \-* H4) ==> H4 \* H3 \* (\$$n3 \-* \$$n4 \-* H5) \* \$$n5 \* H2.
Proof using. intros. xsimpl. Abort.
(* LATER: unclear whether we really want to simplify (\$$n2 \-* H4) by paying for it;
   is this done only when we wish to reveal what's behind the wand? *)

Lemma xsimpl_hcredits_hwand_eq_Z : forall (n:Z) H,
  ((\$n) \-* H) = (H \* (\$(- n)%Z)).
Proof using. intros. xsimpl. (* TODO: autorewrite to cleanup 0+ and 0- in Qc *)
Abort.

Lemma xsimpl_hcredits_hwand_eq : forall n H,
  ((\$$n) \-* H) = (H \* (\$$(- n)%Qc)).
Proof using. intros. xsimpl. ring. Abort.

Lemma xsimpl_hcredits_steps : forall (n1 n2 n3 : Qc),
  \$$ (n1 + n2)%cr ==> \$$ n3.
Proof using. intros. xsimpl. Abort.

Lemma xsimpl_hcredits_steps_Z : forall (n1 n2 n3 : Z),
  \$ (n1 + n2)%Z ==> \$ n3.
Proof using. intros. xsimpl. Abort.

Lemma xsimpl_hcredits_ring : forall (a b : Z),
  \$$ (Z2Qc ((a + b) ^ 2) - Z2Qc (a * a) - Z2Qc (b * b) - Z2Qc (2 * a * b))%cr ==> \[].
Proof using. intros. xsimpl. ring. Abort.

Lemma xsimpl_hcredits_ring2 : forall (a b : Z),
  \$$ (Z2Qc ((a + b) ^ 2) - Z2Qc (a * a) - Z2Qc (b * b) - Z2Qc (2 * a * b))%cr ==> \$$(0)%cr.
Proof using. intros. xsimpl. (* would need some processing before ring works *) Abort.

Lemma xsimpl_hcredits_ring3 : forall (a b : Z),
  \$$ (Z2Qc ((a + b) ^ 2))%cr ==> \$$(Z2Qc (a * a) + Z2Qc (b * b) + Z2Qc (2 * a * b))%cr.
Proof using. intros. xsimpl. ring. Abort.


(* TODO: add a demo with an hypothesis [M] with simplifiable credits in an entailment,
   do [dup 2].
   in the first branch, call [xsimpl_beautify_hcredits_everywhere tt]
   then [xchanges M].
   in the second branch, call [xsimpl_beautify_hcredits_everywhere tt] directly. *)

(* End using credits *)
Ltac xsimpl_use_credits tt ::=
  constr:(false).


(* ---------------------------------------------------------------------- *)
(** [xchange] demos *)

Lemma xchange_demo_1 : forall H1 H2 H3 H4 H5 H6,
  H1 ==> H2 \* H3 ->
  H1 \* H4 ==> (H5 \-* H6).
Proof using.
  introv M. dup 3.
  { xchange_nosimpl M. xsimpl. demo. }
  { xchange M. xsimpl. demo. }
  { xchanges M. demo. }
Qed.

Lemma xchange_demo_2 : forall A (Q:A->hprop) H1 H2 H3,
  H1 ==> \exists x, Q x \* (H2 \-* H3) ->
  H1 \* H2 ==> \exists x, Q x \* H3.
Proof using.
  introv M. dup 3.
  { xchange_nosimpl M. xsimpl. unfold protect. xsimpl. }
  { xchange M. xsimpl. }
  { xchanges M. }
Qed.

Lemma xchange_demo_4 : forall A (Q1 Q2:A->hprop) H,
  Q1 ===> Q2 ->
  Q1 \*+ H ===> Q2 \*+ H.
Proof using. introv M. xchanges M. Qed.

Lemma xsimpl_demo_hfalse : forall H1 H2,
  H1 ==> \[False] ->
  H1 \* H2 ==> \[False].
Proof using.
  introv M. dup.
  { xchange_nosimpl M. xsimpl0. xsimpl1. xsimpl1. xsimpl1.
    xsimpl1. xsimpl1. xsimpl1. xsimpl1. }
  { xchange M. }
Qed.

Lemma xchange_demo_hforall_l :
 forall (hforall_specialize : forall A (x:A) (J:A->hprop), (hforall J) ==> (J x)),
 forall (Q:int->hprop) H1,
  (\forall x, Q x) \* H1 ==> Q 2 \* \Top.
Proof using.
  intros. xchange (>> hforall_specialize 2). xsimpl.
Qed.

(* ---------------------------------------------------------------------- *)

End XsimplSetupCredits.


(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(** * Body of the functor with dummy credits *)

Module XsimplSetup (HP : XsimplParams).

(** Definition of the functor argument *)

Module Export HPC <: XsimplParamsCredits.

Include HP.

Open Scope heap_scope.

Definition use_credits : bool :=
  false.

Notation "'credits'" := Qcanon.Qc.
Local Open Scope Qc_scope.
Delimit Scope Qc with cr.

Definition hcredits (n:credits) : hprop :=
  \[].

Notation "'\$' n" := (hcredits (Z2Qc n))
  (at level 40,
   n at level 0,
   format "\$ n") : heap_scope.

Notation "'\$$' n" := (hcredits n)
  (at level 40,
   n at level 0,
   format "\$$  n") : heap_scope.

Open Scope heap_scope.

Lemma hcredits_skip :
  use_credits = false ->
  forall n, \$$ n = \[].
Proof using. auto. Qed.

Lemma hcredits_zero :
  \$$ 0 = \[].
Proof using. auto. Qed.

Lemma hcredits_add : forall (n m:credits),
  \$$ (n+m)%cr = \$$ n \* \$$ m.
Proof using. intros. unfold hcredits. rewrite* hstar_hempty_l. Qed.

Lemma haffine_hcredits : forall (n:credits),
  (n >= 0)%cr ->
  haffine (\$$ n).
Proof using. introv M. applys haffine_hempty. Qed.

Lemma hwand_hcredits_l : forall H (n:credits),
  (\$$n \-* H) = (\$$(-n)%cr \* H).
Proof using. intros. unfold hcredits. rewrite hwand_hempty_l. rewrite* hstar_hempty_l. Qed.

End HPC.

(** Instantiation *)

Module Export Setup := XsimplSetupCredits HPC.

End XsimplSetup.
