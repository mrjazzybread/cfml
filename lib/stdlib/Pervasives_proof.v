Set Implicit Arguments.
Require Import CFLib.
Require Import Pervasives_ml.
Generalizable Variable A.


(* TODO: add PRE/POST notation *)

(************************************************************)
(** Boolean *)

Lemma not_spec : forall (a:bool),
  TRIPLE (not a)
    PRE \[]
    POST \[= !a ].
Proof using.
  xcf. xgo*.
Qed.

Hint Extern 1 (RegisterSpec not) => Provide not_spec.


(************************************************************)
(** Physical equality *)

(** There are two specifications:
    - [==] at type [loc] implements comparison of locations
    - [==] in general, if it returns true, then implies logical equality.

    The first specification is used by default.
    Use [xapp_spec infix_eq_eq_gen_spec] for the latter.
*)

Parameter infix_eq_eq_loc_spec : forall (a b:loc),
  TRIPLE (infix_eq_eq__ a b)
    PRE \[]
    POST \[= isTrue (a = b) ].

Parameter infix_eq_eq_gen_spec : forall (A:Type) (a b:A),
  TRIPLE (infix_eq_eq__ a b)
    PRE \[]
    POST (fun r => \[r = true -> isTrue (a = b)]).

Hint Extern 1 (RegisterSpec infix_eq_eq__) => Provide infix_eq_eq_loc_spec.

Lemma infix_emark_eq_loc_spec : forall (a b:loc),
  TRIPLE (infix_emark_eq__ a b)
    PRE \[]
    POST \[= isTrue (a <> b) ].
Proof using.
  xcf. xgo*. rew_isTrue; xauto*.
Qed.

Lemma infix_emark_eq_gen_spec : forall (A:Type) (a b:A),
  TRIPLE (infix_emark_eq__ a b)
    PRE \[]
    POST (fun r => \[r = false -> isTrue (a = b)]).
Proof using.
  xcf. xapp_spec infix_eq_eq_gen_spec.
  introv E. xrets~.
Qed.

Hint Extern 1 (RegisterSpec infix_emark_eq__) => Provide infix_emark_eq_loc_spec.


(************************************************************)
(** Comparison *)

Parameter infix_eq_spec : forall A (a b : A),
  (polymorphic_eq_arg a \/ polymorphic_eq_arg b) ->
  TRIPLE (infix_eq__ a b)
    PRE \[]
    POST \[= isTrue (a = b) ].

Hint Extern 1 (RegisterSpec infix_eq__) => Provide infix_eq_spec.

Parameter infix_neq_spec : curried 2%nat infix_eq__ /\
  forall A (a b : A),
  (polymorphic_eq_arg a \/ polymorphic_eq_arg b) ->
  TRIPLE (infix_lt_gt__ a b)
    PRE \[]
    POST \[= isTrue (a <> b) ].

Hint Extern 1 (RegisterSpec infix_lt_gt__) => Provide infix_neq_spec.

Lemma min_spec : forall (n m:int),
  TRIPLE (min n m)
    PRE \[]
    POST \[= Z.min n m ].
Proof using.
  xcf. xgo*.
  { rewrite~ Z.min_l. }
  { rewrite~ Z.min_r. math. }
Qed.

Lemma max_spec : forall (n m:int),
  TRIPLE (max n m)
    PRE \[]
    POST \[= Z.max n m ].
Proof using.
  xcf. xgo*.
  { rewrite~ Z.max_l. }
  { rewrite~ Z.max_r. math. }
Qed.

Hint Extern 1 (RegisterSpec min) => Provide min_spec.
Hint Extern 1 (RegisterSpec max) => Provide max_spec.


(************************************************************)
(** Boolean *)

Parameter infix_bar_bar_spec : forall (a b:bool),
  TRIPLE (infix_bar_bar__ a b)
    PRE \[]
    POST \[= a && b ].

Parameter infix_amp_amp_spec : forall (a b:bool),
  TRIPLE (infix_amp_amp__ a b)
    PRE \[]
    POST \[= a || b ].

Hint Extern 1 (RegisterSpec infix_bar_bar__) => Provide infix_bar_bar_spec.
Hint Extern 1 (RegisterSpec infix_amp_amp__) => Provide infix_amp_amp_spec.


(************************************************************)
(** Integer *)

Parameter infix_tilde_minus_spec : forall (n:int),
  TRIPLE (infix_tilde_minus__ n)
    PRE \[]
    POST \[= Z.opp n ].

Parameter infix_plus_spec : forall (n m:int),
  TRIPLE (infix_plus__ n m)
    PRE \[]
    POST \[= Z.add n m ].

Parameter infix_minus_spec : forall (n m:int),
  TRIPLE (infix_minus__ n m)
    PRE \[]
    POST \[= Z.sub n m ].

Parameter infix_star_spec : forall (n m:int),
  TRIPLE (infix_star__ n m)
    PRE \[]
    POST \[= Z.mul n m ].

Parameter infix_slash_spec : forall (n m:int),
  m <> 0 ->
  TRIPLE (infix_slash__ n m)
    PRE \[]
    POST \[= Z.quot n m ].

Parameter mod_spec : forall (n m:int),
  m <> 0 ->
  TRIPLE (Pervasives_ml.mod n m)
    PRE \[]
    POST \[= Z.rem n m ].

Hint Extern 1 (RegisterSpec infix_tilde_minus__) => Provide infix_tilde_minus_spec.
Hint Extern 1 (RegisterSpec infix_plus__) => Provide infix_plus_spec.
Hint Extern 1 (RegisterSpec infix_minus__) => Provide infix_minus_spec.
Hint Extern 1 (RegisterSpec infix_star__) => Provide infix_star_spec.
Hint Extern 1 (RegisterSpec infix_slash__) => Provide infix_slash_spec.
Hint Extern 1 (RegisterSpec Pervasives_ml.mod) => Provide mod_spec.

Notation "x `/` y" := (Z.quot x y)
  (at level 69, right associativity) : charac.
Notation "x `mod` y" := (Z.rem x y)
  (at level 69, no associativity) : charac.
(* TODO: check levels for these notations *)


(* NOT NEEDED
Notation "`~- n" := (App infix_tilde_minus_ n;)
  (at level 69, no associativity) : app_scope.
Notation "n `+ m" := (App infix_plus_ n m;)
  (at level 69, no associativity) : app_scope.
Notation "n `+ m" := (App infix_minus_ n m;)
  (at level 69, no associativity) : app_scope.
Notation "n `+ m" := (App infix_star_ n m;)
  (at level 69, no associativity) : app_scope.
Notation "n `+ m" := (App infix_div_ n m;)
  (at level 69, no associativity) : app_scope.
Notation "n `+ m" := (App infix_mod_ n m;)
  (at level 69, no associativity) : app_scope.
 *)

Lemma succ_spec : forall (n:int),
  TRIPLE (succ n)
    PRE \[]
    POST \[= n+1 ].
Proof using.
  xcf. xgo*.
Qed.

Lemma pred_spec : forall (n:int),
  TRIPLE (pred n)
    PRE \[]
    POST \[= n-1 ].
Proof using.
  xcf. xgo*.
Qed.

Lemma abs_spec : forall (n:int),
  TRIPLE (Pervasives_ml.abs n)
    PRE \[]
    POST \[= Z.abs n ].
Proof using.
  xcf. xgo.
  { rewrite~ Z.abs_eq. }
  { rewrite~ Z.abs_neq. math. }
Qed.

Hint Extern 1 (RegisterSpec succ) => Provide succ_spec.
Hint Extern 1 (RegisterSpec pred) => Provide pred_spec.
Hint Extern 1 (RegisterSpec abs) => Provide abs_spec.


(************************************************************)
(** Bit-level Integer *)

(* TODO: check *)

Parameter land_spec : forall (n m:int),
  TRIPLE (land n m)
    PRE \[]
    POST \[= Z.land n m ].

Parameter lor_spec :  forall (n m:int),
  TRIPLE (lor n m)
    PRE \[]
    POST \[= Z.lor n m ].

Parameter lxor_spec : forall (n m:int),
  TRIPLE (lxor n m)
    PRE \[]
    POST \[= Z.lxor n m ].

Definition Zlnot (x : Z) : Z := -(x + 1).

Parameter lnot_spec : forall (n:int),
  TRIPLE (lnot n)
    PRE \[]
    POST \[= Zlnot n ].

Parameter lsl_spec : forall (n m:int),
  0 <= m ->   (* y < Sys.word_size -> *)
  TRIPLE (lsl n m)
    PRE \[]
    POST \[= Z.shiftl n m ].

  (* TODO We temporarily? restrict [lsr] to nonnegative integers,
     so it behaves like [asr]. Anyway, [lsr] really operates
     on unsigned integers, and this notion is missing in CFML. *)

Parameter lsr_spec : forall (n m:int),
  0 <= n ->
  0 <= m ->
  (* m < Sys.word_size -> *)
  TRIPLE (lsr n m)
    PRE \[]
    POST \[= Z.shiftr n m ].

Parameter asr_spec : forall (n m:int),
  0 <= m ->
  (* m < Sys.word_size -> *)
  TRIPLE (asr n m)
    PRE \[]
    POST \[= Z.shiftr n m ].

Hint Extern 1 (RegisterSpec land) => Provide land_spec.
Hint Extern 1 (RegisterSpec lor) => Provide lor_spec.
Hint Extern 1 (RegisterSpec lxor) => Provide lxor_spec.
Hint Extern 1 (RegisterSpec lnot) => Provide lnot_spec.
Hint Extern 1 (RegisterSpec lsl) => Provide lsl_spec.
Hint Extern 1 (RegisterSpec land) => Provide land_spec.
Hint Extern 1 (RegisterSpec lsr) => Provide lsr_spec.
Hint Extern 1 (RegisterSpec asr) => Provide asr_spec.


(************************************************************)
(** References *)

Definition Ref {A} (v:A) (r:loc) :=
  r ~> `{ contents' := v }.

(* TODO: THIS IS NOW REALIZED AT A LOWER LEVEL *)
...
Axiom Ref_Heapdata : forall A,
  (Heapdata (@Ref A)).

Existing Instance Ref_Heapdata.
(* TODO: need an axiom about allocated records *)
(*
Proof using.
  intros. applys Heapdata_prove. intros x X1 X2.
  xunfold @Ref.
lets: star_is_single_same_loc.
  hchange (@star_is_single_same_loc x). hsimpl.
Qed.
*)

Notation "r '~~>' v" := (hdata (Ref v) r)
  (at level 32, no associativity) : heap_scope.

Lemma haffine_Ref : forall A r (v: A),
  haffine (r ~~> v).
Proof. intros. unfold Ref, hdata. affine. Qed.

Hint Resolve haffine_Ref : haffine.

(* Expose that [ref_ A] (defined in Pervasives_ml) is defined as [loc] *)
Hint Transparent ref_ : haffine.

Lemma ref_spec : forall A (v:A),
  TRIPLE (ref v)
    PRE \[]
    POST (fun r => r ~~> v).
Proof using. xcf_go~. Qed.

Lemma infix_emark_spec : forall A (v:A) r,
  TRIPLE (infix_emark__ r)
    INV (r ~~> v)
    POST \[= v].
Proof using. xunfold @Ref. xcf_go~. Qed.

Lemma infix_colon_eq_spec : forall A (v w:A) r,
  TRIPLE (infix_colon_eq__ r w)
    PRE (r ~~> v)
    POSTUNIT (r ~~> w).
Proof using. xunfold @Ref. xcf_go~. Qed.

Hint Extern 1 (RegisterSpec ref) => Provide ref_spec.
Hint Extern 1 (RegisterSpec infix_emark__) => Provide infix_emark_spec.
Hint Extern 1 (RegisterSpec infix_colon_eq__) => Provide infix_colon_eq_spec.

.. TODO ALREADY DEFINED ELSEWHERE
Notation "'App'' `! r" := (App infix_emark__ r;)
  (at level 69, no associativity, r at level 0,
   format "'App''  `! r") : charac.

Notation "'App'' r `:= x" := (App infix_colon_eq__ r x;)
  (at level 69, no associativity, r at level 0,
   format "'App''  r  `:=  x") : charac.

Lemma incr_spec : forall (n:int) r,
  TRIPLE (incr r)
    PRE (r ~~> n)
    POST (# r ~~> (n+1)).
Proof using. xcf_go~. Qed.

Lemma decr_spec : forall (n:int) r,
  TRIPLE (decr r)
    PRE (r ~~> n)
    POST (# r ~~> (n-1)).
Proof using. xcf_go~. Qed.

Hint Extern 1 (RegisterSpec incr) => Provide incr_spec.
Hint Extern 1 (RegisterSpec decr) => Provide decr_spec.



(************************************************************)
(** Group of References -- TODO: needs hfold_fmap

Axiom ref_spec_group : forall A (M:map loc A) (v:A),
  TRIPLE (Pervasives_ml.ref v)
    PRE (Group Ref M)
    POST (fun (r:loc) => Group Ref (M[r:=v]) \* \[r \notindom M]).
(* TODO: proof *)

Lemma infix_emark_spec_group : forall `{Inhab A} (M:map loc A) r,
  r \indom M ->
  TRIPLE (Pervasives_ml.infix_emark__ r)
    INV (Group Ref M)
    POST (fun x => \[x = M[r]]).
Proof using.
  intros. rewrite~ (Group_rem r M). xapp. xsimpl~.
Qed.

Lemma infix_colon_eq_spec_group : forall `{Inhab A} (M:map loc A) (v:A) r,
  r \indom M ->
  TRIPLE (Pervasives_ml.infix_colon_eq__ r v)
    PRE (Group Ref M)
    POSTUNIT (Group Ref (M[r:=v])).
Proof using.
  intros. rewrite~ (Group_rem r M). xapp. intros tt.
  hchanges~ (Group_add' r M).
Qed.

*)


(************************************************************)
(** Pairs *)

Lemma fst_spec : forall A B (x:A) (y:B),
  TRIPLE (fst (x,y))
    PRE \[]
    POST \[= x].
Proof using. xcf_go~. Qed.

Lemma snd_spec : forall A B (x:A) (y:B),
  TRIPLE (snd (x,y))
    PRE \[]
    POST \[= y].
Proof using. xcf_go~. Qed.

Hint Extern 1 (RegisterSpec fst) => Provide fst_spec.
Hint Extern 1 (RegisterSpec snd) => Provide snd_spec.


(************************************************************)
(** Unit *)

Lemma ignore_spec :
  TRIPLE (ignore tt)
    PRE \[]
    POST \[= tt].
Proof using. xcf_go~. Qed.

Hint Extern 1 (RegisterSpec ignore) => Provide ignore_spec.


(************************************************************)
(** Float *)

(* LATER: float operations *)





(************************************************************)
(************************************************************)
(************************************************************)
(* FUTURE

  (*------------------------------------------------------------------*)

  (** Pred / Succ *)

  Definition pred (n:int) := (Coq.ZArith.BinInt.Z.sub n 1).

  Definition succ (n:int) := (Coq.ZArith.BinInt.Z.add n 1).

  (** Ignore *)

  Definition ignore A (x:A) := tt.
  Definition char := Ascii.ascii.



  (*------------------------------------------------------------------*)
  (* ** References *)

  Definition Ref a A (T:htype A a) (V:A) (r:loc) :=
    Hexists v, heap_is_single r v \* v ~> T V.

  Instance Ref_Heapdata : forall a A (T:htype A a),
    (Heapdata (@Ref a A T)).
  Proof using.
    intros. applys Heapdata_prove. intros x X1 X2.
    unfold Ref. hdata_simpl. hextract as x1 x2.
    hchange (@star_is_single_same_loc x). hsimpl.
  Qed.

  Open Local Scope heap_scope_advanced.

  Notation "'~~>' v" := (~> Ref (@Id _) v)
    (at level 32, no associativity) : heap_scope_advanced.

  (*
  Notation "l '~~>' v" := (r ~> Ref (@Id _) v)
    (at level 32, no associativity) : heap_scope.
  *)
  Notation "l '~~>' v" := (hdata (@Ref _ _ (@Id _) v) r)
    (at level 32, no associativity) : heap_scope.

  Lemma focus_ref : forall (r:loc) a A (T:htype A a) V,
    r ~> Ref T V ==> Hexists v, r ~~> v \* v ~> T V.
  Proof. intros. unfold Ref, hdata. unfold Id. hsimpl~. Qed.

  Lemma unfocus_ref : forall (r:loc) a (v:a) A (T:htype A a) V,
    r ~~> v \* v ~> T V ==> r ~> Ref T V.
  Proof. intros. unfold Ref. hdata_simpl. hsimpl. subst~. Qed.

  Lemma heap_is_single_impl_null : forall (r:loc) A (v:A),
    heap_is_single r v ==> heap_is_single r v \* \[r <> null].
  Proof.
    intros. intros h Hh. forwards*: heap_is_single_null. exists___*.
  Qed.

  Lemma focus_ref_null : forall a A (T:htype A a) V,
    null ~> Ref T V ==> \[False].
  Proof.
    intros. unfold Ref, hdata. hextract as v.
    hchanges (@heap_is_single_impl_null null).
  Qed.

  Global Opaque Ref.
  Implicit Arguments focus_ref [a A].
  Implicit Arguments unfocus_ref [a A].

*)


