Set Implicit Arguments.

Require Import gospelstdlib_verified.

Require Coq.ZArith.BinInt TLC.LibLogic TLC.LibRelation TLC.LibInt TLC.LibListZ.

Require Import CFML.SepBase CFML.SepLifted CFML.WPLib CFML.WPLifted CFML.WPRecord CFML.WPArray CFML.WPBuiltin.

Require CFML.Stdlib.Array_ml CFML.Stdlib.List_ml CFML.Stdlib.Sys_ml.

Require Import Coq.ZArith.BinIntDef CFML.Semantics CFML.WPHeader.

Delimit Scope Z_scope with Z.

Parameter sequence : Type -> Type.

Parameter bag : Type -> Type.

Parameter set : Type -> Type.

Parameter map : Type -> Type -> Type.

Parameter succ : Z -> Z.

Parameter pred : Z -> Z.

Parameter neg : Z -> Z.

Parameter plus : Z -> Z -> Z.

Parameter minus : Z -> Z -> Z.

Parameter mult : Z -> Z -> Z.

Parameter div : Z -> Z -> Z.

Parameter _mod : Z -> Z -> Z.

Parameter pow : Z -> Z -> Z.

Parameter abs : Z -> Z.

Parameter min : Z -> Z -> Z.

Parameter max : Z -> Z -> Z.

Parameter gt : Z -> Z -> Prop.

Parameter ge : Z -> Z -> Prop.

Parameter lt : Z -> Z -> Prop.

Parameter le : Z -> Z -> Prop.

Parameter integer_of_int : int -> Z.

Parameter to_seq :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  array a -> sequence a.

Parameter of_list :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  list a -> sequence a.

Parameter max_int : Z.

Parameter min_int : Z.

Parameter app :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  sequence a -> sequence a -> sequence a.

Parameter seq_get :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  sequence a -> Z -> a.

Parameter seq_sub :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  sequence a -> Z -> Z -> sequence a.

Parameter seq_sub_l :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  sequence a -> Z -> sequence a.

Parameter seq_sub_r :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  sequence a -> Z -> sequence a.

Parameter monoid :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  (a -> a -> a) -> a -> Prop.

Axiom monoid_def :
  forall {a59 : Type},
  forall {Ih_a59 : Inhab a59},
  forall f : a59 -> a59 -> a59,
  forall neutral : a59,
  Coq.Init.Logic.iff (monoid f neutral) (
    Coq.Init.Logic.and (
      forall x : a59,
      Coq.Init.Logic.and (eq (f neutral x) (f x neutral)) (eq (f x neutral) x)
    ) (
      forall x : a59,
      forall y : a59,
      forall z : a59,
      eq (f x (f y z)) (f (f x y) z)
    )
  ).

Parameter comm_monoid :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  (a -> a -> a) -> a -> Prop.

Axiom comm_monoid_def :
  forall {a70 : Type},
  forall {Ih_a70 : Inhab a70},
  forall f : a70 -> a70 -> a70,
  forall neutral : a70,
  Coq.Init.Logic.iff (comm_monoid f neutral) (
    Coq.Init.Logic.and (monoid f neutral) (
      forall x : a70,
      forall y : a70,
      eq (f x y) (f y x)
    )
  ).

Module Sequence.

Parameter t : Type -> Type.

Parameter length :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  sequence a -> Z.

Parameter in_range :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  sequence a -> Z -> Prop.

Axiom in_range_def :
  forall {a74 : Type},
  forall {Ih_a74 : Inhab a74},
  forall s : sequence a74,
  forall i : Z,
  Coq.Init.Logic.iff (in_range s i) (
    Coq.Init.Logic.and (le (0)%Z i) (lt i (length s))
  ).

Axiom length_nonneg :
  forall {a76 : Type},
  forall {Ih_a76 : Inhab a76},
  forall s : sequence a76,
  le (0)%Z (length s).

Axiom subseq_l :
  forall {a82 : Type},
  forall {Ih_a82 : Inhab a82},
  forall s : sequence a82,
  forall i : Z,
  in_range s i -> eq (seq_sub_l s i) (seq_sub s i (length s)).

Axiom subseq_r :
  forall {a88 : Type},
  forall {Ih_a88 : Inhab a88},
  forall s : sequence a88,
  forall i : Z,
  in_range s i -> eq (seq_sub_r s i) (seq_sub s (0)%Z i).

Axiom subseq :
  forall {a98 : Type},
  forall {Ih_a98 : Inhab a98},
  forall s : sequence a98,
  forall i : Z,
  forall i1 : Z,
  forall i2 : Z,
  Coq.Init.Logic.and (le (0)%Z i1) (
    Coq.Init.Logic.and (le i1 i) (
      Coq.Init.Logic.and (lt i i2) (le i2 (length s))
    )
  ) ->
  eq (seq_get s i) (seq_get (seq_sub s i1 i2) (minus i i1)).

Axiom subseq_len :
  forall {a104 : Type},
  forall {Ih_a104 : Inhab a104},
  forall s : sequence a104,
  forall i1 : Z,
  forall i2 : Z,
  Coq.Init.Logic.and (le (0)%Z i1) (
    Coq.Init.Logic.and (le i1 i2) (lt i2 (length s))
  ) ->
  eq (length (seq_sub s i1 i2)) (minus i2 i1).

Parameter empty :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  sequence a.

Axiom empty_length :
  forall {a107 : Type},
  forall {Ih_a107 : Inhab a107},
  eq (length (@empty a107 Ih_a107)) (0)%Z.

Parameter init :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  Z -> (Z -> a) -> sequence a.

Axiom init_length :
  forall {a112 : Type},
  forall {Ih_a112 : Inhab a112},
  forall n : Z,
  forall f : Z -> a112,
  ge n (0)%Z -> eq (length (init n f)) n.

Axiom init_elems :
  forall {a120 : Type},
  forall {Ih_a120 : Inhab a120},
  forall n : Z,
  forall f : Z -> a120,
  forall i : Z,
  Coq.Init.Logic.and (le (0)%Z i) (lt i n) ->
  eq (seq_get (init n f) i) (f i).

Parameter singleton :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  a -> sequence a.

Axiom singleton_def :
  forall {a126 : Type},
  forall {Ih_a126 : Inhab a126},
  forall x : a126,
  forall f : Z -> a126,
  eq (f (0)%Z) x -> eq (singleton x) (init (1)%Z f).

Parameter cons :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  a -> sequence a -> sequence a.

Axiom cons_def :
  forall {a132 : Type},
  forall {Ih_a132 : Inhab a132},
  forall x : a132,
  forall s : sequence a132,
  eq (cons x s) (app (singleton x) s).

Parameter snoc :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  sequence a -> a -> sequence a.

Axiom snoc_def :
  forall {a138 : Type},
  forall {Ih_a138 : Inhab a138},
  forall s : sequence a138,
  forall x : a138,
  eq (snoc s x) (app s (singleton x)).

Parameter hd :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  sequence a -> a.

Axiom hd_def :
  forall {a143 : Type},
  forall {Ih_a143 : Inhab a143},
  forall s : sequence a143,
  eq (hd s) (seq_get s (0)%Z).

Parameter tl :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  sequence a -> sequence a.

Axiom tl_def :
  forall {a146 : Type},
  forall {Ih_a146 : Inhab a146},
  forall s : sequence a146,
  eq (tl s) (seq_sub_l s (1)%Z).

Parameter append :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  sequence a -> sequence a -> sequence a.

Axiom append_def :
  forall {a151 : Type},
  forall {Ih_a151 : Inhab a151},
  forall s1 : sequence a151,
  forall s2 : sequence a151,
  eq (append s1 s2) (app s1 s2).

Axiom append_length :
  forall {a158 : Type},
  forall {Ih_a158 : Inhab a158},
  forall s : sequence a158,
  forall s' : sequence a158,
  eq (length (app s s')) (plus (length s) (length s')).

Axiom append_elems_left :
  forall {a167 : Type},
  forall {Ih_a167 : Inhab a167},
  forall s : sequence a167,
  forall s' : sequence a167,
  forall i : Z,
  in_range s i -> eq (seq_get (app s s') i) (seq_get s i).

Axiom append_elems_right :
  forall {a178 : Type},
  forall {Ih_a178 : Inhab a178},
  forall s : sequence a178,
  forall s' : sequence a178,
  forall i : Z,
  Coq.Init.Logic.and (le (length s) i) (
    lt i (plus (length s) (length s'))
  ) ->
  eq (seq_get (app s s') i) (seq_get s' (minus i (length s))).

Parameter multiplicity :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  a -> sequence a -> Z.

Axiom mult_empty :
  forall {a181 : Type},
  forall {Ih_a181 : Inhab a181},
  forall x : a181,
  eq (multiplicity x (@empty a181 Ih_a181)) (0)%Z.

Axiom mult_cons :
  forall {a187 : Type},
  forall {Ih_a187 : Inhab a187},
  forall s : sequence a187,
  forall x : a187,
  eq (plus (1)%Z (multiplicity x s)) (multiplicity x (cons x s)).

Axiom mult_cons_neutral :
  forall {a195 : Type},
  forall {Ih_a195 : Inhab a195},
  forall s : sequence a195,
  forall x1 : a195,
  forall x2 : a195,
  Coq.Init.Logic.not (eq x1 x2) ->
  eq (multiplicity x1 s) (multiplicity x1 (cons x2 s)).

Axiom mult_length :
  forall {a200 : Type},
  forall {Ih_a200 : Inhab a200},
  forall x : a200,
  forall s : sequence a200,
  Coq.Init.Logic.and (le (0)%Z (multiplicity x s)) (
    le (multiplicity x s) (length s)
  ).

Parameter mem :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  a -> sequence a -> Prop.

Axiom mem_def :
  forall {a204 : Type},
  forall {Ih_a204 : Inhab a204},
  forall s : sequence a204,
  forall x : a204,
  Coq.Init.Logic.iff (mem x s) (gt (multiplicity x s) (0)%Z).

Parameter _forall :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  (a -> Prop) -> sequence a -> Prop.

Axiom forall_def :
  forall {a209 : Type},
  forall {Ih_a209 : Inhab a209},
  forall p : a209 -> bool,
  forall s : sequence a209,
  Coq.Init.Logic.iff (_forall p s) (forall x : a209, mem x s -> p x).

Parameter _exists :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  (a -> Prop) -> sequence a -> Prop.

Axiom _exists_def :
  forall {a215 : Type},
  forall {Ih_a215 : Inhab a215},
  forall p : a215 -> bool,
  forall s : sequence a215,
  Coq.Init.Logic.iff (_exists p s) (
    Coq.Init.Logic.ex (fun x : a215 => Coq.Init.Logic.and (mem x s) (p x))
  ).

Parameter map :
  forall {a : Type},
  forall {b : Type},
  forall {Ih_a : Inhab a},
  forall {Ih_b : Inhab b},
  (a -> b) -> sequence a -> sequence b.

Axiom map_elems :
  forall {a224 : Type},
  forall {a226 : Type},
  forall {Ih_a224 : Inhab a224},
  forall {Ih_a226 : Inhab a226},
  forall i : Z,
  forall f : a224 -> a226,
  forall s : sequence a224,
  in_range s i -> eq (seq_get (map f s) i) (f (seq_get s i)).

Parameter filter :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  (a -> Prop) -> sequence a -> sequence a.

Axiom filter_elems :
  forall {a233 : Type},
  forall {Ih_a233 : Inhab a233},
  forall f : a233 -> bool,
  forall s : sequence a233,
  forall x : a233,
  mem x s -> f x -> mem x (filter f s).

Parameter filter_map :
  forall {a : Type},
  forall {b : Type},
  forall {Ih_a : Inhab a},
  forall {Ih_b : Inhab b},
  (a -> option b) -> sequence a -> sequence b.

Axiom filter_map_elems :
  forall {a243 : Type},
  forall {a244 : Type},
  forall {Ih_a243 : Inhab a243},
  forall {Ih_a244 : Inhab a244},
  forall f : a243 -> option a244,
  forall s : sequence a243,
  forall y : a244,
  Coq.Init.Logic.iff (
    Coq.Init.Logic.ex (
      fun x : a243 =>
      Coq.Init.Logic.and (eq (f x) (Some y)) (mem x s)
    )
  ) (mem y (filter_map f s)).

Parameter get :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  sequence a -> Z -> a.

Axiom get_def :
  forall {a249 : Type},
  forall {Ih_a249 : Inhab a249},
  forall s : sequence a249,
  forall i : Z,
  eq (get s i) (seq_get s i).

Parameter set :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  sequence a -> Z -> a -> sequence a.

Axiom set_elem :
  forall {a256 : Type},
  forall {Ih_a256 : Inhab a256},
  forall s : sequence a256,
  forall i : Z,
  forall x : a256,
  in_range s i -> eq (seq_get (set s i x) i) x.

Axiom set_elem_other :
  forall {a267 : Type},
  forall {Ih_a267 : Inhab a267},
  forall s : sequence a267,
  forall i1 : Z,
  forall i2 : Z,
  forall x : a267,
  Coq.Init.Logic.not (eq i1 i2) ->
  in_range s i1 ->
  in_range s i2 -> eq (seq_get (set s i1 x) i2) (seq_get s i2).

Parameter rev :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  sequence a -> sequence a.

Axiom rev_length :
  forall {a271 : Type},
  forall {Ih_a271 : Inhab a271},
  forall s : sequence a271,
  eq (length s) (length (rev s)).

Axiom rev_elems :
  forall {a280 : Type},
  forall {Ih_a280 : Inhab a280},
  forall i : Z,
  forall s : sequence a280,
  in_range s i ->
  eq (seq_get (rev s) i) (seq_get s (minus (minus (length s) (1)%Z) i)).

Axiom extensionality :
  forall {a290 : Type},
  forall {Ih_a290 : Inhab a290},
  forall s1 : sequence a290,
  forall s2 : sequence a290,
  eq (length s1) (length s2) ->
  (forall i : Z, in_range s1 i -> eq (seq_get s1 i) (seq_get s2 i)) ->
  eq s1 s2.

Parameter fold_left :
  forall {a : Type},
  forall {b : Type},
  forall {Ih_a : Inhab a},
  forall {Ih_b : Inhab b},
  (a -> b -> a) -> a -> sequence b -> a.

Axiom fold_left_empty :
  forall {a296 : Type},
  forall {a297 : Type},
  forall {Ih_a296 : Inhab a296},
  forall {Ih_a297 : Inhab a297},
  forall f : a297 -> a296 -> a297,
  forall acc : a297,
  eq (fold_left f acc (@empty a296 Ih_a296)) acc.

Axiom fold_left_cons :
  forall {a308 : Type},
  forall {a309 : Type},
  forall {Ih_a308 : Inhab a308},
  forall {Ih_a309 : Inhab a309},
  forall f : a309 -> a308 -> a309,
  forall acc : a309,
  forall x : a308,
  forall l : sequence a308,
  eq (fold_left f acc (cons x l)) (fold_left f (f acc x) l).

Parameter fold_right :
  forall {a : Type},
  forall {b : Type},
  forall {Ih_a : Inhab a},
  forall {Ih_b : Inhab b},
  (a -> b -> b) -> sequence a -> b -> b.

Axiom fold_right_empty :
  forall {a314 : Type},
  forall {a315 : Type},
  forall {Ih_a314 : Inhab a314},
  forall {Ih_a315 : Inhab a315},
  forall acc : a315,
  forall f : a314 -> a315 -> a315,
  eq (fold_right f (@empty a314 Ih_a314) acc) acc.

Axiom fold_right_cons :
  forall {a325 : Type},
  forall {a327 : Type},
  forall {Ih_a325 : Inhab a325},
  forall {Ih_a327 : Inhab a327},
  forall acc : a327,
  forall f : a325 -> a327 -> a327,
  forall x : a325,
  forall l : sequence a325,
  eq (fold_right f (cons x l) acc) (f x (fold_right f l acc)).

Parameter permut :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  sequence a -> sequence a -> Prop.

Axiom permut_mem :
  forall {a333 : Type},
  forall {Ih_a333 : Inhab a333},
  forall s1 : sequence a333,
  forall s2 : sequence a333,
  permut s1 s2 ->
  (forall x : a333, Coq.Init.Logic.iff (mem x s1) (mem x s2)).

Parameter permut_sub :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  sequence a -> sequence a -> Z -> Z -> Prop.

Axiom permut_sub_def :
  forall {a347 : Type},
  forall {Ih_a347 : Inhab a347},
  forall s1 : sequence a347,
  forall s2 : sequence a347,
  forall i : Z,
  forall j : Z,
  permut (seq_sub s1 i j) (seq_sub s2 i j) ->
  eq (seq_sub_r s1 i) (seq_sub_r s2 i) ->
  eq (seq_sub_l s1 j) (seq_sub_l s2 j) -> permut_sub s1 s2 i j.

End Sequence.

Module Bag.

Parameter t : Type -> Type.

Parameter multiplicity :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  a -> bag a -> Z.

Axiom well_formed :
  forall {a350 : Type},
  forall {Ih_a350 : Inhab a350},
  forall b : bag a350,
  forall x : a350,
  ge (multiplicity x b) (0)%Z.

Parameter empty : forall {a : Type}, forall {Ih_a : Inhab a}, bag a.

Axiom empty_mult :
  forall {a353 : Type},
  forall {Ih_a353 : Inhab a353},
  forall x : a353,
  eq (multiplicity x (@empty a353 Ih_a353)) (0)%Z.

Parameter init :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  (a -> Z) -> bag a.

Axiom init_axiom :
  forall {a359 : Type},
  forall {Ih_a359 : Inhab a359},
  forall f : a359 -> Z,
  forall x : a359,
  eq (max (0)%Z (f x)) (multiplicity x (init f)).

Parameter mem :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  a -> bag a -> Prop.

Axiom mem_def :
  forall {a364 : Type},
  forall {Ih_a364 : Inhab a364},
  forall x : a364,
  forall b : bag a364,
  Coq.Init.Logic.iff (mem x b) (gt (multiplicity x b) (0)%Z).

Parameter add :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  a -> bag a -> bag a.

Axiom add_mult_x :
  forall {a369 : Type},
  forall {Ih_a369 : Inhab a369},
  forall b : bag a369,
  forall x : a369,
  eq (multiplicity x (add x b)) (plus (1)%Z (multiplicity x b)).

Axiom add_mult_neg_x :
  forall {a377 : Type},
  forall {Ih_a377 : Inhab a377},
  forall x : a377,
  forall y : a377,
  forall b : bag a377,
  Coq.Init.Logic.not (eq x y) ->
  eq (multiplicity y (add x b)) (multiplicity y b).

Parameter singleton :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  a -> bag a.

Axiom singleton_def :
  forall {a382 : Type},
  forall {Ih_a382 : Inhab a382},
  forall x : a382,
  eq (singleton x) (add x (@empty a382 Ih_a382)).

Parameter remove :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  a -> bag a -> bag a.

Axiom remove_mult_x :
  forall {a388 : Type},
  forall {Ih_a388 : Inhab a388},
  forall b : bag a388,
  forall x : a388,
  eq (multiplicity x (remove x b)) (
    max (0)%Z (minus (multiplicity x b) (1)%Z)
  ).

Axiom remove_mult_neg_x :
  forall {a396 : Type},
  forall {Ih_a396 : Inhab a396},
  forall x : a396,
  forall y : a396,
  forall b : bag a396,
  Coq.Init.Logic.not (eq x y) ->
  eq (multiplicity y (remove x b)) (multiplicity y b).

Parameter union :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  bag a -> bag a -> bag a.

Axiom union_all :
  forall {a404 : Type},
  forall {Ih_a404 : Inhab a404},
  forall b : bag a404,
  forall b' : bag a404,
  forall x : a404,
  eq (max (multiplicity x b) (multiplicity x b')) (
    multiplicity x (union b b')
  ).

Parameter sum :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  bag a -> bag a -> bag a.

Axiom sum_all :
  forall {a412 : Type},
  forall {Ih_a412 : Inhab a412},
  forall b : bag a412,
  forall b' : bag a412,
  forall x : a412,
  eq (plus (multiplicity x b) (multiplicity x b')) (
    multiplicity x (sum b b')
  ).

Parameter inter :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  bag a -> bag a -> bag a.

Axiom inter_all :
  forall {a420 : Type},
  forall {Ih_a420 : Inhab a420},
  forall b : bag a420,
  forall b' : bag a420,
  forall x : a420,
  eq (min (multiplicity x b) (multiplicity x b')) (
    multiplicity x (inter b b')
  ).

Parameter disjoint :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  bag a -> bag a -> Prop.

Axiom disjoint_def :
  forall {a427 : Type},
  forall {Ih_a427 : Inhab a427},
  forall b : bag a427,
  forall b' : bag a427,
  Coq.Init.Logic.iff (disjoint b b') (
    forall x : a427,
    mem x b -> Coq.Init.Logic.not (mem x b')
  ).

Parameter diff :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  bag a -> bag a -> bag a.

Axiom diff_all :
  forall {a434 : Type},
  forall {Ih_a434 : Inhab a434},
  forall b : bag a434,
  forall b' : bag a434,
  forall x : a434,
  eq (max (0)%Z (minus (multiplicity x b) (multiplicity x b'))) (
    multiplicity x (diff b b')
  ).

Parameter subset :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  bag a -> bag a -> Prop.

Axiom subset_def :
  forall {a441 : Type},
  forall {Ih_a441 : Inhab a441},
  forall b : bag a441,
  forall b' : bag a441,
  Coq.Init.Logic.iff (subset b b') (
    forall x : a441,
    le (multiplicity x b) (multiplicity x b')
  ).

Parameter filter :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  (a -> Prop) -> bag a -> bag a.

Axiom filter_mem :
  forall {a448 : Type},
  forall {Ih_a448 : Inhab a448},
  forall b : bag a448,
  forall x : a448,
  forall f : a448 -> bool,
  f x -> eq (multiplicity x (filter f b)) (multiplicity x b).

Axiom filter_mem_neg :
  forall {a455 : Type},
  forall {Ih_a455 : Inhab a455},
  forall b : bag a455,
  forall x : a455,
  forall f : a455 -> bool,
  Coq.Init.Logic.not (f x) -> eq (multiplicity x (filter f b)) (0)%Z.

Parameter cardinal :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  bag a -> Z.

Parameter finite :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  bag a -> Prop.

Axiom finite_def :
  forall {a462 : Type},
  forall {Ih_a462 : Inhab a462},
  forall b : bag a462,
  Coq.Init.Logic.iff (finite b) (
    Coq.Init.Logic.ex (
      fun s : sequence a462 =>
      forall x : a462,
      mem x b -> mem x s
    )
  ).

Axiom card_nonneg :
  forall {a464 : Type},
  forall {Ih_a464 : Inhab a464},
  forall b : bag a464,
  ge (cardinal b) (0)%Z.

Axiom card_empty :
  forall {a466 : Type},
  forall {Ih_a466 : Inhab a466},
  eq (cardinal (@empty a466 Ih_a466)) (0)%Z.

Axiom card_singleton :
  forall {a470 : Type},
  forall {Ih_a470 : Inhab a470},
  forall x : a470,
  eq (cardinal (singleton x)) (1)%Z.

Axiom card_union :
  forall {a479 : Type},
  forall {Ih_a479 : Inhab a479},
  forall b1 : bag a479,
  forall b2 : bag a479,
  finite b1 ->
  finite b2 ->
  eq (cardinal (union b1 b2)) (plus (cardinal b1) (cardinal b2)).

Axiom card_add :
  forall {a486 : Type},
  forall {Ih_a486 : Inhab a486},
  forall x : a486,
  forall b : bag a486,
  finite b -> eq (cardinal (add x b)) (plus (cardinal b) (1)%Z).

Axiom card_map :
  forall {a493 : Type},
  forall {Ih_a493 : Inhab a493},
  forall f : a493 -> bool,
  forall b : bag a493,
  finite b -> le (cardinal (filter f b)) (cardinal b).

Parameter of_seq :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  sequence a -> bag a.

Axiom of_seq_multiplicity :
  forall {a498 : Type},
  forall {Ih_a498 : Inhab a498},
  forall s : sequence a498,
  forall x : a498,
  eq (multiplicity x s) (multiplicity x (of_seq s)).

End Bag.

Parameter set_create :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  set a.

Module _Set.

Parameter t : Type -> Type.

Parameter empty : forall {a : Type}, forall {Ih_a : Inhab a}, set a.

Parameter mem :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  a -> set a -> Prop.

Axiom empty_mem :
  forall {a502 : Type},
  forall {Ih_a502 : Inhab a502},
  forall x : a502,
  Coq.Init.Logic.not (mem x (@empty a502 Ih_a502)).

Parameter add :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  a -> set a -> set a.

Axiom add_mem :
  forall {a506 : Type},
  forall {Ih_a506 : Inhab a506},
  forall s : set a506,
  forall x : a506,
  mem x (add x s).

Axiom add_mem_neq :
  forall {a513 : Type},
  forall {Ih_a513 : Inhab a513},
  forall s : set a513,
  forall x : a513,
  forall y : a513,
  Coq.Init.Logic.not (eq x y) ->
  Coq.Init.Logic.iff (mem x s) (mem x (add y s)).

Parameter singleton :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  a -> set a.

Parameter remove :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  a -> set a -> set a.

Axiom remove_mem :
  forall {a517 : Type},
  forall {Ih_a517 : Inhab a517},
  forall s : set a517,
  forall x : a517,
  Coq.Init.Logic.not (mem x (remove x s)).

Axiom remove_mem_neq :
  forall {a524 : Type},
  forall {Ih_a524 : Inhab a524},
  forall s : set a524,
  forall x : a524,
  forall y : a524,
  Coq.Init.Logic.not (eq x y) ->
  Coq.Init.Logic.iff (mem x s) (mem x (remove y s)).

Parameter union :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  set a -> set a -> set a.

Axiom union_mem :
  forall {a531 : Type},
  forall {Ih_a531 : Inhab a531},
  forall s : set a531,
  forall s' : set a531,
  forall x : a531,
  Coq.Init.Logic.or (mem x s) (mem x s') -> mem x (union s s').

Axiom union_mem_neg :
  forall {a538 : Type},
  forall {Ih_a538 : Inhab a538},
  forall s : set a538,
  forall s' : set a538,
  forall x : a538,
  Coq.Init.Logic.not (mem x s) ->
  Coq.Init.Logic.not (mem x s') -> Coq.Init.Logic.not (mem x (union s s')).

Parameter inter :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  set a -> set a -> set a.

Axiom inter_mem :
  forall {a545 : Type},
  forall {Ih_a545 : Inhab a545},
  forall s : set a545,
  forall s' : set a545,
  forall x : a545,
  mem x s -> mem x s' -> mem x (inter s s').

Axiom inter_mem_neq :
  forall {a552 : Type},
  forall {Ih_a552 : Inhab a552},
  forall s : set a552,
  forall s' : set a552,
  forall x : a552,
  Coq.Init.Logic.not (Coq.Init.Logic.or (mem x s) (mem x s')) ->
  Coq.Init.Logic.not (mem x (inter s s')).

Parameter disjoint :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  set a -> set a -> Prop.

Axiom disjoint_def :
  forall {a556 : Type},
  forall {Ih_a556 : Inhab a556},
  forall s : set a556,
  forall s' : set a556,
  Coq.Init.Logic.iff (disjoint s s') (
    eq (inter s s') (@empty a556 Ih_a556)
  ).

Parameter diff :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  set a -> set a -> set a.

Axiom diff_mem :
  forall {a564 : Type},
  forall {Ih_a564 : Inhab a564},
  forall s : set a564,
  forall s' : set a564,
  forall x : a564,
  mem x s' -> Coq.Init.Logic.not (mem x (diff s s')).

Axiom diff_mem_fst :
  forall {a571 : Type},
  forall {Ih_a571 : Inhab a571},
  forall s : set a571,
  forall s' : set a571,
  forall x : a571,
  Coq.Init.Logic.not (mem x s') ->
  Coq.Init.Logic.iff (mem x s) (mem x (diff s s')).

Parameter subset :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  set a -> set a -> Prop.

Axiom subset_def :
  forall {a577 : Type},
  forall {Ih_a577 : Inhab a577},
  forall s : set a577,
  forall s' : set a577,
  Coq.Init.Logic.iff (subset s s') (forall x : a577, mem x s -> mem x s').

Parameter map :
  forall {a : Type},
  forall {b : Type},
  forall {Ih_a : Inhab a},
  forall {Ih_b : Inhab b},
  (a -> b) -> set a -> set b.

Axiom set_map :
  forall {a586 : Type},
  forall {a587 : Type},
  forall {Ih_a586 : Inhab a586},
  forall {Ih_a587 : Inhab a587},
  forall f : a587 -> a586,
  forall s : set a587,
  forall x : a586,
  Coq.Init.Logic.iff (mem x (map f s)) (
    Coq.Init.Logic.ex (
      fun y : a587 =>
      Coq.Init.Logic.and (eq (f y) x) (mem y s)
    )
  ).

Parameter partition :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  (a -> Prop) -> set a -> tuple2 (set a) (set a).

Axiom partition_l_mem :
  forall {a599 : Type},
  forall {Ih_a599 : Inhab a599},
  forall f : a599 -> bool,
  forall s : set a599,
  forall x : a599,
  forall p1 : set a599,
  forall p2 : set a599,
  mem x s -> f x -> eq (partition f s) (tuple2 p1 p2) -> mem x p1.

Axiom partition_r_mem :
  forall {a611 : Type},
  forall {Ih_a611 : Inhab a611},
  forall f : a611 -> bool,
  forall s : set a611,
  forall x : a611,
  forall p1 : set a611,
  forall p2 : set a611,
  mem x s ->
  Coq.Init.Logic.not (f x) ->
  eq (partition f s) (tuple2 p1 p2) -> mem x p2.

Parameter cardinal :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  set a -> Z.

Parameter finite :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  set a -> Prop.

Axiom finite_def :
  forall {a617 : Type},
  forall {Ih_a617 : Inhab a617},
  forall s : set a617,
  Coq.Init.Logic.iff (finite s) (
    Coq.Init.Logic.ex (
      fun seq : sequence a617 =>
      forall x : a617,
      mem x s -> mem x seq
    )
  ).

Axiom cardinal_nonneg :
  forall {a619 : Type},
  forall {Ih_a619 : Inhab a619},
  forall s : set a619,
  ge (cardinal s) (0)%Z.

Axiom cardinal_empty :
  forall {a621 : Type},
  forall {Ih_a621 : Inhab a621},
  eq (cardinal (@empty a621 Ih_a621)) (0)%Z.

Axiom cardinal_remove :
  forall {a633 : Type},
  forall {Ih_a633 : Inhab a633},
  forall s : set a633,
  forall x : a633,
  finite s ->
  (
    if classicT (mem x s) then
      eq (cardinal (remove x s)) (minus (cardinal s) (1)%Z)
      else
    eq (cardinal (remove x s)) (cardinal s)
  ).

Axiom cardinal_add :
  forall {a645 : Type},
  forall {Ih_a645 : Inhab a645},
  forall s : set a645,
  forall x : a645,
  finite s ->
  (
    if classicT (mem x s) then
      eq (cardinal (add x s)) (cardinal s)
      else
    eq (cardinal (add x s)) (plus (cardinal s) (1)%Z)
  ).

Parameter of_seq :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  sequence a -> set a.

Axiom of_seq_mem :
  forall {a651 : Type},
  forall {Ih_a651 : Inhab a651},
  forall s : sequence a651,
  forall x : a651,
  Coq.Init.Logic.iff (mem x (of_seq s)) (mem x s).

Parameter to_seq :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  set a -> sequence a.

Axiom to_seq_mem :
  forall {a657 : Type},
  forall {Ih_a657 : Inhab a657},
  forall s : set a657,
  finite s ->
  (
    forall x : a657,
    Coq.Init.Logic.iff (mem x s) (eq (multiplicity x (to_seq s)) (1)%Z)
  ).

Parameter fold :
  forall {a : Type},
  forall {b : Type},
  forall {Ih_a : Inhab a},
  forall {Ih_b : Inhab b},
  (a -> b) -> (b -> b -> b) -> set a -> b -> b.

Axiom fold_def :
  forall {a : Type},
  forall {b : Type},
  forall {Ih_a : Inhab a},
  forall {Ih_b : Inhab b},
  forall f : a -> b,
  forall m : b -> b -> b,
  forall s : set a,
  forall acc : b,
  finite s ->
  comm_monoid m acc ->
  eq (fold f m s acc) (
    fold_right (fun x : a => fun acc : b => m (f x) acc) (to_seq s) acc
  ).

End _Set.

Parameter map_set :
  forall {a : Type},
  forall {b : Type},
  forall {Ih_a : Inhab a},
  forall {Ih_b : Inhab b},
  (a -> b) -> a -> b -> a -> b.

Axiom map_set_def :
  forall {a : Type},
  forall {b : Type},
  forall {Ih_a : Inhab a},
  forall {Ih_b : Inhab b},
  forall f : a -> b,
  forall x : a,
  forall y : b,
  eq (map_set f x y) (
    fun arg : a =>
    if classicT (eq arg x) then y else f x
  ).

Module Map.

Parameter t : Type -> Type -> Type.

Parameter domain :
  forall {a : Type},
  forall {b : Type},
  forall {Ih_a : Inhab a},
  forall {Ih_b : Inhab b},
  b -> (a -> b) -> set a.

Axiom domain_mem :
  forall {a690 : Type},
  forall {a691 : Type},
  forall {Ih_a690 : Inhab a690},
  forall {Ih_a691 : Inhab a691},
  forall x : a691,
  forall m : a691 -> a690,
  forall default : a690,
  Coq.Init.Logic.not (eq (m x) default) -> mem x (domain default m).

End Map.


