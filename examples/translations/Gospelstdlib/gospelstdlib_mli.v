Set Implicit Arguments.

Require Import Gospel.

Require Coq.ZArith.BinInt TLC.LibLogic TLC.LibRelation TLC.LibInt TLC.LibListZ.

Require Import CFML.SepBase CFML.SepLifted CFML.WPLib CFML.WPLifted CFML.WPRecord CFML.WPArray CFML.WPBuiltin.

Require CFML.Stdlib.Array_ml CFML.Stdlib.List_ml CFML.Stdlib.Sys_ml.

Require Import Coq.ZArith.BinIntDef CFML.Semantics CFML.WPHeader.

Delimit Scope Z_scope with Z.

Module Type Stdlib.

Parameter sequence : Type -> Type.

Parameter Sequence :
  forall a : Type,
  forall {aIh : Inhab a},
  sequence a ->
  sequence a -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter bag : Type -> Type.

Parameter Bag :
  forall a : Type,
  forall {aIh : Inhab a},
  bag a -> bag a -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter set : Type -> Type.

Parameter _Set :
  forall a : Type,
  forall {aIh : Inhab a},
  set a -> set a -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter map : Type -> Type -> Type.

Parameter Map :
  forall a : Type,
  forall b : Type,
  forall {aIh : Inhab a},
  forall {bIh : Inhab b},
  map a b ->
  map a b -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter succ : Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z.

Parameter pred : Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z.

Parameter neg : Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z.

Parameter plus :
  Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z.

Parameter minus :
  Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z.

Parameter mult :
  Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z.

Parameter div :
  Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z.

Parameter _mod :
  Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z.

Parameter pow :
  Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z.

Parameter abs : Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z.

Parameter min :
  Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z.

Parameter max :
  Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z.

Parameter gt : Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z -> Prop.

Parameter ge : Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z -> Prop.

Parameter lt : Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z -> Prop.

Parameter le : Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z -> Prop.

Parameter max_int : Coq.Numbers.BinNums.Z.

Parameter min_int : Coq.Numbers.BinNums.Z.

Parameter app :
  forall a : Type,
  forall {aIh : Inhab a},
  sequence a -> sequence a -> sequence a.

Parameter seq_get :
  forall a : Type,
  forall {aIh : Inhab a},
  sequence a -> Coq.Numbers.BinNums.Z -> a.

Definition map_set  (a : Type) (b : Type) { aIh : Inhab a } {
  bIh : Inhab b
} (f : a -> b) (x : a) (y : b) : a -> b:=
fun arg : a =>
if classicT (Coq.Init.Logic.eq arg x) then y else f x.

Module Sequence.

Parameter t : Type -> Type.

Parameter T :
  forall a : Type,
  forall {aIh : Inhab a},
  t a -> t a -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter length :
  forall a : Type,
  forall {aIh : Inhab a},
  sequence a -> Coq.Numbers.BinNums.Z.

Parameter seq_sub :
  forall a : Type,
  forall {aIh : Inhab a},
  sequence a ->
  Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z -> sequence a.

Definition seq_sub_l  (a : Type) { aIh : Inhab a } (s : sequence a) (
  i : Coq.Numbers.BinNums.Z
) : sequence a:=
seq_sub s i (length s).

Definition seq_sub_r  (a : Type) { aIh : Inhab a } (s : sequence a) (
  i : Coq.Numbers.BinNums.Z
) : sequence a:=
seq_sub s (0)%Z i.

Definition in_range  (a : Type) { aIh : Inhab a } (s : sequence a) (
  i : Coq.Numbers.BinNums.Z
) : Prop:=
Coq.Init.Logic.and (le (0)%Z i) (lt i (length s)).

Parameter length_nonneg :
  forall a10 : Type,
  forall {a10Ih : Inhab a10},
  forall s : sequence a10,
  le (0)%Z (length s).

Parameter append_length :
  forall a16 : Type,
  forall {a16Ih : Inhab a16},
  forall s : sequence a16,
  forall s' : sequence a16,
  Coq.Init.Logic.eq (length (app s s')) (plus (length s) (length s')).

Parameter append_elems_left :
  forall a25 : Type,
  forall {a25Ih : Inhab a25},
  forall s : sequence a25,
  forall s' : sequence a25,
  forall i : Coq.Numbers.BinNums.Z,
  Coq.Init.Logic.and (le (0)%Z i) (lt i (length s)) ->
  Coq.Init.Logic.eq (seq_get (app s s') i) (seq_get s i).

Parameter append_elems_right :
  forall a36 : Type,
  forall {a36Ih : Inhab a36},
  forall s : sequence a36,
  forall s' : sequence a36,
  forall i : Coq.Numbers.BinNums.Z,
  Coq.Init.Logic.and (le (length s) i) (
    lt i (plus (length s) (length s'))
  ) ->
  Coq.Init.Logic.eq (seq_get (app s s') i) (
    seq_get s' (minus i (length s))
  ).

Parameter subseq :
  forall a44 : Type,
  forall {a44Ih : Inhab a44},
  forall s : sequence a44,
  forall i : Coq.Numbers.BinNums.Z,
  forall i1 : Coq.Numbers.BinNums.Z,
  forall i2 : Coq.Numbers.BinNums.Z,
  Coq.Init.Logic.and (le i1 i) (lt i i2) ->
  Coq.Init.Logic.eq (seq_get s i) (seq_get (seq_sub s i1 i2) (minus i i1)).

Parameter init :
  forall a : Type,
  forall {aIh : Inhab a},
  Coq.Numbers.BinNums.Z -> (Coq.Numbers.BinNums.Z -> a) -> sequence a.

Parameter init_length :
  forall a48 : Type,
  forall {a48Ih : Inhab a48},
  forall n : Coq.Numbers.BinNums.Z,
  forall f : Coq.Numbers.BinNums.Z -> a48,
  ge n (0)%Z -> Coq.Init.Logic.eq (length (init n f)) n.

Parameter init_elems :
  forall a56 : Type,
  forall {a56Ih : Inhab a56},
  forall n : Coq.Numbers.BinNums.Z,
  forall f : Coq.Numbers.BinNums.Z -> a56,
  forall i : Coq.Numbers.BinNums.Z,
  Coq.Init.Logic.and (le (0)%Z i) (lt i n) ->
  Coq.Init.Logic.eq (seq_get (init n f) i) (f i).

Parameter empty : forall a : Type, forall {aIh : Inhab a}, sequence a.

Parameter empty_length :
  forall a58 : Type,
  forall {a58Ih : Inhab a58},
  Coq.Init.Logic.eq (length (@empty a58 a58Ih)) (0)%Z.

Definition singleton  (a : Type) { aIh : Inhab a } (x : a) : sequence a:=
init (1)%Z (fun _ : Coq.Numbers.BinNums.Z => x).

Definition cons  (a : Type) { aIh : Inhab a } (x : a) (s : sequence a) : sequence a:=
app (singleton x) s.

Definition snoc  (a : Type) { aIh : Inhab a } (s : sequence a) (x : a) : sequence a:=
app s (singleton x).

Definition hd  (a : Type) { aIh : Inhab a } (s : sequence a) : a:=
seq_get s (0)%Z.

Definition tl  (a : Type) { aIh : Inhab a } (s : sequence a) : sequence a:=
seq_sub_l s (1)%Z.

Definition append  (a : Type) { aIh : Inhab a } (s1 : sequence a) (
  s2 : sequence a
) : sequence a:=
app s1 s2.

Parameter multiplicity :
  forall a : Type,
  forall {aIh : Inhab a},
  a -> sequence a -> Coq.Numbers.BinNums.Z.

Parameter mult_empty :
  forall a72 : Type,
  forall {a72Ih : Inhab a72},
  forall x : a72,
  Coq.Init.Logic.eq (multiplicity x (@empty a72 a72Ih)) (0)%Z.

Parameter mult_cons :
  forall a78 : Type,
  forall {a78Ih : Inhab a78},
  forall s : sequence a78,
  forall x : a78,
  Coq.Init.Logic.eq (plus (1)%Z (multiplicity x s)) (
    multiplicity x (cons x s)
  ).

Parameter mult_cons_neutral :
  forall a86 : Type,
  forall {a86Ih : Inhab a86},
  forall s : sequence a86,
  forall x1 : a86,
  forall x2 : a86,
  Coq.Init.Logic.not (Coq.Init.Logic.eq x1 x2) ->
  Coq.Init.Logic.eq (multiplicity x1 s) (multiplicity x1 (cons x2 s)).

Parameter mult_length :
  forall a91 : Type,
  forall {a91Ih : Inhab a91},
  forall x : a91,
  forall s : sequence a91,
  Coq.Init.Logic.and (le (0)%Z (multiplicity x s)) (
    le (multiplicity x s) (length s)
  ).

Definition mem  (a : Type) { aIh : Inhab a } (x : a) (s : sequence a) : Prop:=
gt (multiplicity x s) (0)%Z.

Parameter map :
  forall a : Type,
  forall b : Type,
  forall {aIh : Inhab a},
  forall {bIh : Inhab b},
  (a -> b) -> sequence a -> sequence b.

Parameter map_elems :
  forall a100 : Type,
  forall a102 : Type,
  forall {a100Ih : Inhab a100},
  forall {a102Ih : Inhab a102},
  forall i : Coq.Numbers.BinNums.Z,
  forall f : a100 -> a102,
  forall s : sequence a100,
  Coq.Init.Logic.and (le (0)%Z i) (lt i (length s)) ->
  Coq.Init.Logic.eq (seq_get (map f s) i) (f (seq_get s i)).

Parameter filter :
  forall a : Type,
  forall {aIh : Inhab a},
  (a -> Prop) -> sequence a -> sequence a.

Parameter filter_elems :
  forall a109 : Type,
  forall {a109Ih : Inhab a109},
  forall f : a109 -> bool,
  forall s : sequence a109,
  forall x : a109,
  mem x s -> f x -> mem x (filter f s).

Definition get  (a : Type) { aIh : Inhab a } (s : sequence a) (
  i : Coq.Numbers.BinNums.Z
) : a:=
seq_get s i.

Parameter set :
  forall a : Type,
  forall {aIh : Inhab a},
  sequence a -> Coq.Numbers.BinNums.Z -> a -> sequence a.

Parameter set_elem :
  forall a117 : Type,
  forall {a117Ih : Inhab a117},
  forall s : sequence a117,
  forall i : Coq.Numbers.BinNums.Z,
  forall x : a117,
  Coq.Init.Logic.and (le (0)%Z i) (lt i (length s)) ->
  Coq.Init.Logic.eq (seq_get (set s i x) i) x.

Parameter set_elem_other :
  forall a128 : Type,
  forall {a128Ih : Inhab a128},
  forall s : sequence a128,
  forall i1 : Coq.Numbers.BinNums.Z,
  forall i2 : Coq.Numbers.BinNums.Z,
  forall x : a128,
  Coq.Init.Logic.not (Coq.Init.Logic.eq i1 i2) ->
  Coq.Init.Logic.and (le (0)%Z i1) (lt i1 (length s)) ->
  Coq.Init.Logic.and (le (0)%Z i2) (lt i2 (length s)) ->
  Coq.Init.Logic.eq (seq_get (set s i1 x) i2) (seq_get s i2).

Parameter rev :
  forall a : Type,
  forall {aIh : Inhab a},
  sequence a -> sequence a.

Parameter rev_length :
  forall a132 : Type,
  forall {a132Ih : Inhab a132},
  forall s : sequence a132,
  Coq.Init.Logic.eq (length s) (length (rev s)).

Parameter rev_elems :
  forall a141 : Type,
  forall {a141Ih : Inhab a141},
  forall i : Coq.Numbers.BinNums.Z,
  forall s : sequence a141,
  Coq.Init.Logic.and (le (0)%Z i) (lt i (length s)) ->
  Coq.Init.Logic.eq (seq_get (rev s) i) (
    seq_get s (minus (minus (length s) (1)%Z) i)
  ).

Parameter fold :
  forall a : Type,
  forall b : Type,
  forall {aIh : Inhab a},
  forall {bIh : Inhab b},
  (a -> b -> a) -> a -> sequence b -> a.

Parameter fold_empty :
  forall a146 : Type,
  forall a147 : Type,
  forall {a146Ih : Inhab a146},
  forall {a147Ih : Inhab a147},
  forall f : a147 -> a146 -> a147,
  forall acc : a147,
  Coq.Init.Logic.eq (fold f acc (@empty a146 a146Ih)) acc.

Parameter fold_cons :
  forall a158 : Type,
  forall a159 : Type,
  forall {a158Ih : Inhab a158},
  forall {a159Ih : Inhab a159},
  forall f : a159 -> a158 -> a159,
  forall acc : a159,
  forall x : a158,
  forall l : sequence a158,
  Coq.Init.Logic.eq (fold f acc (cons x l)) (fold f (f acc x) l).

Parameter extensionality :
  forall a169 : Type,
  forall {a169Ih : Inhab a169},
  forall s1 : sequence a169,
  forall s2 : sequence a169,
  Coq.Init.Logic.eq (length s1) (length s2) ->
  (
    forall i : Coq.Numbers.BinNums.Z,
    Coq.Init.Logic.and (le (0)%Z i) (lt i (length s1)) ->
    Coq.Init.Logic.eq (seq_get s1 i) (seq_get s2 i)
  ) ->
  Coq.Init.Logic.eq s1 s2.

Parameter of_list :
  forall a : Type,
  forall {aIh : Inhab a},
  list a -> sequence a.

Parameter fold_left :
  forall a : Type,
  forall b : Type,
  forall {aIh : Inhab a},
  forall {bIh : Inhab b},
  (a -> b -> a) -> a -> sequence b -> a.

Parameter fold_right :
  forall a : Type,
  forall b : Type,
  forall {aIh : Inhab a},
  forall {bIh : Inhab b},
  (b -> a -> a) -> sequence b -> a -> a.

End Sequence.

Module Bag.

Parameter t : Type -> Type.

Parameter T :
  forall a : Type,
  forall {aIh : Inhab a},
  t a -> t a -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter multiplicity :
  forall a : Type,
  forall {aIh : Inhab a},
  a -> bag a -> Coq.Numbers.BinNums.Z.

Parameter well_formed :
  forall a173 : Type,
  forall {a173Ih : Inhab a173},
  forall b : a173,
  forall x : bag a173,
  ge (multiplicity b x) (0)%Z.

Parameter empty : forall a : Type, forall {aIh : Inhab a}, bag a.

Parameter empty_mult :
  forall a176 : Type,
  forall {a176Ih : Inhab a176},
  forall x : a176,
  Coq.Init.Logic.eq (multiplicity x (@empty a176 a176Ih)) (0)%Z.

Parameter init :
  forall a : Type,
  forall {aIh : Inhab a},
  (a -> Coq.Numbers.BinNums.Z) -> bag a.

Parameter init_axiom :
  forall a182 : Type,
  forall {a182Ih : Inhab a182},
  forall f : a182 -> Coq.Numbers.BinNums.Z,
  forall x : a182,
  Coq.Init.Logic.eq (max (0)%Z (f x)) (multiplicity x (init f)).

Parameter add :
  forall a : Type,
  forall {aIh : Inhab a},
  a -> bag a -> bag a.

Parameter add_mult_x :
  forall a188 : Type,
  forall {a188Ih : Inhab a188},
  forall b : bag a188,
  forall x : a188,
  Coq.Init.Logic.eq (multiplicity x (add x b)) (
    plus (1)%Z (multiplicity x b)
  ).

Parameter add_mult_neg_x :
  forall a196 : Type,
  forall {a196Ih : Inhab a196},
  forall x : a196,
  forall y : a196,
  forall b : bag a196,
  Coq.Init.Logic.not (Coq.Init.Logic.eq x y) ->
  Coq.Init.Logic.eq (multiplicity y (add x b)) (multiplicity y b).

Definition singleton  (a : Type) { aIh : Inhab a } (x : a) : bag a:=
add x (@empty a aIh).

Definition mem  (a : Type) { aIh : Inhab a } (x : a) (b : bag a) : Prop:=
gt (multiplicity x b) (0)%Z.

Parameter remove :
  forall a : Type,
  forall {aIh : Inhab a},
  a -> bag a -> bag a.

Parameter remove_mult_x :
  forall a205 : Type,
  forall {a205Ih : Inhab a205},
  forall b : bag a205,
  forall x : a205,
  Coq.Init.Logic.eq (multiplicity x (remove x b)) (
    max (0)%Z (minus (multiplicity x b) (1)%Z)
  ).

Parameter remove_mult_neg_x :
  forall a213 : Type,
  forall {a213Ih : Inhab a213},
  forall x : a213,
  forall y : a213,
  forall b : bag a213,
  Coq.Init.Logic.not (Coq.Init.Logic.eq x y) ->
  Coq.Init.Logic.eq (multiplicity y (remove x b)) (multiplicity y b).

Parameter union :
  forall a : Type,
  forall {aIh : Inhab a},
  bag a -> bag a -> bag a.

Parameter union_all :
  forall a221 : Type,
  forall {a221Ih : Inhab a221},
  forall b : bag a221,
  forall b' : bag a221,
  forall x : a221,
  Coq.Init.Logic.eq (max (multiplicity x b) (multiplicity x b')) (
    multiplicity x (union b b')
  ).

Parameter sum :
  forall a : Type,
  forall {aIh : Inhab a},
  bag a -> bag a -> bag a.

Parameter sum_all :
  forall a229 : Type,
  forall {a229Ih : Inhab a229},
  forall b : bag a229,
  forall b' : bag a229,
  forall x : a229,
  Coq.Init.Logic.eq (plus (multiplicity x b) (multiplicity x b')) (
    multiplicity x (sum b b')
  ).

Parameter inter :
  forall a : Type,
  forall {aIh : Inhab a},
  bag a -> bag a -> bag a.

Parameter inter_all :
  forall a237 : Type,
  forall {a237Ih : Inhab a237},
  forall b : bag a237,
  forall b' : bag a237,
  forall x : a237,
  Coq.Init.Logic.eq (min (multiplicity x b) (multiplicity x b')) (
    multiplicity x (inter b b')
  ).

Parameter diff :
  forall a : Type,
  forall {aIh : Inhab a},
  bag a -> bag a -> bag a.

Parameter diff_all :
  forall a245 : Type,
  forall {a245Ih : Inhab a245},
  forall b : bag a245,
  forall b' : bag a245,
  forall x : a245,
  Coq.Init.Logic.eq (
    max (0)%Z (minus (multiplicity x b) (multiplicity x b'))
  ) (multiplicity x (diff b b')).

Definition disjoint  (a : Type) { aIh : Inhab a } (b : bag a) (
  b' : bag a
) : Prop:=
forall x : a,
mem x b -> Coq.Init.Logic.not (mem x b').

Definition subset  (a : Type) { aIh : Inhab a } (b : bag a) (b' : bag a) : Prop:=
forall x : a,
le (multiplicity x b) (multiplicity x b').

Parameter filter :
  forall a : Type,
  forall {aIh : Inhab a},
  (a -> Prop) -> bag a -> bag a.

Parameter filter_mem :
  forall a259 : Type,
  forall {a259Ih : Inhab a259},
  forall b : bag a259,
  forall x : a259,
  forall f : a259 -> bool,
  f x ->
  Coq.Init.Logic.eq (multiplicity x (filter f b)) (multiplicity x b).

Parameter filter_mem_neg :
  forall a266 : Type,
  forall {a266Ih : Inhab a266},
  forall b : bag a266,
  forall x : a266,
  forall f : a266 -> bool,
  Coq.Init.Logic.not (f x) ->
  Coq.Init.Logic.eq (multiplicity x (filter f b)) (0)%Z.

Parameter cardinal :
  forall a : Type,
  forall {aIh : Inhab a},
  bag a -> Coq.Numbers.BinNums.Z.

Definition finite  (a : Type) { aIh : Inhab a } (b : bag a) : Prop:=
Coq.Init.Logic.ex (
  fun s : sequence a =>
  forall x : a,
  mem x b -> Sequence.mem x s
).

Parameter card_nonneg :
  forall a273 : Type,
  forall {a273Ih : Inhab a273},
  forall b : bag a273,
  ge (cardinal b) (0)%Z.

Parameter card_empty :
  forall a276 : Type,
  forall a274 : Type,
  forall {a276Ih : Inhab a276},
  forall {a274Ih : Inhab a274},
  forall b : a274,
  Coq.Init.Logic.eq (cardinal (@empty a276 a276Ih)) (0)%Z.

Parameter card_singleton :
  forall a280 : Type,
  forall {a280Ih : Inhab a280},
  forall x : a280,
  Coq.Init.Logic.eq (cardinal (singleton x)) (1)%Z.

Parameter card_union :
  forall a289 : Type,
  forall {a289Ih : Inhab a289},
  forall b1 : bag a289,
  forall b2 : bag a289,
  finite b1 ->
  finite b2 ->
  Coq.Init.Logic.eq (cardinal (union b1 b2)) (
    plus (cardinal b1) (cardinal b2)
  ).

Parameter card_add :
  forall a296 : Type,
  forall {a296Ih : Inhab a296},
  forall x : a296,
  forall b : bag a296,
  finite b ->
  Coq.Init.Logic.eq (cardinal (add x b)) (plus (cardinal b) (1)%Z).

Parameter card_map :
  forall a303 : Type,
  forall {a303Ih : Inhab a303},
  forall f : a303 -> bool,
  forall b : bag a303,
  finite b -> le (cardinal (filter f b)) (cardinal b).

Parameter of_seq :
  forall a : Type,
  forall {aIh : Inhab a},
  sequence a -> bag a.

Parameter of_seq_multiplicity :
  forall a308 : Type,
  forall {a308Ih : Inhab a308},
  forall s : sequence a308,
  forall x : a308,
  Coq.Init.Logic.eq (Sequence.multiplicity x s) (
    multiplicity x (of_seq s)
  ).

End Bag.

Parameter set_create : forall a : Type, forall {aIh : Inhab a}, set a.

Module _Set.

Parameter t : Type -> Type.

Parameter T :
  forall a : Type,
  forall {aIh : Inhab a},
  t a -> t a -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter mem :
  forall a : Type,
  forall {aIh : Inhab a},
  a -> set a -> Prop.

Parameter empty : forall a : Type, forall {aIh : Inhab a}, set a.

Parameter empty_mem :
  forall a312 : Type,
  forall {a312Ih : Inhab a312},
  forall x : a312,
  Coq.Init.Logic.not (mem x (@empty a312 a312Ih)).

Parameter add :
  forall a : Type,
  forall {aIh : Inhab a},
  a -> set a -> set a.

Parameter add_mem :
  forall a316 : Type,
  forall {a316Ih : Inhab a316},
  forall s : set a316,
  forall x : a316,
  mem x (add x s).

Parameter add_mem_neq :
  forall a323 : Type,
  forall {a323Ih : Inhab a323},
  forall s : set a323,
  forall x : a323,
  forall y : a323,
  Coq.Init.Logic.not (Coq.Init.Logic.eq x y) ->
  Coq.Init.Logic.iff (mem x s) (mem x (add y s)).

Definition singleton  (a : Type) { aIh : Inhab a } (x : a) : set a:=
add x (@empty a aIh).

Parameter remove :
  forall a : Type,
  forall {aIh : Inhab a},
  a -> set a -> set a.

Parameter remove_mem :
  forall a329 : Type,
  forall {a329Ih : Inhab a329},
  forall s : set a329,
  forall x : a329,
  Coq.Init.Logic.not (mem x (remove x s)).

Parameter remove_mem_neq :
  forall a336 : Type,
  forall {a336Ih : Inhab a336},
  forall s : set a336,
  forall x : a336,
  forall y : a336,
  Coq.Init.Logic.not (Coq.Init.Logic.eq x y) ->
  Coq.Init.Logic.iff (mem x s) (mem x (remove y s)).

Parameter union :
  forall a : Type,
  forall {aIh : Inhab a},
  set a -> set a -> set a.

Parameter union_mem :
  forall a343 : Type,
  forall {a343Ih : Inhab a343},
  forall s : set a343,
  forall s' : set a343,
  forall x : a343,
  Coq.Init.Logic.or (mem x s) (mem x s') -> mem x (union s s').

Parameter union_mem_neg :
  forall a350 : Type,
  forall {a350Ih : Inhab a350},
  forall s : set a350,
  forall s' : set a350,
  forall x : a350,
  Coq.Init.Logic.not (mem x s) ->
  Coq.Init.Logic.not (mem x s') -> Coq.Init.Logic.not (mem x (union s s')).

Parameter inter :
  forall a : Type,
  forall {aIh : Inhab a},
  set a -> set a -> set a.

Parameter inter_mem :
  forall a357 : Type,
  forall {a357Ih : Inhab a357},
  forall s : set a357,
  forall s' : set a357,
  forall x : a357,
  mem x s -> mem x s' -> mem x (inter s s').

Parameter inter_mem_neq :
  forall a364 : Type,
  forall {a364Ih : Inhab a364},
  forall s : set a364,
  forall s' : set a364,
  forall x : a364,
  Coq.Init.Logic.not (Coq.Init.Logic.or (mem x s) (mem x s')) ->
  Coq.Init.Logic.not (mem x (inter s s')).

Definition disjoint  (a : Type) { aIh : Inhab a } (s : set a) (
  s' : set a
) : Prop:=
Coq.Init.Logic.eq (inter s s') (@empty a aIh).

Parameter diff :
  forall a : Type,
  forall {aIh : Inhab a},
  set a -> set a -> set a.

Parameter diff_mem :
  forall a373 : Type,
  forall {a373Ih : Inhab a373},
  forall s : set a373,
  forall s' : set a373,
  forall x : a373,
  mem x s' -> Coq.Init.Logic.not (mem x (diff s s')).

Parameter diff_mem_fst :
  forall a380 : Type,
  forall {a380Ih : Inhab a380},
  forall s : set a380,
  forall s' : set a380,
  forall x : a380,
  Coq.Init.Logic.not (mem x s') ->
  Coq.Init.Logic.iff (mem x s) (mem x (diff s s')).

Definition subset  (a : Type) { aIh : Inhab a } (s : set a) (s' : set a) : Prop:=
forall x : a,
mem x s -> mem x s'.

Parameter map :
  forall a : Type,
  forall b : Type,
  forall {aIh : Inhab a},
  forall {bIh : Inhab b},
  (a -> b) -> set a -> set b.

Parameter set_map :
  forall a392 : Type,
  forall a393 : Type,
  forall {a392Ih : Inhab a392},
  forall {a393Ih : Inhab a393},
  forall f : a393 -> a392,
  forall s : set a393,
  forall x : a392,
  Coq.Init.Logic.iff (mem x (map f s)) (
    Coq.Init.Logic.ex (
      fun y : a393 =>
      Coq.Init.Logic.and (Coq.Init.Logic.eq (f y) x) (mem y s)
    )
  ).

Parameter cardinal :
  forall a : Type,
  forall {aIh : Inhab a},
  set a -> Coq.Numbers.BinNums.Z.

Definition finite  (a : Type) { aIh : Inhab a } (s : set a) : Prop:=
Coq.Init.Logic.ex (
  fun seq : sequence a =>
  forall x : a,
  mem x s -> Sequence.mem x seq
).

Parameter cardinal_nonneg :
  forall a399 : Type,
  forall {a399Ih : Inhab a399},
  forall s : set a399,
  ge (cardinal s) (0)%Z.

Parameter cardinal_empty :
  forall a401 : Type,
  forall {a401Ih : Inhab a401},
  Coq.Init.Logic.eq (cardinal (@empty a401 a401Ih)) (0)%Z.

Parameter cardinal_remove :
  forall a413 : Type,
  forall {a413Ih : Inhab a413},
  forall s : set a413,
  forall x : a413,
  finite s ->
  (
    if classicT (mem x s) then
      Coq.Init.Logic.eq (cardinal (remove x s)) (minus (cardinal s) (1)%Z)
      else
    Coq.Init.Logic.eq (cardinal (remove x s)) (cardinal s)
  ).

Parameter cardinal_add :
  forall a425 : Type,
  forall {a425Ih : Inhab a425},
  forall s : set a425,
  forall x : a425,
  finite s ->
  (
    if classicT (mem x s) then
      Coq.Init.Logic.eq (cardinal (add x s)) (cardinal s)
      else
    Coq.Init.Logic.eq (cardinal (add x s)) (plus (cardinal s) (1)%Z)
  ).

Parameter of_seq :
  forall a : Type,
  forall {aIh : Inhab a},
  sequence a -> set a.

Parameter of_seq_set :
  forall a431 : Type,
  forall {a431Ih : Inhab a431},
  forall x : a431,
  forall s : sequence a431,
  Coq.Init.Logic.iff (Sequence.mem x s) (mem x (of_seq s)).

Parameter fold :
  forall a : Type,
  forall b : Type,
  forall {aIh : Inhab a},
  forall {bIh : Inhab b},
  (a -> b -> b) -> set a -> b -> b.

End _Set.

Module Map.

Parameter t : Type -> Type -> Type.

Parameter T :
  forall a : Type,
  forall b : Type,
  forall {aIh : Inhab a},
  forall {bIh : Inhab b},
  t a b -> t a b -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter domain :
  forall a : Type,
  forall b : Type,
  forall {aIh : Inhab a},
  forall {bIh : Inhab b},
  b -> (a -> b) -> set a.

Parameter domain_mem :
  forall a438 : Type,
  forall a439 : Type,
  forall {a438Ih : Inhab a438},
  forall {a439Ih : Inhab a439},
  forall x : a439,
  forall m : a439 -> a438,
  forall default : a438,
  Coq.Init.Logic.not (Coq.Init.Logic.eq (m x) default) ->
  _Set.mem x (domain default m).

End Map.

Module Array.

Parameter get :
  forall a : Type,
  forall {aIh : Inhab a},
  array a -> Coq.Numbers.BinNums.Z -> a.

Parameter length :
  forall a : Type,
  forall {aIh : Inhab a},
  array a -> Coq.Numbers.BinNums.Z.

Parameter to_seq :
  forall a : Type,
  forall {aIh : Inhab a},
  array a -> sequence a.

Parameter permut :
  forall a : Type,
  forall {aIh : Inhab a},
  array a -> array a -> Prop.

Parameter permut_sub :
  forall a : Type,
  forall {aIh : Inhab a},
  array a ->
  array a -> Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z -> Prop.

End Array.

Module List.

Parameter fold_left :
  forall a : Type,
  forall b : Type,
  forall {aIh : Inhab a},
  forall {bIh : Inhab b},
  (b -> a -> b) -> b -> list a -> b.

Parameter _exists :
  forall a : Type,
  forall {aIh : Inhab a},
  (a -> Prop) -> list a -> Prop.

Parameter length :
  forall a : Type,
  forall {aIh : Inhab a},
  list a -> Coq.Numbers.BinNums.Z.

Parameter nth :
  forall a : Type,
  forall {aIh : Inhab a},
  list a -> Coq.Numbers.BinNums.Z -> a.

Parameter mem :
  forall a : Type,
  forall {aIh : Inhab a},
  a -> list a -> Prop.

Parameter map :
  forall a : Type,
  forall b : Type,
  forall {aIh : Inhab a},
  forall {bIh : Inhab b},
  (a -> b) -> list a -> list b.

End List.

Module Order.

Parameter is_pre_order :
  forall a : Type,
  forall {aIh : Inhab a},
  (a -> a -> int) -> Prop.

End Order.

Parameter ref : Type -> Type.

Parameter Ref :
  forall a : Type,
  forall {aIh : Inhab a},
  ref a -> ref a -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter _UNUSED : forall a : Type, forall {aIh : Inhab a}, ref a -> a.

Parameter logand :
  Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z.

Parameter integer_of_int : int -> Coq.Numbers.BinNums.Z.


End Stdlib.
