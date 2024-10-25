Set Implicit Arguments.

Require Import stdlib_defs.

Require Coq.ZArith.BinInt TLC.LibLogic TLC.LibRelation TLC.LibInt TLC.LibListZ.

Require Import CFML.SepBase CFML.SepLifted CFML.WPLib CFML.WPLifted CFML.WPRecord CFML.WPArray CFML.WPBuiltin.

Require CFML.Stdlib.Array_ml CFML.Stdlib.List_ml CFML.Stdlib.Sys_ml.

Require Import Coq.ZArith.BinIntDef CFML.Semantics CFML.WPHeader.

Delimit Scope Z_scope with Z.

Module Type Stdlib.

Parameter sequence : Type -> Type.

Parameter Sequence :
  forall {a : Type},
  forall {_Ga : OCamlType a},
  sequence a ->
  sequence a -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter bag : Type -> Type.

Parameter Bag :
  forall {a : Type},
  forall {_Ga : OCamlType a},
  bag a -> bag a -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter set : Type -> Type.

Parameter _Set :
  forall {a : Type},
  forall {_Ga : OCamlType a},
  set a -> set a -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter map : Type -> Type -> Type.

Parameter Map :
  forall {a : Type},
  forall {b : Type},
  forall {_Ga : OCamlType a},
  forall {_Gb : OCamlType b},
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
  forall {a : Type},
  forall {_Ga : GospelType a},
  sequence a -> sequence a -> sequence a.

Parameter seq_get :
  forall {a : Type},
  forall {_Ga : GospelType a},
  sequence a -> Coq.Numbers.BinNums.Z -> a.

Definition map_set  { a : Type } { b : Type } { _Ga : GospelType a } {
  _Gb : GospelType b
} (f : a -> b) (x : a) (y : b) : a -> b:=
fun arg : a =>
if classicT (Coq.Init.Logic.eq arg x) then y else f x.

Parameter seq_sub :
  forall {a : Type},
  forall {_Ga : GospelType a},
  sequence a ->
  Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z -> sequence a.

Parameter seq_sub_l :
  forall {a : Type},
  forall {_Ga : GospelType a},
  sequence a -> Coq.Numbers.BinNums.Z -> sequence a.

Definition seq_sub_r  { a : Type } { _Ga : GospelType a } (
  s : sequence a
) (i : Coq.Numbers.BinNums.Z) : sequence a:=
seq_sub s (0)%Z i.

Module Sequence.

Parameter t : Type -> Type.

Parameter Sequence :
  forall {a : Type},
  forall {_Ga : OCamlType a},
  t a -> t a -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter length :
  forall {a : Type},
  forall {_Ga : GospelType a},
  sequence a -> Coq.Numbers.BinNums.Z.

Definition in_range  { a : Type } { _Ga : GospelType a } (
  s : sequence a
) (i : Coq.Numbers.BinNums.Z) : Prop:=
Coq.Init.Logic.and (le (0)%Z i) (lt i (length s)).

Axiom length_nonneg :
  forall {a8 : Type},
  forall {_Ga8 : GospelType a8},
  forall s : sequence a8,
  le (0)%Z (length s).

Axiom append_length :
  forall {a14 : Type},
  forall {_Ga14 : GospelType a14},
  forall s : sequence a14,
  forall s' : sequence a14,
  Coq.Init.Logic.eq (length (app s s')) (plus (length s) (length s')).

Axiom append_elems_left :
  forall {a23 : Type},
  forall {_Ga23 : GospelType a23},
  forall s : sequence a23,
  forall s' : sequence a23,
  forall i : Coq.Numbers.BinNums.Z,
  Coq.Init.Logic.and (le (0)%Z i) (lt i (length s)) ->
  Coq.Init.Logic.eq (seq_get (app s s') i) (seq_get s i).

Axiom append_elems_right :
  forall {a34 : Type},
  forall {_Ga34 : GospelType a34},
  forall s : sequence a34,
  forall s' : sequence a34,
  forall i : Coq.Numbers.BinNums.Z,
  Coq.Init.Logic.and (le (length s) i) (
    lt i (plus (length s) (length s'))
  ) ->
  Coq.Init.Logic.eq (seq_get (app s s') i) (
    seq_get s' (minus i (length s))
  ).

Axiom subseq_l :
  forall {a40 : Type},
  forall {_Ga40 : GospelType a40},
  forall s : sequence a40,
  forall i : Coq.Numbers.BinNums.Z,
  Coq.Init.Logic.and (le (0)%Z i) (lt i (length s)) ->
  Coq.Init.Logic.eq (seq_sub_l s i) (seq_sub s i (length s)).

Axiom subseq :
  forall {a50 : Type},
  forall {_Ga50 : GospelType a50},
  forall s : sequence a50,
  forall i : Coq.Numbers.BinNums.Z,
  forall i1 : Coq.Numbers.BinNums.Z,
  forall i2 : Coq.Numbers.BinNums.Z,
  Coq.Init.Logic.and (le (0)%Z i1) (
    Coq.Init.Logic.and (le i1 i) (
      Coq.Init.Logic.and (lt i i2) (le i2 (length s))
    )
  ) ->
  Coq.Init.Logic.eq (seq_get s i) (seq_get (seq_sub s i1 i2) (minus i i1)).

Axiom subseq_len :
  forall {a56 : Type},
  forall {_Ga56 : GospelType a56},
  forall s : sequence a56,
  forall i1 : Coq.Numbers.BinNums.Z,
  forall i2 : Coq.Numbers.BinNums.Z,
  Coq.Init.Logic.and (le (0)%Z i1) (
    Coq.Init.Logic.and (le i1 i2) (lt i2 (length s))
  ) ->
  Coq.Init.Logic.eq (length (seq_sub s i1 i2)) (minus i1 i2).

Parameter init :
  forall {a : Type},
  forall {_Ga : GospelType a},
  Coq.Numbers.BinNums.Z -> (Coq.Numbers.BinNums.Z -> a) -> sequence a.

Axiom init_length :
  forall {a61 : Type},
  forall {_Ga61 : GospelType a61},
  forall n : Coq.Numbers.BinNums.Z,
  forall f : Coq.Numbers.BinNums.Z -> a61,
  ge n (0)%Z -> Coq.Init.Logic.eq (length (init n f)) n.

Axiom init_elems :
  forall {a69 : Type},
  forall {_Ga69 : GospelType a69},
  forall n : Coq.Numbers.BinNums.Z,
  forall f : Coq.Numbers.BinNums.Z -> a69,
  forall i : Coq.Numbers.BinNums.Z,
  Coq.Init.Logic.and (le (0)%Z i) (lt i n) ->
  Coq.Init.Logic.eq (seq_get (init n f) i) (f i).

Parameter empty :
  forall {a : Type},
  forall {_Ga : GospelType a},
  sequence a.

Axiom empty_length :
  forall {a71 : Type},
  forall {_Ga71 : GospelType a71},
  Coq.Init.Logic.eq (length (@empty a71 _Ga71)) (0)%Z.

Definition singleton  { a : Type } { _Ga : GospelType a } (x : a) : sequence a:=
init (1)%Z (fun _ : Coq.Numbers.BinNums.Z => x).

Definition cons  { a : Type } { _Ga : GospelType a } (x : a) (
  s : sequence a
) : sequence a:=
app (singleton x) s.

Definition snoc  { a : Type } { _Ga : GospelType a } (s : sequence a) (
  x : a
) : sequence a:=
app s (singleton x).

Definition hd  { a : Type } { _Ga : GospelType a } (s : sequence a) : a:=
seq_get s (0)%Z.

Definition tl  { a : Type } { _Ga : GospelType a } (s : sequence a) : sequence a:=
seq_sub_l s (1)%Z.

Definition append  { a : Type } { _Ga : GospelType a } (s1 : sequence a) (
  s2 : sequence a
) : sequence a:=
app s1 s2.

Parameter multiplicity :
  forall {a : Type},
  forall {_Ga : GospelType a},
  a -> sequence a -> Coq.Numbers.BinNums.Z.

Axiom mult_empty :
  forall {a85 : Type},
  forall {_Ga85 : GospelType a85},
  forall x : a85,
  Coq.Init.Logic.eq (multiplicity x (@empty a85 _Ga85)) (0)%Z.

Axiom mult_cons :
  forall {a91 : Type},
  forall {_Ga91 : GospelType a91},
  forall s : sequence a91,
  forall x : a91,
  Coq.Init.Logic.eq (plus (1)%Z (multiplicity x s)) (
    multiplicity x (cons x s)
  ).

Axiom mult_cons_neutral :
  forall {a99 : Type},
  forall {_Ga99 : GospelType a99},
  forall s : sequence a99,
  forall x1 : a99,
  forall x2 : a99,
  Coq.Init.Logic.not (Coq.Init.Logic.eq x1 x2) ->
  Coq.Init.Logic.eq (multiplicity x1 s) (multiplicity x1 (cons x2 s)).

Axiom mult_length :
  forall {a104 : Type},
  forall {_Ga104 : GospelType a104},
  forall x : a104,
  forall s : sequence a104,
  Coq.Init.Logic.and (le (0)%Z (multiplicity x s)) (
    le (multiplicity x s) (length s)
  ).

Definition mem  { a : Type } { _Ga : GospelType a } (x : a) (
  s : sequence a
) : Prop:=
gt (multiplicity x s) (0)%Z.

Parameter map :
  forall {a : Type},
  forall {b : Type},
  forall {_Ga : GospelType a},
  forall {_Gb : GospelType b},
  (a -> b) -> sequence a -> sequence b.

Axiom map_elems :
  forall {a113 : Type},
  forall {a115 : Type},
  forall {_Ga113 : GospelType a113},
  forall {_Ga115 : GospelType a115},
  forall i : Coq.Numbers.BinNums.Z,
  forall f : a113 -> a115,
  forall s : sequence a113,
  Coq.Init.Logic.and (le (0)%Z i) (lt i (length s)) ->
  Coq.Init.Logic.eq (seq_get (map f s) i) (f (seq_get s i)).

Parameter filter :
  forall {a : Type},
  forall {_Ga : GospelType a},
  (a -> Prop) -> sequence a -> sequence a.

Axiom filter_elems :
  forall {a122 : Type},
  forall {_Ga122 : GospelType a122},
  forall f : a122 -> bool,
  forall s : sequence a122,
  forall x : a122,
  mem x s -> f x -> mem x (filter f s).

Definition get  { a : Type } { _Ga : GospelType a } (s : sequence a) (
  i : Coq.Numbers.BinNums.Z
) : a:=
seq_get s i.

Parameter set :
  forall {a : Type},
  forall {_Ga : GospelType a},
  sequence a -> Coq.Numbers.BinNums.Z -> a -> sequence a.

Axiom set_elem :
  forall {a130 : Type},
  forall {_Ga130 : GospelType a130},
  forall s : sequence a130,
  forall i : Coq.Numbers.BinNums.Z,
  forall x : a130,
  Coq.Init.Logic.and (le (0)%Z i) (lt i (length s)) ->
  Coq.Init.Logic.eq (seq_get (set s i x) i) x.

Axiom set_elem_other :
  forall {a141 : Type},
  forall {_Ga141 : GospelType a141},
  forall s : sequence a141,
  forall i1 : Coq.Numbers.BinNums.Z,
  forall i2 : Coq.Numbers.BinNums.Z,
  forall x : a141,
  Coq.Init.Logic.not (Coq.Init.Logic.eq i1 i2) ->
  Coq.Init.Logic.and (le (0)%Z i1) (lt i1 (length s)) ->
  Coq.Init.Logic.and (le (0)%Z i2) (lt i2 (length s)) ->
  Coq.Init.Logic.eq (seq_get (set s i1 x) i2) (seq_get s i2).

Parameter rev :
  forall {a : Type},
  forall {_Ga : GospelType a},
  sequence a -> sequence a.

Axiom rev_length :
  forall {a145 : Type},
  forall {_Ga145 : GospelType a145},
  forall s : sequence a145,
  Coq.Init.Logic.eq (length s) (length (rev s)).

Axiom rev_elems :
  forall {a154 : Type},
  forall {_Ga154 : GospelType a154},
  forall i : Coq.Numbers.BinNums.Z,
  forall s : sequence a154,
  Coq.Init.Logic.and (le (0)%Z i) (lt i (length s)) ->
  Coq.Init.Logic.eq (seq_get (rev s) i) (
    seq_get s (minus (minus (length s) (1)%Z) i)
  ).

Parameter fold :
  forall {a : Type},
  forall {b : Type},
  forall {_Ga : GospelType a},
  forall {_Gb : GospelType b},
  (a -> b -> a) -> a -> sequence b -> a.

Axiom fold_empty :
  forall {a159 : Type},
  forall {a160 : Type},
  forall {_Ga159 : GospelType a159},
  forall {_Ga160 : GospelType a160},
  forall f : a160 -> a159 -> a160,
  forall acc : a160,
  Coq.Init.Logic.eq (fold f acc (@empty a159 _Ga159)) acc.

Axiom fold_cons :
  forall {a171 : Type},
  forall {a172 : Type},
  forall {_Ga171 : GospelType a171},
  forall {_Ga172 : GospelType a172},
  forall f : a172 -> a171 -> a172,
  forall acc : a172,
  forall x : a171,
  forall l : sequence a171,
  Coq.Init.Logic.eq (fold f acc (cons x l)) (fold f (f acc x) l).

Axiom extensionality :
  forall {a182 : Type},
  forall {_Ga182 : GospelType a182},
  forall s1 : sequence a182,
  forall s2 : sequence a182,
  Coq.Init.Logic.eq (length s1) (length s2) ->
  (
    forall i : Coq.Numbers.BinNums.Z,
    Coq.Init.Logic.and (le (0)%Z i) (lt i (length s1)) ->
    Coq.Init.Logic.eq (seq_get s1 i) (seq_get s2 i)
  ) ->
  Coq.Init.Logic.eq s1 s2.

Parameter of_list :
  forall {a : Type},
  forall {_Ga : GospelType a},
  list a -> sequence a.

Parameter fold_left :
  forall {a : Type},
  forall {b : Type},
  forall {_Ga : GospelType a},
  forall {_Gb : GospelType b},
  (a -> b -> a) -> a -> sequence b -> a.

Parameter fold_right :
  forall {a : Type},
  forall {b : Type},
  forall {_Ga : GospelType a},
  forall {_Gb : GospelType b},
  (b -> a -> a) -> sequence b -> a -> a.

End Sequence.

Module Bag.

Parameter t : Type -> Type.

Parameter Bag :
  forall {a : Type},
  forall {_Ga : OCamlType a},
  t a -> t a -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter multiplicity :
  forall {a : Type},
  forall {_Ga : GospelType a},
  a -> bag a -> Coq.Numbers.BinNums.Z.

Axiom well_formed :
  forall {a186 : Type},
  forall {_Ga186 : GospelType a186},
  forall b : a186,
  forall x : bag a186,
  ge (multiplicity b x) (0)%Z.

Parameter empty : forall {a : Type}, forall {_Ga : GospelType a}, bag a.

Axiom empty_mult :
  forall {a189 : Type},
  forall {_Ga189 : GospelType a189},
  forall x : a189,
  Coq.Init.Logic.eq (multiplicity x (@empty a189 _Ga189)) (0)%Z.

Parameter init :
  forall {a : Type},
  forall {_Ga : GospelType a},
  (a -> Coq.Numbers.BinNums.Z) -> bag a.

Axiom init_axiom :
  forall {a195 : Type},
  forall {_Ga195 : GospelType a195},
  forall f : a195 -> Coq.Numbers.BinNums.Z,
  forall x : a195,
  Coq.Init.Logic.eq (max (0)%Z (f x)) (multiplicity x (init f)).

Parameter add :
  forall {a : Type},
  forall {_Ga : GospelType a},
  a -> bag a -> bag a.

Axiom add_mult_x :
  forall {a201 : Type},
  forall {_Ga201 : GospelType a201},
  forall b : bag a201,
  forall x : a201,
  Coq.Init.Logic.eq (multiplicity x (add x b)) (
    plus (1)%Z (multiplicity x b)
  ).

Axiom add_mult_neg_x :
  forall {a209 : Type},
  forall {_Ga209 : GospelType a209},
  forall x : a209,
  forall y : a209,
  forall b : bag a209,
  Coq.Init.Logic.not (Coq.Init.Logic.eq x y) ->
  Coq.Init.Logic.eq (multiplicity y (add x b)) (multiplicity y b).

Definition singleton  { a : Type } { _Ga : GospelType a } (x : a) : bag a:=
add x (@empty a _Ga).

Definition mem  { a : Type } { _Ga : GospelType a } (x : a) (b : bag a) : Prop:=
gt (multiplicity x b) (0)%Z.

Parameter remove :
  forall {a : Type},
  forall {_Ga : GospelType a},
  a -> bag a -> bag a.

Axiom remove_mult_x :
  forall {a218 : Type},
  forall {_Ga218 : GospelType a218},
  forall b : bag a218,
  forall x : a218,
  Coq.Init.Logic.eq (multiplicity x (remove x b)) (
    max (0)%Z (minus (multiplicity x b) (1)%Z)
  ).

Axiom remove_mult_neg_x :
  forall {a226 : Type},
  forall {_Ga226 : GospelType a226},
  forall x : a226,
  forall y : a226,
  forall b : bag a226,
  Coq.Init.Logic.not (Coq.Init.Logic.eq x y) ->
  Coq.Init.Logic.eq (multiplicity y (remove x b)) (multiplicity y b).

Parameter union :
  forall {a : Type},
  forall {_Ga : GospelType a},
  bag a -> bag a -> bag a.

Axiom union_all :
  forall {a234 : Type},
  forall {_Ga234 : GospelType a234},
  forall b : bag a234,
  forall b' : bag a234,
  forall x : a234,
  Coq.Init.Logic.eq (max (multiplicity x b) (multiplicity x b')) (
    multiplicity x (union b b')
  ).

Parameter sum :
  forall {a : Type},
  forall {_Ga : GospelType a},
  bag a -> bag a -> bag a.

Axiom sum_all :
  forall {a242 : Type},
  forall {_Ga242 : GospelType a242},
  forall b : bag a242,
  forall b' : bag a242,
  forall x : a242,
  Coq.Init.Logic.eq (plus (multiplicity x b) (multiplicity x b')) (
    multiplicity x (sum b b')
  ).

Parameter inter :
  forall {a : Type},
  forall {_Ga : GospelType a},
  bag a -> bag a -> bag a.

Axiom inter_all :
  forall {a250 : Type},
  forall {_Ga250 : GospelType a250},
  forall b : bag a250,
  forall b' : bag a250,
  forall x : a250,
  Coq.Init.Logic.eq (min (multiplicity x b) (multiplicity x b')) (
    multiplicity x (inter b b')
  ).

Parameter diff :
  forall {a : Type},
  forall {_Ga : GospelType a},
  bag a -> bag a -> bag a.

Axiom diff_all :
  forall {a258 : Type},
  forall {_Ga258 : GospelType a258},
  forall b : bag a258,
  forall b' : bag a258,
  forall x : a258,
  Coq.Init.Logic.eq (
    max (0)%Z (minus (multiplicity x b) (multiplicity x b'))
  ) (multiplicity x (diff b b')).

Definition disjoint  { a : Type } { _Ga : GospelType a } (b : bag a) (
  b' : bag a
) : Prop:=
forall x : a,
mem x b -> Coq.Init.Logic.not (mem x b').

Definition subset  { a : Type } { _Ga : GospelType a } (b : bag a) (
  b' : bag a
) : Prop:=
forall x : a,
le (multiplicity x b) (multiplicity x b').

Parameter filter :
  forall {a : Type},
  forall {_Ga : GospelType a},
  (a -> Prop) -> bag a -> bag a.

Axiom filter_mem :
  forall {a272 : Type},
  forall {_Ga272 : GospelType a272},
  forall b : bag a272,
  forall x : a272,
  forall f : a272 -> bool,
  f x ->
  Coq.Init.Logic.eq (multiplicity x (filter f b)) (multiplicity x b).

Axiom filter_mem_neg :
  forall {a279 : Type},
  forall {_Ga279 : GospelType a279},
  forall b : bag a279,
  forall x : a279,
  forall f : a279 -> bool,
  Coq.Init.Logic.not (f x) ->
  Coq.Init.Logic.eq (multiplicity x (filter f b)) (0)%Z.

Parameter cardinal :
  forall {a : Type},
  forall {_Ga : GospelType a},
  bag a -> Coq.Numbers.BinNums.Z.

Definition finite  { a : Type } { _Ga : GospelType a } (b : bag a) : Prop:=
Coq.Init.Logic.ex (
  fun s : sequence a =>
  forall x : a,
  mem x b -> Sequence.mem x s
).

Axiom card_nonneg :
  forall {a286 : Type},
  forall {_Ga286 : GospelType a286},
  forall b : bag a286,
  ge (cardinal b) (0)%Z.

Axiom card_empty :
  forall {a288 : Type},
  forall {_Ga288 : GospelType a288},
  Coq.Init.Logic.eq (cardinal (@empty a288 _Ga288)) (0)%Z.

Axiom card_singleton :
  forall {a292 : Type},
  forall {_Ga292 : GospelType a292},
  forall x : a292,
  Coq.Init.Logic.eq (cardinal (singleton x)) (1)%Z.

Axiom card_union :
  forall {a301 : Type},
  forall {_Ga301 : GospelType a301},
  forall b1 : bag a301,
  forall b2 : bag a301,
  finite b1 ->
  finite b2 ->
  Coq.Init.Logic.eq (cardinal (union b1 b2)) (
    plus (cardinal b1) (cardinal b2)
  ).

Axiom card_add :
  forall {a308 : Type},
  forall {_Ga308 : GospelType a308},
  forall x : a308,
  forall b : bag a308,
  finite b ->
  Coq.Init.Logic.eq (cardinal (add x b)) (plus (cardinal b) (1)%Z).

Axiom card_map :
  forall {a315 : Type},
  forall {_Ga315 : GospelType a315},
  forall f : a315 -> bool,
  forall b : bag a315,
  finite b -> le (cardinal (filter f b)) (cardinal b).

Parameter of_seq :
  forall {a : Type},
  forall {_Ga : GospelType a},
  sequence a -> bag a.

Axiom of_seq_multiplicity :
  forall {a320 : Type},
  forall {_Ga320 : GospelType a320},
  forall s : sequence a320,
  forall x : a320,
  Coq.Init.Logic.eq (Sequence.multiplicity x s) (
    multiplicity x (of_seq s)
  ).

End Bag.

Parameter set_create :
  forall {a : Type},
  forall {_Ga : GospelType a},
  set a.

Module _Set.

Parameter t : Type -> Type.

Parameter _Set :
  forall {a : Type},
  forall {_Ga : OCamlType a},
  t a -> t a -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter mem :
  forall {a : Type},
  forall {_Ga : GospelType a},
  a -> set a -> Prop.

Parameter empty : forall {a : Type}, forall {_Ga : GospelType a}, set a.

Axiom empty_mem :
  forall {a324 : Type},
  forall {_Ga324 : GospelType a324},
  forall x : a324,
  Coq.Init.Logic.not (mem x (@empty a324 _Ga324)).

Parameter add :
  forall {a : Type},
  forall {_Ga : GospelType a},
  a -> set a -> set a.

Axiom add_mem :
  forall {a328 : Type},
  forall {_Ga328 : GospelType a328},
  forall s : set a328,
  forall x : a328,
  mem x (add x s).

Axiom add_mem_neq :
  forall {a335 : Type},
  forall {_Ga335 : GospelType a335},
  forall s : set a335,
  forall x : a335,
  forall y : a335,
  Coq.Init.Logic.not (Coq.Init.Logic.eq x y) ->
  Coq.Init.Logic.iff (mem x s) (mem x (add y s)).

Definition singleton  { a : Type } { _Ga : GospelType a } (x : a) : set a:=
add x (@empty a _Ga).

Parameter remove :
  forall {a : Type},
  forall {_Ga : GospelType a},
  a -> set a -> set a.

Axiom remove_mem :
  forall {a341 : Type},
  forall {_Ga341 : GospelType a341},
  forall s : set a341,
  forall x : a341,
  Coq.Init.Logic.not (mem x (remove x s)).

Axiom remove_mem_neq :
  forall {a348 : Type},
  forall {_Ga348 : GospelType a348},
  forall s : set a348,
  forall x : a348,
  forall y : a348,
  Coq.Init.Logic.not (Coq.Init.Logic.eq x y) ->
  Coq.Init.Logic.iff (mem x s) (mem x (remove y s)).

Parameter union :
  forall {a : Type},
  forall {_Ga : GospelType a},
  set a -> set a -> set a.

Axiom union_mem :
  forall {a355 : Type},
  forall {_Ga355 : GospelType a355},
  forall s : set a355,
  forall s' : set a355,
  forall x : a355,
  Coq.Init.Logic.or (mem x s) (mem x s') -> mem x (union s s').

Axiom union_mem_neg :
  forall {a362 : Type},
  forall {_Ga362 : GospelType a362},
  forall s : set a362,
  forall s' : set a362,
  forall x : a362,
  Coq.Init.Logic.not (mem x s) ->
  Coq.Init.Logic.not (mem x s') -> Coq.Init.Logic.not (mem x (union s s')).

Parameter inter :
  forall {a : Type},
  forall {_Ga : GospelType a},
  set a -> set a -> set a.

Axiom inter_mem :
  forall {a369 : Type},
  forall {_Ga369 : GospelType a369},
  forall s : set a369,
  forall s' : set a369,
  forall x : a369,
  mem x s -> mem x s' -> mem x (inter s s').

Axiom inter_mem_neq :
  forall {a376 : Type},
  forall {_Ga376 : GospelType a376},
  forall s : set a376,
  forall s' : set a376,
  forall x : a376,
  Coq.Init.Logic.not (Coq.Init.Logic.or (mem x s) (mem x s')) ->
  Coq.Init.Logic.not (mem x (inter s s')).

Definition disjoint  { a : Type } { _Ga : GospelType a } (s : set a) (
  s' : set a
) : Prop:=
Coq.Init.Logic.eq (inter s s') (@empty a _Ga).

Parameter diff :
  forall {a : Type},
  forall {_Ga : GospelType a},
  set a -> set a -> set a.

Axiom diff_mem :
  forall {a385 : Type},
  forall {_Ga385 : GospelType a385},
  forall s : set a385,
  forall s' : set a385,
  forall x : a385,
  mem x s' -> Coq.Init.Logic.not (mem x (diff s s')).

Axiom diff_mem_fst :
  forall {a392 : Type},
  forall {_Ga392 : GospelType a392},
  forall s : set a392,
  forall s' : set a392,
  forall x : a392,
  Coq.Init.Logic.not (mem x s') ->
  Coq.Init.Logic.iff (mem x s) (mem x (diff s s')).

Definition subset  { a : Type } { _Ga : GospelType a } (s : set a) (
  s' : set a
) : Prop:=
forall x : a,
mem x s -> mem x s'.

Parameter map :
  forall {a : Type},
  forall {b : Type},
  forall {_Ga : GospelType a},
  forall {_Gb : GospelType b},
  (a -> b) -> set a -> set b.

Axiom set_map :
  forall {a404 : Type},
  forall {a405 : Type},
  forall {_Ga404 : GospelType a404},
  forall {_Ga405 : GospelType a405},
  forall f : a405 -> a404,
  forall s : set a405,
  forall x : a404,
  Coq.Init.Logic.iff (mem x (map f s)) (
    Coq.Init.Logic.ex (
      fun y : a405 =>
      Coq.Init.Logic.and (Coq.Init.Logic.eq (f y) x) (mem y s)
    )
  ).

Parameter cardinal :
  forall {a : Type},
  forall {_Ga : GospelType a},
  set a -> Coq.Numbers.BinNums.Z.

Definition finite  { a : Type } { _Ga : GospelType a } (s : set a) : Prop:=
Coq.Init.Logic.ex (
  fun seq : sequence a =>
  forall x : a,
  mem x s -> Sequence.mem x seq
).

Axiom cardinal_nonneg :
  forall {a411 : Type},
  forall {_Ga411 : GospelType a411},
  forall s : set a411,
  ge (cardinal s) (0)%Z.

Axiom cardinal_empty :
  forall {a413 : Type},
  forall {_Ga413 : GospelType a413},
  Coq.Init.Logic.eq (cardinal (@empty a413 _Ga413)) (0)%Z.

Axiom cardinal_remove :
  forall {a425 : Type},
  forall {_Ga425 : GospelType a425},
  forall s : set a425,
  forall x : a425,
  finite s ->
  (
    if classicT (mem x s) then
      Coq.Init.Logic.eq (cardinal (remove x s)) (minus (cardinal s) (1)%Z)
      else
    Coq.Init.Logic.eq (cardinal (remove x s)) (cardinal s)
  ).

Axiom cardinal_add :
  forall {a437 : Type},
  forall {_Ga437 : GospelType a437},
  forall s : set a437,
  forall x : a437,
  finite s ->
  (
    if classicT (mem x s) then
      Coq.Init.Logic.eq (cardinal (add x s)) (cardinal s)
      else
    Coq.Init.Logic.eq (cardinal (add x s)) (plus (cardinal s) (1)%Z)
  ).

Parameter of_seq :
  forall {a : Type},
  forall {_Ga : GospelType a},
  sequence a -> set a.

Axiom of_seq_set :
  forall {a443 : Type},
  forall {_Ga443 : GospelType a443},
  forall x : a443,
  forall s : sequence a443,
  Coq.Init.Logic.iff (Sequence.mem x s) (mem x (of_seq s)).

Parameter fold :
  forall {a : Type},
  forall {b : Type},
  forall {_Ga : GospelType a},
  forall {_Gb : GospelType b},
  (a -> b -> b) -> set a -> b -> b.

End _Set.

Module Map.

Parameter t : Type -> Type -> Type.

Parameter Map :
  forall {a : Type},
  forall {b : Type},
  forall {_Ga : OCamlType a},
  forall {_Gb : OCamlType b},
  t a b -> t a b -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter domain :
  forall {a : Type},
  forall {b : Type},
  forall {_Ga : GospelType a},
  forall {_Gb : GospelType b},
  b -> (a -> b) -> set a.

Axiom domain_mem :
  forall {a450 : Type},
  forall {a451 : Type},
  forall {_Ga450 : GospelType a450},
  forall {_Ga451 : GospelType a451},
  forall x : a451,
  forall m : a451 -> a450,
  forall default : a450,
  Coq.Init.Logic.not (Coq.Init.Logic.eq (m x) default) ->
  _Set.mem x (domain default m).

End Map.

Module Array.

Parameter get :
  forall {a : Type},
  forall {_Ga : GospelType a},
  array a -> Coq.Numbers.BinNums.Z -> a.

Parameter length :
  forall {a : Type},
  forall {_Ga : GospelType a},
  array a -> Coq.Numbers.BinNums.Z.

Parameter to_seq :
  forall {a : Type},
  forall {_Ga : GospelType a},
  array a -> sequence a.

Parameter permut :
  forall {a : Type},
  forall {_Ga : GospelType a},
  array a -> array a -> Prop.

Parameter permut_sub :
  forall {a : Type},
  forall {_Ga : GospelType a},
  array a ->
  array a -> Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z -> Prop.

End Array.

Module List.

Parameter fold_left :
  forall {a : Type},
  forall {b : Type},
  forall {_Ga : GospelType a},
  forall {_Gb : GospelType b},
  (b -> a -> b) -> b -> list a -> b.

Parameter _exists :
  forall {a : Type},
  forall {_Ga : GospelType a},
  (a -> Prop) -> list a -> Prop.

Parameter length :
  forall {a : Type},
  forall {_Ga : GospelType a},
  list a -> Coq.Numbers.BinNums.Z.

Parameter nth :
  forall {a : Type},
  forall {_Ga : GospelType a},
  list a -> Coq.Numbers.BinNums.Z -> a.

Parameter mem :
  forall {a : Type},
  forall {_Ga : GospelType a},
  a -> list a -> Prop.

Parameter map :
  forall {a : Type},
  forall {b : Type},
  forall {_Ga : GospelType a},
  forall {_Gb : GospelType b},
  (a -> b) -> list a -> list b.

End List.

Module Order.

Parameter is_pre_order :
  forall {a : Type},
  forall {_Ga : GospelType a},
  (a -> a -> int) -> Prop.

End Order.

Parameter ref : Type -> Type.

Parameter Ref :
  forall {a : Type},
  forall {_Ga : OCamlType a},
  ref a -> ref a -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter _UNUSED :
  forall {a : Type},
  forall {_Ga : GospelType a},
  ref a -> a.

Parameter logand :
  Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z -> Coq.Numbers.BinNums.Z.

Parameter integer_of_int : int -> Coq.Numbers.BinNums.Z.

End Stdlib.


