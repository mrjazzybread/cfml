Set Implicit Arguments.

Require Coq.ZArith.BinInt TLC.LibLogic TLC.LibRelation TLC.LibInt TLC.LibListZ.

Require Import CFML.SepBase CFML.SepLifted CFML.WPLib CFML.WPLifted CFML.WPRecord CFML.WPArray CFML.WPBuiltin.

Require CFML.Stdlib.Array_ml CFML.Stdlib.List_ml CFML.Stdlib.Sys_ml.

Require Import Coq.ZArith.BinIntDef CFML.Semantics CFML.WPHeader.

Delimit Scope Z_scope with Z.

Module Type Stdlib.

Parameter sequence : Type -> Type.

Parameter bag : Type -> Type.

Parameter ref : Type -> Type.

Parameter set : Type -> Type.

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

Parameter logand : Z -> Z -> Z.

Parameter logor : Z -> Z -> Z.

Parameter logxor : Z -> Z -> Z.

Parameter lognot : Z -> Z.

Parameter shift_left : Z -> Z -> Z.

Parameter shift_right : Z -> Z -> Z.

Parameter shift_right_trunc : Z -> Z -> Z.

Parameter integer_of_int : int -> Z.

Parameter max_int : Z.

Parameter min_int : Z.

Parameter fst :
  forall {a : Type},
  forall {b : Type},
  forall {Ih_a : Inhab a},
  forall {Ih_b : Inhab b},
  tuple2 a b -> a.

Parameter snd :
  forall {a : Type},
  forall {b : Type},
  forall {Ih_a : Inhab a},
  forall {Ih_b : Inhab b},
  tuple2 a b -> b.

Parameter _UNUSED :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  ref a -> a.

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

Module Sequence.

Parameter t : Type -> Type.

Parameter length :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  sequence a -> Z.

Parameter empty :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  sequence a.

Parameter singleton :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  a -> sequence a.

Parameter init :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  Z -> (Z -> a) -> sequence a.

Parameter cons :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  a -> sequence a -> sequence a.

Parameter snoc :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  sequence a -> a -> sequence a.

Parameter hd :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  sequence a -> a.

Parameter tl :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  sequence a -> sequence a.

Parameter append :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  sequence a -> sequence a -> sequence a.

Parameter mem :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  sequence a -> a -> Prop.

Parameter map :
  forall {a : Type},
  forall {b : Type},
  forall {Ih_a : Inhab a},
  forall {Ih_b : Inhab b},
  (a -> b) -> sequence a -> sequence b.

Parameter filter :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  (a -> Prop) -> sequence a -> sequence a.

Parameter filter_map :
  forall {a : Type},
  forall {b : Type},
  forall {Ih_a : Inhab a},
  forall {Ih_b : Inhab b},
  (a -> option b) -> sequence a -> sequence b.

Parameter get :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  sequence a -> Z -> a.

Parameter set :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  sequence a -> Z -> a -> sequence a.

Parameter rev :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  sequence a -> sequence a.

Parameter fold_left :
  forall {b : Type},
  forall {a : Type},
  forall {Ih_b : Inhab b},
  forall {Ih_a : Inhab a},
  (a -> b -> a) -> a -> sequence b -> a.

Parameter fold_right :
  forall {a : Type},
  forall {b : Type},
  forall {Ih_a : Inhab a},
  forall {Ih_b : Inhab b},
  (a -> b -> b) -> sequence a -> b -> b.

End Sequence.

Module List.

Parameter t : Type -> Type.

Parameter length :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  list a -> Z.

Parameter hd : forall {a : Type}, forall {Ih_a : Inhab a}, list a -> a.

Parameter tl :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  list a -> list a.

Parameter nth :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  list a -> Z -> a.

Parameter nth_opt :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  list a -> Z -> option a.

Parameter rev :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  list a -> list a.

Parameter init :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  Z -> (Z -> a) -> list a.

Parameter map :
  forall {a : Type},
  forall {b : Type},
  forall {Ih_a : Inhab a},
  forall {Ih_b : Inhab b},
  (a -> b) -> list a -> list b.

Parameter mapi :
  forall {a : Type},
  forall {b : Type},
  forall {Ih_a : Inhab a},
  forall {Ih_b : Inhab b},
  (Z -> a -> b) -> list a -> list b.

Parameter fold_left :
  forall {b : Type},
  forall {a : Type},
  forall {Ih_b : Inhab b},
  forall {Ih_a : Inhab a},
  (a -> b -> a) -> a -> list b -> a.

Parameter fold_right :
  forall {b : Type},
  forall {a : Type},
  forall {Ih_b : Inhab b},
  forall {Ih_a : Inhab a},
  (b -> a -> a) -> list b -> a -> a.

Parameter map2 :
  forall {b : Type},
  forall {c : Type},
  forall {a : Type},
  forall {Ih_b : Inhab b},
  forall {Ih_c : Inhab c},
  forall {Ih_a : Inhab a},
  (a -> b -> c) -> list a -> list b -> list c.

Parameter for_all :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  (a -> Prop) -> list a -> Prop.

Parameter _exists :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  (a -> Prop) -> list a -> Prop.

Parameter for_all2 :
  forall {a : Type},
  forall {b : Type},
  forall {Ih_a : Inhab a},
  forall {Ih_b : Inhab b},
  (a -> b -> Prop) -> list a -> list b -> Prop.

Parameter _exists2 :
  forall {a : Type},
  forall {b : Type},
  forall {Ih_a : Inhab a},
  forall {Ih_b : Inhab b},
  (a -> b -> Prop) -> list a -> list b -> Prop.

Parameter mem :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  a -> list a -> Prop.

Parameter to_seq :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  list a -> sequence a.

Parameter of_seq :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  sequence a -> list a.

End List.

Module Array.

Parameter t : Type -> Type.

Parameter length :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  array a -> Z.

Parameter get :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  array a -> Z -> a.

Parameter make :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  Z -> a -> array a.

Parameter init :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  Z -> (Z -> a) -> array a.

Parameter append :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  array a -> array a -> array a.

Parameter concat :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  list (array a) -> array a.

Parameter sub :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  array a -> Z -> Z -> array a.

Parameter map :
  forall {a : Type},
  forall {b : Type},
  forall {Ih_a : Inhab a},
  forall {Ih_b : Inhab b},
  (a -> b) -> array a -> array b.

Parameter mapi :
  forall {a : Type},
  forall {b : Type},
  forall {Ih_a : Inhab a},
  forall {Ih_b : Inhab b},
  (Z -> a -> b) -> array a -> array b.

Parameter fold_left :
  forall {b : Type},
  forall {a : Type},
  forall {Ih_b : Inhab b},
  forall {Ih_a : Inhab a},
  (a -> b -> a) -> a -> array b -> a.

Parameter fold_right :
  forall {b : Type},
  forall {a : Type},
  forall {Ih_b : Inhab b},
  forall {Ih_a : Inhab a},
  (b -> a -> a) -> array b -> a -> a.

Parameter map2 :
  forall {b : Type},
  forall {c : Type},
  forall {a : Type},
  forall {Ih_b : Inhab b},
  forall {Ih_c : Inhab c},
  forall {Ih_a : Inhab a},
  (a -> b -> c) -> array a -> array b -> array c.

Parameter for_all :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  (a -> Prop) -> array a -> Prop.

Parameter _exists :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  (a -> Prop) -> array a -> Prop.

Parameter for_all2 :
  forall {a : Type},
  forall {b : Type},
  forall {Ih_a : Inhab a},
  forall {Ih_b : Inhab b},
  (a -> b -> Prop) -> array a -> array b -> Prop.

Parameter _exists2 :
  forall {a : Type},
  forall {b : Type},
  forall {Ih_a : Inhab a},
  forall {Ih_b : Inhab b},
  (a -> b -> Prop) -> array a -> array b -> Prop.

Parameter mem :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  a -> array a -> Prop.

Parameter to_list :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  array a -> list a.

Parameter of_list :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  list a -> array a.

Parameter to_seq :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  array a -> sequence a.

Parameter of_seq :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  sequence a -> array a.

Parameter to_bag :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  array a -> bag a.

Parameter permut :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  array a -> array a -> Prop.

Parameter permut_sub :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  array a -> array a -> Z -> Z -> Prop.

End Array.

Module Bag.

Parameter t : Type -> Type.

Parameter occurrences :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  a -> bag a -> Z.

Parameter empty : forall {a : Type}, forall {Ih_a : Inhab a}, bag a.

Parameter is_empty :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  bag a -> Prop.

Parameter mem :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  a -> bag a -> Prop.

Parameter add :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  a -> bag a -> bag a.

Parameter singleton :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  a -> bag a.

Parameter remove :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  a -> bag a -> bag a.

Parameter union :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  bag a -> bag a -> bag a.

Parameter sum :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  bag a -> bag a -> bag a.

Parameter inter :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  bag a -> bag a -> bag a.

Parameter disjoint :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  bag a -> bag a -> Prop.

Parameter diff :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  bag a -> bag a -> bag a.

Parameter subset :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  bag a -> bag a -> Prop.

Parameter choose :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  bag a -> a.

Parameter choose_opt :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  bag a -> option a.

Parameter map :
  forall {a : Type},
  forall {b : Type},
  forall {Ih_a : Inhab a},
  forall {Ih_b : Inhab b},
  (a -> b) -> bag a -> bag b.

Parameter fold :
  forall {a : Type},
  forall {b : Type},
  forall {Ih_a : Inhab a},
  forall {Ih_b : Inhab b},
  (a -> b -> b) -> bag a -> b -> b.

Parameter for_all :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  (a -> Prop) -> bag a -> Prop.

Parameter _exists :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  (a -> Prop) -> bag a -> Prop.

Parameter filter :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  (a -> Prop) -> bag a -> bag a.

Parameter filter_map :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  (a -> option a) -> bag a -> bag a.

Parameter partition :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  (a -> Prop) -> bag a -> tuple2 (bag a) (bag a).

Parameter cardinal :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  bag a -> Z.

Parameter to_list :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  bag a -> list a.

Parameter of_list :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  list a -> bag a.

Parameter to_seq :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  bag a -> sequence a.

Parameter of_seq :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  sequence a -> bag a.

End Bag.

Parameter set_create :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  set a.

Module _Set.

Parameter t : Type -> Type.

Parameter compare :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  set a -> set a -> Z.

Parameter empty : forall {a : Type}, forall {Ih_a : Inhab a}, set a.

Parameter is_empty :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  set a -> Prop.

Parameter mem :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  a -> set a -> Prop.

Parameter add :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  a -> set a -> set a.

Parameter singleton :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  a -> set a.

Parameter remove :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  a -> set a -> set a.

Parameter union :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  set a -> set a -> set a.

Parameter inter :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  set a -> set a -> set a.

Parameter disjoint :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  set a -> set a -> Prop.

Parameter diff :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  set a -> set a -> set a.

Parameter subset :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  set a -> set a -> Prop.

Parameter cardinal :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  set a -> Z.

Parameter choose :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  set a -> Z.

Parameter choose_opt :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  set a -> option a.

Parameter map :
  forall {a : Type},
  forall {b : Type},
  forall {Ih_a : Inhab a},
  forall {Ih_b : Inhab b},
  (a -> b) -> set a -> set b.

Parameter fold :
  forall {a : Type},
  forall {b : Type},
  forall {Ih_a : Inhab a},
  forall {Ih_b : Inhab b},
  (a -> b -> b) -> set a -> b -> b.

Parameter for_all :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  (a -> Prop) -> set a -> Prop.

Parameter _exists :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  (a -> Prop) -> set a -> Prop.

Parameter filter :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  (a -> Prop) -> set a -> set a.

Parameter filter_map :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  (a -> option a) -> set a -> set a.

Parameter partition :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  (a -> Prop) -> set a -> tuple2 (set a) (set a).

Parameter to_list :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  set a -> list a.

Parameter of_list :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  list a -> set a.

Parameter to_seq :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  set a -> sequence a.

Parameter of_seq :
  forall {a : Type},
  forall {Ih_a : Inhab a},
  sequence a -> set a.

End _Set.

Parameter map_set :
  forall {a : Type},
  forall {b : Type},
  forall {Ih_a : Inhab a},
  forall {Ih_b : Inhab b},
  (a -> b) -> a -> b -> a -> b.

Module Map.

End Map.

Module Order.

Definition is_pre_order  { a : Type } { Ih_a : Inhab a } (
  cmp : a -> a -> int
) : Prop:=
Coq.Init.Logic.and (forall x : a, eq (cmp x x) (0)%Z) (
  Coq.Init.Logic.and (
    forall x : a,
    forall y : a,
    Coq.Init.Logic.iff (le (cmp x y) (0)%Z) (ge (cmp y x) (0)%Z)
  ) (
    forall x : a,
    forall y : a,
    forall z : a,
    Coq.Init.Logic.and (
      le (cmp x y) (0)%Z -> le (cmp y z) (0)%Z -> le (cmp x z) (0)%Z
    ) (
      Coq.Init.Logic.and (
        le (cmp x y) (0)%Z -> lt (cmp y z) (0)%Z -> lt (cmp x z) (0)%Z
      ) (
        Coq.Init.Logic.and (
          lt (cmp x y) (0)%Z -> le (cmp y z) (0)%Z -> lt (cmp x z) (0)%Z
        ) (lt (cmp x y) (0)%Z -> lt (cmp y z) (0)%Z -> lt (cmp x z) (0)%Z)
      )
    )
  )
).

End Order.

Module Sys.

Parameter word_size : Z.

Parameter int_size : Z.

Parameter big_endian : Prop.

Parameter max_string_length : Z.

Parameter max_array_length : Z.

End Sys.

End Stdlib.


