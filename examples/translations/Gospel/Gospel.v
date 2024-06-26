Require TLC.LibLogic.
Require TLC.LibMap.
Require Import List.
Require Import TLC.LibInt.
Require TLC.LibSet.
Require Import CFML.SepBase CFML.SepLifted CFML.WPLib CFML.WPLifted CFML.WPRecord CFML.WPArray CFML.WPBuiltin.
(* Lists *)

Definition hd {A} {Inh:LibLogic.Inhab A} (l : list A) : A :=
  match l with
  |nil => TLC.LibLogic.arbitrary
  |x::_ => x
  end.

Lemma hd_inst :
  forall A (x : A) l (Inh : LibLogic.Inhab A), (hd (x::l)) = x.
Proof. auto. Qed.

Opaque hd.  

Definition tl {A} (l: list A) : list A :=
  match l with
  |nil => nil
  |_::t => t
  end.

Lemma tl_inst :
  forall A (x : A) l, tl (x::l) = l.
Proof. auto. Qed.

Opaque tl.

Definition singleton {A} (x : A) : list A := cons x nil.

Lemma singleton_inst :
  forall A (x : A), singleton x = cons x nil.
Proof. auto. Qed.

Opaque singleton.

Definition domain {A} {B} (e : B) (f: A -> B) : A -> Prop :=
  fun arg => f arg <> e.

Parameter update : forall {A} {B}, (A -> B) -> A -> B -> A -> B.

Axiom update_updated_key :
  forall A B (f : A -> B) k v, update f k v k = v.

Axiom update_other_keys :
  forall A B (f : A -> B) k1 k2 v, k1 <> k2 -> update f k1 v k2 = f k2.

Parameter word_size : Z.

Axiom word_size_values :
  word_size = 32 \/ word_size = 64.

Definition add_set {A} (x : A) (s : set A) : set A :=
  LibSet.union_impl s (LibSet.single_impl x).

Definition Int (i1: Z) (i2: Z) := \[i1 = i2].

Definition Option (o1: option int) (o2: option int) := \[o1 = o2].

Definition Bool (p:Prop) (b:bool) := \[is_true b <-> p].

Definition List (l1:list int) (l2: list int) := \[l1 = l2].

Definition Loc (l1:loc) (l2: loc) := \[l1=l2].

Fixpoint init_nat {A} (n : nat) (f : int -> A) : list A :=
  match n with
  |O => nil
  |S n' => (f n) :: (init_nat n' f)                     
  end.

Definition init {A} (n : int) (f : int -> A) : list A :=
  if n <=? 0 then arbitrary else
    init_nat (Z.to_nat n) f.

Definition bool_of_prop (P : Prop) : bool :=
  if classicT P then true else false.
