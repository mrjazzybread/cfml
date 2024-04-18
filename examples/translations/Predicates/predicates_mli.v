Set Implicit Arguments.

Require Import Gospel.

Require Coq.ZArith.BinInt TLC.LibLogic TLC.LibRelation TLC.LibInt TLC.LibListZ.

Require Import CFML.SepBase CFML.SepLifted CFML.WPLib CFML.WPLifted CFML.WPRecord CFML.WPArray CFML.WPBuiltin.

Require CFML.Stdlib.Array_ml CFML.Stdlib.List_ml CFML.Stdlib.Sys_ml.

Require Import Coq.ZArith.BinIntDef CFML.Semantics CFML.WPHeader.

Delimit Scope Z_scope with Z.

Parameter ho :
  (Coq.Numbers.BinNums.Z -> Prop) -> Coq.Numbers.BinNums.Z -> Prop.

Parameter fo : Coq.Numbers.BinNums.Z -> Prop.

Definition test  (n : Coq.Numbers.BinNums.Z) : Prop:= ho fo n.

Definition eq  (b1 : Prop) (b2 : Prop) : Prop:=
  Coq.Init.Logic.iff b1 b2.

Definition eq_strange  (b1 : Prop) (b2 : Prop) : Prop:=
  (if classicT (test (0)%Z) then Coq.Init.Logic.eq else eq) b1 b2.

Definition flip  (b : Prop) : Prop:=
  match Gospel.bool_of_prop b with
  | true => Coq.Init.Logic.True
  | false => Coq.Init.Logic.True
  end.


