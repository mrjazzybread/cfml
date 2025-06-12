Set Implicit Arguments.

Require Import Gospelstdlib_verified.

Import Gospelstdlib.

Require Coq.ZArith.BinInt TLC.LibLogic TLC.LibRelation TLC.LibInt TLC.LibListZ.

Require Import CFML.SepBase CFML.SepLifted CFML.WPLib CFML.WPLifted CFML.WPRecord CFML.WPArray CFML.WPBuiltin.

Require CFML.Stdlib.Array_ml CFML.Stdlib.List_ml CFML.Stdlib.Sys_ml.

Require Import Coq.ZArith.BinIntDef CFML.Semantics CFML.WPHeader.

Delimit Scope Z_scope with Z.

Parameter name : Type.

Instance __Inhab_name : Inhab name. Admitted.

Instance __Enc_name : Enc name. Admitted.

Parameter Name : name -> name -> hprop.

Parameter Gen : _Set.t name -> loc -> hprop.

Parameter _create : val.

Parameter _create_spec :
  SPEC(_create tt)
  PRE\[]
  POST(fun _prog_g : loc => (_prog_g ~> Gen _Set.empty)).

Parameter _next : val.

Parameter _next_spec :
  forall _prog_g : loc,
  forall g : _Set.t name,
  SPEC(_next _prog_g)
  PRE((_prog_g ~> Gen g))
  POST(
    fun _prog_n : name =>
    \exists n : name,
    ((_prog_g ~> Gen (_Set.add n g)) \* (_prog_n ~> Name n))
  ).

Parameter _reset : val.

Parameter _reset_spec :
  forall _prog_g : loc,
  forall g : _Set.t name,
  SPEC(_reset _prog_g)
  PRE((_prog_g ~> Gen g))
  POST(fun _ : unit => (_prog_g ~> Gen _Set.empty)).
