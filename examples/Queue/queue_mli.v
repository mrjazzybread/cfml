Require Import Gospel.CFML.base queue_ml.

From EXAMPLES Require Primitives.

Local Open Scope comp_scope.

Require Import
  Stdlib.Floats.Floats
  Stdlib.ZArith.BinIntDef
  Stdlib.Strings.Ascii.

Require Import
  CFML.SepBase
  CFML.SepLifted
  CFML.WPLib
  CFML.WPLifted
  CFML.WPRecord
  CFML.WPArray
  CFML.WPBuiltin
  CFML.Semantics
  CFML.WPHeader.

Module Declarations.

  Module Primitives := Primitives.

  Import Primitives.

  Import Sequence.

  Class _T_sig  := {
    T :
      forall {A}, forall `{Enc A}, (sequence val) -> (t_ A) -> hprop
  }.

  Class _create__sig  := { create_ : val }.

  Class _create__spec_sig `{@_create__sig} `{@_T_sig}  := {
    create__spec :
      forall {A}, forall `{Enc A}, forall `{Inhab A}, SPEC(create_  tt )
      PRE \[]
      POST(fun q_ : t_ A=> q_ ~> T empty )
  }.

End Declarations.

Module Type Obligations.

  Import Declarations.

  (* Lens T *)

  Global Declare Instance _T_inst : _T_sig.

  (* Program Value create_ *)

  Global Declare Instance _create__inst : _create__sig.

  (* Separation Logic Triple create__spec *)

  Global Declare Instance _create__spec_inst : _create__spec_sig.

End Obligations.