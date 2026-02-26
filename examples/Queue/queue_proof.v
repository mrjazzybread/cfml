Require Import Gospel.CFML.base queue_ml queue_mli.

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

Module Proofs : Obligations.

  Import Declarations.

  Import queue_ml.

  Declare Instance Enc_cell_ (A : Type) : Enc (cell_ A).

  Hint Constructors cell_ : typeclass_instances.

  Global Instance _T_inst : _T_sig :=
    { T := fun A _ (m : list val) l =>
             match m with
             |nil => l ~> Record `{length' := 0; first' := Nil; last' := Nil}
             |_ => \[True] end}.

  Global Instance _create__inst : _create__sig :=
    { create_ := create }.

  #[refine] Global Instance _create__spec_inst : _create__spec_sig := { }.
  Proof.
    intros.
    simpl.
    xcf.
    applys xapp_lemma_record_new.
    intros.
    xsimpl.


End Proofs.
