From stdpp Require Import base.
From Equations Require Import Equations.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

(* [cleanup] removes an equality hypothesis that is produced by
   [funelim] and that is usually unneeded. *)
Ltac cleanup :=
  match goal with h: sigmaI _ _ _ = sigmaI _ _ _ |- _ =>
    clear h
  end.

(* [unpack] destructs conjunctions in the hypotheses. *)
Ltac unpack :=
  repeat match goal with
  | h: _ ∧ _ |- _ =>
      destruct h
  | h: ∃ x, _ |- _ =>
      destruct h
  end.
