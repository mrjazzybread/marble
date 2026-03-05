From stdpp Require Import base.
From Equations Require Import Equations.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

(* [tc] is a short name for type class search. *)

(* We use [lia] as a helper for arithmetic side conditions. *)

Ltac tc :=
  eauto with typeclass_instances lia.

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

(* [unpack_in] destructs conjunctions in the hypothesis [h]. *)
Ltac unpack_in h :=
  match type of h with
  | _ ∧ _ =>
      destruct h as [ ? h ];
      unpack_in h
  | ∃ x, _ =>
      destruct h as [ ? h ];
      unpack_in h
  | _ =>
      idtac
  end.

Global Tactic Notation "unpack" "in" hyp(h) :=
  unpack_in h.
