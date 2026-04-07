From Stdlib Require Import Lia.
From stdpp Require Import base.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

(* [unpack] destructs conjunctions in the hypotheses. *)
Ltac unpack :=
  repeat match goal with
  | h: _ ∧ _ |- _ =>
      let h' := fresh h in
      destruct h as (h & h')
  | h: ∃ x, _ |- _ =>
      destruct h
  end.

(* [unpack_in] destructs conjunctions in the hypothesis [h]. *)
Ltac unpack_in h :=
  match type of h with
  | _ ∧ _ =>
      let h' := fresh h in
      destruct h as [ h h' ];
      unpack_in h;
      unpack_in h'
  | ∃ x, _ =>
      destruct h as [ ? h ];
      unpack_in h
  | _ =>
      idtac
  end.

Global Tactic Notation "unpack" "in" hyp(h) :=
  unpack_in h.

(* [pack] introduces conjunctions and quantifiers in the goal.
   When introducing a hypothesis, it unpacks this hypothesis. *)
Ltac pack :=
  repeat match goal with
  | |- ∀ x, _ =>
      intro
  | |- _ ∧ _ =>
      split
  | |- ∃ x, _ =>
      eexists
  end.

(* [tc] is a short name for type class search. *)

(* We use [lia] as a helper for arithmetic side conditions. *)

(* TODO why does [typeclasses eauto] fail in situations where [eauto]
   succeeds? *)

Ltac tc :=
  eauto 6 with typeclass_instances lia.

Ltac tc3 :=
  eauto 3 with typeclass_instances lia.
