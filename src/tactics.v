From Stdlib Require Import Lia.
From stdpp Require Import base.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

(* This file defines a small number of tactics that I find useful. *)

(* [unpack] destructs conjunctions and existential quantifiers in all
   hypotheses. It could be called [unpack in *]. *)

Ltac unpack :=
  repeat match goal with
  | h: _ ∧ _ |- _ =>
      let h' := fresh h in
      destruct h as (h & h')
  | h: ∃ x, _ |- _ =>
      destruct h
  end.

(* [unpack in h] destructs conjunctions and existential quantifiers
   in the hypothesis [h]. This can give rise to multiple hypotheses,
   which are named after [h] in a somewhat predictable way. *)

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

Tactic Notation "unpack" "in" hyp(h) :=
  unpack_in h.

(* [pack] introduces conjunctions and quantifiers in the goal. *)

Ltac pack :=
  repeat match goal with
  | |- ∀ x, _ =>
      intro
  | |- _ ∧ _ =>
      split
  | |- ∃ x, _ =>
      eexists
  end.

(* [tc3] and [tc] are short names for type class search. *)

(* We use [lia] as a helper for arithmetic side conditions. *)

Ltac tc3 :=
  eauto 3 with typeclass_instances lia.

Ltac tc :=
  eauto 6 with typeclass_instances lia.
