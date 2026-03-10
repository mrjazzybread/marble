From stdpp Require Import base.
From Equations Require Import Equations.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

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

(* [intuition eauto] can eliminate disjunctions, which is sometimes
   handy. However, it tends to destructure the goal even when it is
   unable to solve it, which is inconvenient. Hence we wrap it with
   [try solve]. Furthermore, in some cases, [intuition eauto] fails
   whereas [eauto] succeeds. Therefore [intuition eauto] should not
   be the default tactic. *)

Ltac itc :=
  try solve [ intuition eauto with typeclass_instances lia ].

(* [cleanup] removes an equality hypothesis that is produced by
   [funelim] and that is usually unneeded. *)
Ltac cleanup :=
  match goal with h: sigmaI _ _ _ = sigmaI _ _ _ |- _ =>
    clear h
  end.
