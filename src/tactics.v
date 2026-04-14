From Stdlib Require Import ZArith Lia.
From stdpp Require Import base numbers.
From marble Require Export equations.

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

(* The tactics [tc] perform type class search and can solve arithmetic
   side conditions. They either solve the goal or leave it untouched. *)

(* We use the hint database [marble]. *)

(* We use [nocore], which disables the hint database [core], because we
   do not want a goal such as [0 ≤ ?i < n] to be solved in a trivial way
   by instantiating [i] with 0. *)

Ltac tc0 := try lia.
Ltac tc1 := eauto 1 with typeclass_instances marble nocore.
Ltac tc2 := eauto 2 with typeclass_instances marble nocore.
Ltac tc3 := eauto 3 with typeclass_instances marble nocore.
Ltac tc4 := eauto 4 with typeclass_instances marble nocore.
Ltac tc5 := eauto 5 with typeclass_instances marble nocore.
Ltac tc6 := eauto 6 with typeclass_instances marble nocore.
Ltac tc7 := eauto 7 with typeclass_instances marble nocore.

Ltac tc  := tc5.

(* The tactics [idtc] are similar to [tc], but they use iterative deepening.
   This helps avoid suboptimal proofs that contain leftover uninstantiated
   metavariables. *)

(* One might expect the iterative deepening tactics to be faster than their
   normal counterparts, because they avoid needlessly deep searches. This is
   not the case: because [lia] can be called at every node, and can cost 0.5
   second, iterative deepening is in fact costly. *)

(* The semantics of the semicolon in Ltac is obscure. Assuming that the
   tactic [foo] either solves the goal or leaves it untouched, one would
   expect that [try solve [foo]] is equivalent to [foo]; yet, when [foo]
   is a composite tactic (a semicolon), I have observed that this is not
   true. In our setting, when there are several goals (e.g., several
   preconditions) that we wish to solve, we want iterative deepening to
   be applied to each goal in turn, NOT to all goals simultaneously,
   because we want correct metavariable instantiations to flow from one
   goal to the next goal. The use of [try solve] below is meant to
   ensure this. *)

Ltac idtc0 := try lia.
Ltac idtc1 := try solve [idtc0; tc1].
Ltac idtc2 := try solve [idtc1; tc2].
Ltac idtc3 := try solve [idtc2; tc3].
Ltac idtc4 := try solve [idtc3; tc4].
Ltac idtc5 := try solve [idtc4; tc5].
Ltac idtc6 := try solve [idtc5; tc6].
Ltac idtc7 := try solve [idtc6; tc7].

(* Populate the hint database [marble]. *)

Create HintDb marble.

(* We would like to avoid trying [lia] at every step of the proof without
   regard for the shape of the goal. We would like to be more selective and
   invoke [lia] only if the goal is an arithmetic goal. On the other hand,
   descending very deep before invoking [lia] can be counter-productive, as
   it can require the user to invoke [eauto] with a large search depth. So,
   for the moment, we keep invoking [lia] everywhere. *)

Hint Extern 1 => lia : marble.

(* Decompose the basic logical connectives: truth, conjunction, disjunction,
   and existential quantification. We need these rules because we want to
   work with [nocore]. The core database contains these rules. *)

Local Lemma true_intro : True.
Proof. tauto. Qed.

Hint Resolve true_intro conj or_introl or_intror ex_intro : marble.

(* This hint about equality at an arbitrary type seems safe. *)

Hint Resolve eq_refl : marble.

(* Tests. *)

Open Scope Z_scope.

Goal ∀ x y : Z, x + y - x = y.
Proof. eauto with marble nocore. Qed.

Goal ∀ x y : Z, x < x + 1.
Proof. eauto with marble nocore. Qed.

Goal ∀ x y : Z, x ≠ x + 1.
Proof. eauto with marble nocore. Qed.

Goal ∀ x y : Z, x ≤ x + 1 < x + 2.
Proof. eauto with marble nocore. Qed.

Goal ∀ x y : Z, x ≤ x + 1 ∨ x + 1 ≤ x.
Proof. eauto with marble nocore. Qed.

Goal ∀ x y : Z, x + 1 ≤ x ∨ x ≤ x + 1.
Proof. eauto with marble nocore. Qed.

Goal ∀ x y : Z, ¬ (x ≤ x + 1 < x).
Proof. eauto with marble nocore. Qed.

Goal ∀ x y : Z, ¬ ¬ (x ≤ y → x ≤ y + 1).
Proof. eauto with marble nocore. Qed.

Goal ∀ x y : Z, x ≤ y + 1 → ∃ z, x ≤ z ∧ y < z.
Proof. eauto with marble nocore. Qed.

(* Instruct Equations to kill proof obligations using [tc]. *)

Global Obligation Tactic :=
  simpl in *;
  Tactics.program_simplify;
  CoreTactics.equations_simpl;
  try Tactics.program_solve_wf;
  tc.
