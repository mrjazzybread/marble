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

(* [intuition eauto] can eliminate disjunctions, which is sometimes
   handy. However, it tends to destructure the goal even when it is
   unable to solve it, which is inconvenient. Hence we wrap it with
   [try solve]. Furthermore, in some cases, [intuition eauto] fails
   whereas [eauto] succeeds. Therefore [intuition eauto] should not
   be the default tactic. *)

Ltac itc :=
  try solve [ intuition eauto with typeclass_instances lia ].

(* The tactic [really replace i with e] replaces [i] with [e] in
   the goal, and fails if this replacement is trivial, that is,
   if [i] and [e] are identical. This can be a good thing, as it
   can cause backtracking higher up. *)

Tactic Notation "really" "replace" constr(i) "with" constr(e) :=
  let eq := fresh in
  assert (eq: i = e) by eauto with lia;
  rewrite eq; (* [rewrite eq] fails if [eq] is trivial *)
  clear eq.

Tactic Notation "really" "replace" constr(i) "with" constr(e) "in" hyp(h) :=
  let eq := fresh in
  assert (eq: i = e) by eauto with lia;
  rewrite eq in h;
  clear eq.

Tactic Notation "really" "replace" constr(i) "with" constr(e) "in" "*" :=
  let eq := fresh in
  assert (eq: i = e) by eauto with lia;
  rewrite eq in *;
  clear eq.

(* The tactic [reckon e], where [e] has type [nat], searches for
   a subexpression [e'] in the goal that is provably equal to [e]
   and replaces it with [e]. *)

(* The tactics [reckon e in h] and [reckon e in *] are similar,
   but act inside the hypothesis [h] or inside all hypotheses. *)

(* This offers a poor man's way of simplifying arithmetic expressions.
   As long as you are able to spell out the result of the desired
   simplification step, simplification will succeed. *)

Tactic Notation "reckon" constr(e) :=
  match goal with |- context[?i] =>
  match type of i with nat =>
    really replace i with e
  end end.

Tactic Notation "reckon" constr(e) "in" hyp(h) :=
  match type of h with context[?i] =>
  match type of i with nat =>
    really replace i with e in h
  end end.

Tactic Notation "reckon" constr(e) "in" "*" :=
  match goal with h: context[?i] |- _ =>
  match type of i with nat =>
    really replace i with e in *
  end end.
