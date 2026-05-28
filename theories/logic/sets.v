(* This file offers a few lemmas and tactics about sets. *)

(* We do not need much, because [stdpp] offers most of what we need, and its
   [set_solver] tactic is excellent. *)

From stdpp Require Import sets propset.
Local Notation set := propset.
From marble.logic Require Import lists.

(* -------------------------------------------------------------------------- *)

(* A few generic lemmas. *)

(* If there is a decision procedure for [P]
   and if [P] is equivalent to [Q]
   then there is a decision procedure for [Q]. *)

Lemma Decision_consequence P Q :
  Decision P → (P ↔ Q) → Decision Q.
Proof.
  unfold Decision. tauto.
Qed.

(* Provided equality of elements is decidable,
   membership in a finite set is decidable. *)

Lemma Decision_membership_in_finite_set
  `{SemiSet A C, EqDecision A}
  (xs : list A) (c : C) :
  list_to_set xs ≡ c →
  ∀ x, Decision (x ∈ c).
Proof.
  intros Heq x.
  eapply Decision_consequence with (P := x ∈ xs).
  { eauto with typeclass_instances. }
  { set_solver. }
Qed.

(* If the list [xs] is a prefix of the list [ys]
   then [xs] forms a subset of [ys]. *)

Lemma prefix_list_to_set `{SemiSet A C} (xs ys : list A) :
  xs `prefix_of` ys →
  list_to_set xs ⊆ (list_to_set ys : C).
Proof.
  unfold prefix. intros (xs' & ->). set_solver.
Qed.

(* -------------------------------------------------------------------------- *)

(* We could parameterize the following lemmas with suitable type classes:
   [SemiSet], [Set_], [TopSet], so that they work with several kinds of
   sets. However, the lemmas would then have more premises and would require
   the use of [eauto with typeclass_instances], which I find painful. For
   the moment, I prefer to stick with one concrete kind of sets. *)

(* Basic lemmas. *)

Section Sets.

Context {V : Type}.

Implicit Types vs ws zs : set V.

Lemma prove_subset vs ws : (∀ v, v ∈ vs → v ∈ ws) → vs ⊆ ws.
Proof. set_solver. Qed.

Lemma prove_equiv vs ws : (∀ v, v ∈ vs ↔ v ∈ ws) → vs ≡ ws.
Proof. set_solver. Qed.

Lemma prove_disjoint vs ws : (∀ v, v ∈ vs → v ∈ ws → False) → vs ## ws.
Proof. set_solver. Qed.

Lemma subset_transitive vs ws zs :
  vs ⊆ ws → ws ⊆ zs → vs ⊆ zs.
Proof. set_solver. Qed.

Lemma subset_antisymmetric vs ws :
  vs ⊆ ws → ws ⊆ vs → vs ≡ ws.
Proof. set_solver. Qed.

Lemma prove_subset_empty_left vs : ∅ ⊆ vs.
Proof. set_solver. Qed.

Lemma prove_subset_union_left vs1 vs2 ws :
  vs1 ⊆ ws -> vs2 ⊆ ws -> vs1 ∪ vs2 ⊆ ws.
Proof. set_solver. Qed.

(* Set union is associative. *)

Lemma union_assoc vs ws zs :
  vs ∪ (ws ∪ zs) ≡ vs ∪ ws ∪ zs.
Proof. set_solver. Qed.

(* Currently unused, but kept for the record. *)
Lemma prove_subset_union_diff `{!RelDecision (∈@{set V})} vs ws :
  vs ⊆ (vs ∖ ws) ∪ ws.
Proof. rewrite difference_union. set_solver. Qed.

Lemma prove_subset_intersection_right vs vs1 vs2 :
  vs ⊆ vs1 -> vs ⊆ vs2 -> vs ⊆ vs1 ∩ vs2.
Proof. set_solver. Qed.

Lemma double_complement `{!RelDecision (∈@{set V})} vs :
  ⊤ ∖ (⊤ ∖ vs) ≡ vs.
Proof.
  rewrite difference_difference_r. set_solver.
Qed.

(* [cardinal vs n] means that the cardinal of the set [vs] is at most [n]. *)

Definition cardinal vs (n : Z) :=
  ∃ (enum : list V),
  length enum ≤ Z.to_nat n ∧
  ∀ v, v ∈ vs → v ∈ enum.

Local Ltac introCardinal enum :=
  exists enum; split; eauto.

Local Ltac elimCardinal :=
  match goal with h: cardinal _ _ |- _ =>
    destruct h as (enum & ? & Hmem)
  end.

(* The empty set has cardinal 0. *)

Lemma cardinal_empty vs :
  vs ⊆ ∅ →
  cardinal vs 0.
Proof.
  exists []. eauto with set_solver.
Qed.

(* Only the empty set has cardinal 0. *)

Lemma cardinal_empty_rev vs :
  cardinal vs 0 →
  vs ⊆ ∅.
Proof.
  intros. elimCardinal.
  assert (enum = []) as ->.
  { apply nil_length_inv. lia. }
  eauto with set_solver.
Qed.

Lemma cardinal_empty_iff vs :
  cardinal vs 0 ↔
  vs ⊆ ∅.
Proof.
  split; eauto using cardinal_empty, cardinal_empty_rev.
Qed.

(* If a set is nonempty then it cannot have cardinal 0. *)

Lemma cardinal_empty_contradiction v vs :
  cardinal vs 0 →
  v ∈ vs →
  False.
Proof.
  rewrite cardinal_empty_iff. set_solver.
Qed.

(* If a set has cardinal at most [n]
   then a subset of it has cardinal at most [n]. *)

Lemma cardinal_mono_1 vs ws n :
  cardinal ws n →
  vs ⊆ ws →
  cardinal vs n.
Proof.
  intros. elimCardinal. introCardinal enum.
Qed.

(* If a set has cardinal at most [n]
   then a strict subset of it has cardinal at most [n-1]. *)

Lemma cardinal_mono_1_strict `{EqDecision V} vs ws n w :
  cardinal ws n →
  vs ⊆ ws →
  w ∉ vs →
  w ∈ ws →
  cardinal vs (n - 1).
Proof.
  intros. elimCardinal.
  introCardinal (filter (λ x, x ≠ w) enum).
  { assert (Hw1: w ∈ enum) by eauto.
    assert (Hw2: ¬ w ≠ w) by congruence.
    generalize (length_filter_lt (λ x, x ≠ w) enum w Hw1 Hw2); intro.
    lia. }
  { intros. rewrite list_elem_of_filter. eauto with set_solver. }
Qed.

End Sets.

Hint Rewrite
  @union_assoc
: sets.

(* -------------------------------------------------------------------------- *)

(* The tactic [elem] and its variant simplify [x ∈ e], where [e] is a set
   expression. *)

Hint Rewrite
  @elem_of_PropSet
  @not_elem_of_PropSet
  @elem_of_empty
  @elem_of_singleton
  @elem_of_difference
  @elem_of_union
  @elem_of_intersection
  using eauto with typeclass_instances
: elem_of.

Ltac elem :=
  autorewrite with elem_of.

Tactic Notation "elem" "in" hyp(h) :=
  autorewrite with elem_of in h.

Tactic Notation "elem" "in" "*" :=
  autorewrite with elem_of in *.

(* -------------------------------------------------------------------------- *)

(* Conversion of a list to a set. *)

Lemma list_to_set_singleton `{SemiSet A C} (x : A) :
  list_to_set {[x]} ≡ ({[x]} : C).
Proof. simpl. set_solver. Qed.

Lemma list_to_set_rev `{SemiSet A C} (xs : list A) :
  list_to_set (rev xs) ≡ (list_to_set xs : C).
Proof.
  induction xs; simpl; intros.
  + eauto.
  + rewrite list_to_set_app, IHxs. simpl. set_solver.
Qed.

Hint Rewrite
  @list_to_set_nil
  @list_to_set_singleton
  @list_to_set_app
  @list_to_set_rev
  using eauto with typeclass_instances
: list_to_set.
