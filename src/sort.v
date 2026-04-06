From stdpp Require Import numbers list well_founded.
From listz Require Import listz.
Notation len := length.
From Stdlib Require Import Uint63.
From Stdlib Require Import Array.PArray.
From Stdlib Require Import Sorting.Permutation Sorting.Sorted.
From Corelib Require Import Classes.RelationClasses.
From marble Require Import equations.
From marble Require Import tactics list_tactics.
From marble Require Import iteration int wp wp_tactics array.
From marble Require Import orders sorting compare.
Implicit Types _i _j _k : int.

(* TODO *)
(* Local Ltac Zify.zify_pre_hook ::= arrays; lengths; ulength in *. *)

Local Ltac listz_arith ::= ulength; lia.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

(* Documentation:
   https://rocq-prover.org/doc/V9.1.0/corelib/Corelib.Classes.RelationClasses.html
   https://rocq-prover.org/doc/v9.0/stdlib/Stdlib.Sorting.Sorted.html
 *)

Local Ltac wp_intros_hook Hx ::=
  (* Simplify expressions that involve lists and arithmetic. *)
  list in Hx;
  (* Decompose existential quantifiers and conjunctions. *)
  unpack in Hx.

(* TODO *)
Local Ltac split_seg i xs :=
  rewrite (split_seg i xs) by lia.

(* -------------------------------------------------------------------------- *)

(* Local hints. *)

(* TODO the hints and tactics about sorting should be cleaned up and moved
   to sorting.v *)

(* TODO also equal_lookups_to_equal_segs *)
Ltac same_lookup_total :=
  match goal with
  | h: ?x = ?xs !!! ?i |- ?x = ?xs !!! ?j =>
      assert (i = j) by listz_arith;
      congruence
  | h: ?x = ?xs !!! ?i |- ?xs !!! ?j = ?x =>
      assert (i = j) by listz_arith;
      congruence
  | h: ?xs !!! ?i = ?x |- ?x = ?xs !!! ?j =>
      assert (i = j) by listz_arith;
      congruence
  | h: ?xs !!! ?i = ?x |- ?xs !!! ?j = ?x =>
      assert (i = j) by listz_arith;
      congruence
  end.

Ltac listz_easy ::=
  solve [ eauto 2 | same_lookup_total ].

(* When the goal has the form [?R ?lhs ?rhs], the tactic [derecognize]
   substitutes away [lhs] and [rhs], if they are variables, and
   substitutes away any variables that are known to be equal to
   [lhs] and [rhs]. It is used as a preparatory step in [related]. *)

(* Possibly one could adopt the opposite approach and use [recognize]
   as a preparatory step. *)

Global Ltac derecognize :=
  match goal with |- ?R ?lhs ?rhs =>
    try subst lhs; try subst rhs
  end;
  try match goal with h: ?x = ?lhs |- ?R ?lhs _ =>
    try subst x
  end;
  try match goal with h: ?y = ?rhs |- ?R _ ?rhs =>
    try subst y
  end.

(* [related] solves the goal or fails. *)

(* TODO combine [related] and [same_lookup_total]? *)
(* TODO may want to also use [exploit_sorted]? *)
Ltac related :=
  derecognize;
  match goal with

  | h: Sorted ?R (seg _ _?xs) |- ?R (?xs !!! ?i) (?xs !!! ?j) =>
      (* Two lookups may be related because they hit a sorted segment. *)
      eapply exploit_sorted_seg; [
        exact h
      | listz_arith | listz_arith | listz_arith | listz_arith | listz_arith ]

  | h: pairwise ?R (seg _ _ _) (seg _ _ _) |- ?R _ _ =>
      (* Two lookups may be related because they hit two related segments. *)
      eapply exploit_seg_pairwise_seg; [
        exact h | solve [eauto] | solve [eauto] | listz_arith | listz_arith ]

  | h: ?x ∈ seg _ _ _ |- ?R ?x ?y =>
      (* We want to relate [x] with [y] and we know that [x] is a member
         of a certain segment. This means that there exists an index [j]
         within a certain range such that [x] is [xs !!! j]. Perform this
         replacement and continue. *)
      rewrite lookup_total_elem_seg in h by listz_arith;
      destruct h as (? & ? & h);
      rewrite h;
      related

  | _ =>
      (* Perhaps other recipes are applicable. *)
      solve [ eauto 3 with related ]
  end.

(* [boundary] applies the lemma [boundary_test] to a goal of the form
   [Sorted R (xs ++ ys)]. It solves the first two subgoals and leaves
   the third subgoal, [xs ≼ ys], open. *)

Global Ltac boundary :=
  eapply boundary_test; [ sorted | sorted | length; intros ? ?; list ]

(* [sorted_app] applies the lemma [Sorted_app] to a goal of the form
   [Sorted R (xs ++ ys)]. It solves the first two subgoals and leaves
   the third subgoal, [xs ≼ ys], open. *)

with sorted_app :=
  eapply Sorted_app; [ sorted | sorted |]

(* [pw] solves a goal of the form [xs ⋅≼ ys]. *)

(* [pw] solves the goal or fails. *)

with pw :=
  match goal with (* can backtrack *)

  | |- pairwise _ [] _ =>
      (* One side is the empty list. Easy. *)
      eapply pairwise_nil_left
  | |- pairwise _ _ [] =>
      (* One side is the empty list. Easy. *)
      eapply pairwise_nil_right

  | |- pairwise _ {[_]} {[_]} =>
      (* Both sides are singletons. The goal is transformed into
         an obligation to prove [x < y]. *)
      rewrite pairwise_singleton_singleton_iff;
      related

  | h: pairwise _ {[?x]} ?zs |- pairwise _ {[?y]} ?zs =>
      (* The goal is identical to a hypothesis up to an equation [x = y]. *)
      replace y with x by eauto; exact h
  | h: pairwise _ ?zs {[?x]} |- pairwise _ ?zs {[?y]} =>
      (* The goal is identical to a hypothesis up to an equation [x = y]. *)
      replace y with x by eauto; exact h

  | h: pairwise _ (seg _ _ _) (seg _ _ _) |-
       pairwise _ (seg _ _ _) (seg _ _ _) =>
      (* To prove that two segments are related, it suffices to show that
         are subsegments of segments which we know are related. *)
      eapply seg_pairwise_seg_variance;
        [ exact h | listz_arith | listz_arith | listz_arith | listz_arith ]

  | |- pairwise ?R ?xs ?ys =>
      (* If the lists [xs] and [ys] are sorted, then, to prove [xs ≼ ys],
         it suffices to compare the two elements at the boundary test. *)
      solve [boundary; related]

  | |- pairwise _ _ (_ ++ _) =>
      (* Another option is to decompose concatenations. *)
      rewrite pairwise_app_right_iff; split; pw
  | |- pairwise _ (_ ++ _) _ =>
      rewrite pairwise_app_left_iff; split; pw

  | _ =>
      (* An assumption? *)
      solve [ eauto 2 ]
  end

(* [sorted] solves the goal or fails. *)

with sorted :=
  match goal with
  | |- Sorted _ [] =>
      (* The empty list is sorted. *)
      eapply Sorted_empty
  | |- Sorted _ {[_]} =>
      (* A singleton list is sorted. *)
      eapply Sorted_singleton
  | h: Sorted ?R ?xs |- Sorted ?R ?xs =>
      (* Exploiting an assumption. *)
      exact h
  | h: Sorted ?R (?xs ++ _) |- Sorted ?R ?xs =>
      (* A part of a sorted list is sorted. *)
      eapply Sorted_app_inv_l; [ exact h ]
  | h: Sorted ?R (_ ++ ?xs) |- Sorted ?R ?xs =>
      (* A part of a sorted list is sorted. *)
      eapply Sorted_app_inv_r; [ exact h ]
  | h: Sorted _ (seg _ _ ?xs) |- Sorted _ (seg _ _?xs) =>
      (* A subsegment of a sorted segment is sorted. *)
      eapply sorted_seg_variance; [ exact h | listz_arith | listz_arith ]
(* TODO
  | |- Sorted _ (?xs ++ {[?y]} ++ ?zs) =>
      (* The special case of two concatenations
         with a singleton in the middle. *)
      eapply Sorted_app_app; [ sorted | pw | pw ]
 *)
  | |- Sorted _ (?xs ++ ?zs) =>
      sorted_app; pw
  | h: Sorted ?R ?xs |- Sorted ?R ?ys =>
      (* Exploiting an assumption, up to an equality of lists. *)
      let Heq := fresh in
      assert (Heq: xs = ys); [ solve [lego] | rewrite Heq in h; exact h ]
  | _ =>
      (* An assumption? *)
      solve [eauto 2]
  end.

(* -------------------------------------------------------------------------- *)

(* Setup. *)

Section Sorting.

(* We assume that there is a preorder [R], also written [≤], on the type [A]. *)

(* We also assume that there is a two-way comparison function [leb]. *)

(* We do not need a three-way comparison function, so we do not request one.
   Using three-way comparisons would be wasteful, as Rocq would silently
   generate three-way branches where two branches are identical. *)

Context `{Inhabited A} `{PreOrder A R} `{LebSpec A R}.

Infix "≤?" := leb
  (at level 70, no associativity) : element_scope.

Implicit Types x y : A.

(* Standard mathematical notation. *)

Open Scope element_scope.

Infix "≤" := R
  (at level 70, no associativity) : element_scope.
Infix "<" := (strict R)
  (at level 70, no associativity) : element_scope.
Notation "y ≥ x" := (x ≤ y)
  (only parsing, at level 70, no associativity) : element_scope.
Notation "y > x" := (x < y)
  (only parsing, at level 70, no associativity) : element_scope.
Infix "≡" := (equivalent R)
  (at level 70, no associativity) : element_scope.

(* The following hints seem to be needed. I don't understand why
   reflexivity and transitivity do not work out of the box. *)

Local Lemma reflex_le x : x ≤ x.
Proof. intros. reflexivity. Qed.
Local Lemma trans_le x y z : x ≤ y → y ≤ z → x ≤ z.
Proof. intros. transitivity y; eauto. Qed.
Local Hint Resolve reflex_le trans_le : core.

Definition lt_le' := (@lt_le A R).
Local Hint Resolve lt_le' : core.

Lemma lt_equiv_lt x y z : x < y → y ≡ z → x < z.
Proof. unfold equivalent, strict. intros; unpack; split; eauto. Qed.
Lemma equiv_lt_lt x y z : x ≡ y → y < z → x < z.
Proof. unfold equivalent, strict. intros; unpack; split; eauto. Qed.
Local Hint Resolve lt_equiv_lt equiv_lt_lt : core.

(* We assume that there is a second preorder [R'] on the type [A]. *)

(* We write [x `precedes` y] for this preorder. We will assume that
   the input array is sorted with respect to this order. Therefore,
   intuitively, [x `precedes` y] means that [x] comes earlier than [y]
   in the input data. *)

(* We write [xs `precede` ys] when every element of [xs] precedes
   every element of [ys]. This means that the elements of [xs] come
   earlier than the elements of [ys] in the input data. *)

Context `{PreOrder A R'}.

Infix "`precedes`" := R'
  (at level 70, no associativity) : element_scope.
Infix "`precede`" := (pairwise R')
  (at level 70, no associativity) : element_scope.

(* We specialize this lemma so that [eauto] accepts to use it as a hint. *)

(* In combination with [le_le_lex], this lemma can exploit the hypotheses
   [seg i1 j1 xs1 `precede` seg i2 j2 xs2] and [x1 ≤ x2] so as to prove
   [x1 `lex` x2]. *)

Local Lemma exploit_seg_pairwise_seg i1 j1 xs1 i2 j2 xs2 x1 k1 x2 k2 :
  seg i1 j1 xs1 `precede` seg i2 j2 xs2 →
  x1 = xs1 !!! k1 →
  x2 = xs2 !!! k2 →
  i1 `max` 0 ≤ k1 < j1 `min` len xs1 →
  i2 `max` 0 ≤ k2 < j2 `min` len xs2 →
  x1 `precedes` x2.
Proof.
  intros. eapply exploit_seg_pairwise_seg; eauto.
Qed.

(* TODO still used? *)
Local Hint Resolve exploit_seg_pairwise_seg : related.

(* The following hints seem to be needed. I don't understand why
   reflexivity and transitivity do not work out of the box. *)

Local Lemma reflex_precedes x : x `precedes` x.
Proof. intros. reflexivity. Qed.
Local Lemma trans_precedes x y z : x `precedes` y → y `precedes` z → x `precedes` z.
Proof. intros. transitivity y; eauto. Qed.
Local Hint Resolve reflex_precedes trans_precedes : core.

(* [lex] is the lexicographic combination of the two preorders. *)

(* We do NOT use the following straightforward definition, because
   it involves a disjunction. This in turn entails the need for the
   law of excluded middle (or a hypothesis [RelDecision R]) in the
   proof of the statement: [x ≤ y → x `precedes` y → lex x y].

Local Definition lex x y :=
  x < y ∨
  x ≡ y ∧ x `precedes` y.
 *)

(* Instead, we use this definition: *)

Local Definition lex x y :=
  x ≤ y ∧ (y ≤ x → x `precedes` y).

Infix "`lex`" := lex
  (at level 70, no associativity).

Local Hint Unfold lex : core.

(* [lex] is a preorder. *)

Global Instance : PreOrder lex.
Proof.
  constructor; unfold lex.
  + intros x. eauto.
  + intros x y z. intuition eauto 8.
Qed.

(* Our definition of [lex] implies the usual definition. *)

Lemma lt_lex x y : x < y → x `lex` y.
Proof.
  split.
  + eauto.
  + intro. exfalso. unfold strict in *. tauto.
Qed.

Local Hint Resolve lt_lex : core.

Lemma le_le_lex x y : x ≤ y → x `precedes` y → x `lex` y.
Proof. eauto. Qed.

(* TODO still used? *)
Local Hint Resolve le_le_lex : related.
Local Hint Extern 1 (_ `precedes` _) => related : related.

(* [lex x y] implies [x ≤ y]. *)

Lemma lex_elim x y : x `lex` y → x ≤ y.
Proof. unfold lex. tauto. Qed.

(* We write [sorted xs] when the list [xs] is sorted with respect to [lex]. *)

(* We write [xs ≼ ys] when every element [x ∈ xs]
   and every element [y ∈ ys] satisfy [x ≤ y]. *)

Notation sorted xs   := (Sorted lex xs).
Notation "xs '≼' ys" := (pairwise lex xs ys) (at level 80).

(* We write [xs ≃ ys] when the lists [xs] and [ys] are equivalent up to
   a permutation of their elements. *)

Local Infix "≃" := (@Permutation A)
  (at level 70, no associativity).

(* Naming conventions. *)

Implicit Types _src _dst : array A.
Implicit Types src dst : list A.
Implicit Types _srcofs _dstofs _n : int.
Implicit Types srcofs dstofs n : Z.

(* -------------------------------------------------------------------------- *)

(* Handy lemmas about permutations. *)

Lemma perm_xys xs xs' ys ys' zs zs' :
  xs' ≃ xs →
  ys' ≃ ys →
  zs' ≃ zs →
  xs' ++ ys' ++ zs' ≃ xs ++ ys ++ zs.
Proof.
  intros Hxs Hys Hzs. rewrite Hxs, Hys, Hzs. reflexivity.
Qed.

Lemma perm_yxs xs xs' ys ys' zs zs' :
  xs' ≃ xs →
  ys' ≃ ys →
  zs' ≃ zs →
  ys' ++ xs' ++ zs' ≃ xs ++ ys ++ zs.
Proof.
  intros Hxs Hys Hzs. rewrite Hxs, Hys, Hzs.
  rewrite !app_assoc.
  eapply Permutation_app_tail.
  eapply Permutation_app_comm.
Qed.

(* -------------------------------------------------------------------------- *)

(* What can one do, at the leaves, to speed up a merge sort? Three approaches
   come to mind:
   1. Just use merge sort all the way down to size 0, 1, or 2.
   2. Below a certain threshold, use insertion sort. (OCaml does this.)
   3. Below a certain threshold, switch to a merge sort whose control
      structure has been statically precomputed.

   Our timings (in OCaml) suggest that approach 3 is very slightly faster
   than approach 2. In principle, compared with 1 and 2, approach 3 offers
   the advantage of performing fewer function calls and fewer array accesses.
   In Rocq, this could make it a winner. Plus, this is fun. *)

(* Below, we develop a merge sort with statically computed control flow,
   up to size 4. Our approach is manual: we write each function by hand,
   as opposed to writing a generator. This seems much easier and is good
   enough. *)

(* This exercice represents quite a lot of effort. It is probably not
   really worth the trouble, but it is instructive. *)

Local Definition lt_le_R   := @lt_le A R.
Local Definition lex_trans := @transitivity A lex _.

Local Hint Resolve
  lt_le_R
  lex_trans
  strict_transitive_l
  le_le_lex
  lex_elim
  Permutation_app_comm
  list_elem_of_here
  list_elem_of_further
: network.

Local Hint Extern 1 (_ ≃ _) =>
  match goal with h: _ ≃ _ |- _ => rewrite <- h end; econstructor
: network.

Local Hint Extern 1 (_ `precede` _) =>
  (autorewrite with pairwise in *; first [ tauto | repeat split; eauto ])
: network.

Local Ltac exploit :=
  eapply (@exploit_pairwise_singleton_left_permut A lex);
  eauto with network.
Local Ltac cons :=
  eapply pairwise_singleton_cons; eauto with network.
Local Ltac nil :=
  eapply pairwise_nil_right.

(* We write [merge] and [sort] functions in continuation-passing style:
   they take arguments in registers (variables) and pass results to a
   continuation via registers (variables). This lets us generate code in
   three layers: 1- a sequence of array reads; 2- a tree of conditionals;
   3- a sequence of array writes. *)

(* [merge11] merges two sorted sequences of 1 element each. The two
   elements are named [x0] and [y0]. The resulting sorted sequence is
   transmitted to the continuation [k], which expects two arguments.
   [merge12], [merge22], etc., are similar, with more arguments. *)

(* The preconditions of each [merge] function are as follows: 1- the
   elements of each sequence must be sorted with respect to [lex]; 2- the
   elements of the first sequence must precede the elements of the second
   sequence. *)

Definition merge11 {B} x0 y0 k : B :=
  if x0 ≤? y0 then
    k x0 y0
  else
    k y0 x0.

Lemma wp_merge11 {B} x0 y0 k (Q : B → Prop) :
  [x0] `precede` [y0] →
  (∀ z0 z1,
     z0 `lex` z1 →
     [x0] ++ [y0] ≃ [z0; z1] →
     wp (k z0 z1) Q
  ) →
  wp (merge11 x0 y0 k) Q.
Proof.
  intros. wp_last Hret. unfold merge11.
  wp_if; eapply Hret; eauto with network.
Qed.

Definition merge12 {B} x0 y0 y1 k : B :=
  if x0 ≤? y0 then
    k x0 y0 y1
  else
    merge11 x0 y1 (k y0).

Lemma wp_merge12 {B} x0 y0 y1 k (Q : B → Prop) :
  y0 `lex` y1 →
  [x0] `precede` [y0; y1] →
  (∀ z0 z1 z2,
     z0 `lex` z1 → z1 `lex` z2 →
     [x0] ++ [y0; y1] ≃ [z0; z1; z2] →
     wp (k z0 z1 z2) Q
  ) →
  wp (merge12 x0 y0 y1 k) Q.
Proof.
  intros. wp_last Hret. unfold merge12.
  wp_if.
  + eapply Hret; eauto with network.
  + eapply wp_merge11; eauto with network.
    simpl. intros. eapply Hret; eauto with network.
    exploit. cons. cons. nil.
Qed.

Definition merge13 {B} x0 y0 y1 y2 k : B :=
  if x0 ≤? y0 then
    k x0 y0 y1 y2
  else
    merge12 x0 y1 y2 (k y0).

Lemma wp_merge13 {B} x0 y0 y1 y2 k (Q : B → Prop) :
  y0 `lex` y1 → y1 `lex` y2 →
  [x0] `precede` [y0; y1; y2] →
  (∀ z0 z1 z2 z3,
     z0 `lex` z1 → z1 `lex` z2 → z2 `lex` z3 →
     [x0] ++ [y0; y1; y2] ≃ [z0; z1; z2; z3] →
     wp (k z0 z1 z2 z3) Q
  ) →
  wp (merge13 x0 y0 y1 y2 k) Q.
Proof.
  intros. wp_last Hret. unfold merge13.
  wp_if.
  + eapply Hret; eauto with network.
  + eapply wp_merge12; eauto with network.
    simpl. intros. eapply Hret; eauto with network.
    exploit. cons. cons. cons. nil.
Qed.

Definition merge21 {A} x0 x1 y0 k : A :=
  if x0 ≤? y0 then
    merge11 x1 y0 (k x0)
  else
    k y0 x0 x1.

Lemma wp_merge21 {B} x0 x1 y0 k (Q : B → Prop) :
  x0 `lex` x1 →
  [x0; x1] `precede` [y0] →
  (∀ z0 z1 z2,
     z0 `lex` z1 → z1 `lex` z2 →
     [x0; x1] ++ [y0] ≃ [z0; z1; z2] →
     wp (k z0 z1 z2) Q
  ) →
  wp (merge21 x0 x1 y0 k) Q.
Proof.
  intros. wp_last Hret. unfold merge21.
  wp_if.
  + eapply wp_merge11; eauto with network.
    simpl. intros. eapply Hret; eauto with network.
    exploit. cons. cons. nil.
  + eapply Hret; eauto with network.
Qed.

Definition merge22 {B} x0 x1 y0 y1 k : B :=
  if x0 ≤? y0 then
    merge12 x1 y0 y1 (k x0)
  else
    merge21 x0 x1 y1 (k y0).

Lemma wp_merge22 {B} x0 x1 y0 y1 k (Q : B → Prop) :
  x0 `lex` x1 → y0 `lex` y1 →
  [x0; x1] `precede` [y0; y1] →
  (∀ z0 z1 z2 z3,
     z0 `lex` z1 → z1 `lex` z2 → z2 `lex` z3 →
     [x0; x1] ++ [y0; y1] ≃ [z0; z1; z2; z3] →
     wp (k z0 z1 z2 z3) Q
  ) →
  wp (merge22 x0 x1 y0 y1 k) Q.
Proof.
  intros. wp_last Hret. unfold merge22.
  wp_if.
  + eapply wp_merge12; eauto with network. simpl. intros.
    eapply Hret; eauto with network.
    exploit. cons. cons. cons. nil.
  + eapply wp_merge21; eauto with network.
    simpl. intros. wp_last Hpermut.
    eapply Hret; eauto with network.
    - exploit. cons. cons. cons. nil.
    - rewrite <- Hpermut. simpl.
      (* Wow. We must manually exhibit a permutation. *)
      eapply perm_trans; [ | eapply perm_swap ].
      eapply perm_skip.
      eapply perm_trans; [ | eapply perm_swap ].
      eapply perm_skip.
      reflexivity.
Qed.

(* Equipped with these [merge] functions, we can write [sort] functions. *)

(* The input sequence must be sorted with respect to `precedes`, that is,
   [R']. Then, the output sequence is sorted with respect to [lex]. *)

Definition sort2 {A} x0 x1 k : A :=
  merge11 x0 x1 k.

Definition wp_sort2 :=
  @wp_merge11.

Definition sort3 {B} x0 x1 x2 k : B :=
  sort2 x0 x1 @@ λ x0 x1,
  merge21 x0 x1 x2 k.

Lemma wp_sort3 {B} x0 x1 x2 k (Q : B → Prop) :
  x0 `precedes` x1 →
  x1 `precedes` x2 →
  (∀ z0 z1 z2,
     z0 `lex` z1 → z1 `lex` z2 →
     [x0; x1; x2] ≃ [z0; z1; z2] →
     wp (k z0 z1 z2) Q
  ) →
  wp (sort3 x0 x1 x2 k) Q.
Proof.
  intros. wp_last Hret. unfold sort3.
  eapply wp_sort2; eauto with network. simpl. intros. wp_last Hpermut.
  eapply wp_merge21; eauto with network.
  rewrite <- Hpermut. eauto with network.
Qed.

Definition sort4 {B} x0 x1 x2 x3 k : B :=
  sort2 x0 x1 @@ λ x0 x1,
  sort2 x2 x3 @@ λ y0 y1,
  merge22 x0 x1 y0 y1 k.

Lemma wp_sort4 {B} x0 x1 x2 x3 k (Q : B → Prop) :
  x0 `precedes` x1 →
  x1 `precedes` x2 →
  x2 `precedes` x3 →
  (∀ z0 z1 z2 z3,
     z0 `lex` z1 → z1 `lex` z2 → z2 `lex` z3 →
     [x0; x1; x2; x3] ≃ [z0; z1; z2; z3] →
     wp (k z0 z1 z2 z3) Q
  ) →
  wp (sort4 x0 x1 x2 x3 k) Q.
Proof.
  intros. wp_last Hret. unfold sort4.
  eapply wp_sort2; eauto with network. simpl. intros. wp_last Hpermut1.
  eapply wp_sort2; eauto with network. simpl. intros. wp_last Hpermut2.
  eapply wp_merge22; eauto with network.
  rewrite <- Hpermut1, <- Hpermut2. eauto with network.
Qed.

(* There remains to wrap the sorting networks [sort2], [sort3], [sort4]
   within two layers of array accesses. *)

(* The "naive" versions use the [merge] and [sort] functions above and
   involve lots of continuations. Optimized versions of these functions
   are then obtained via compile-time computation. *)

Section S.
Open Scope uint63.

Definition naive_sortto_segment_2 _src _i _dst _k :=
  do x0 ← get _src _i ;
  do x1 ← get _src (_i + 1) ;
  sort2 x0 x1 @@ λ x0 x1,
  do _dst ← set _dst _k x0 ;
  do _dst ← set _dst (_k + 1) x1 ;
  _dst.

Definition naive_sortto_segment_3 _src _i _dst _k :=
  do x0 ← get _src _i ;
  do x1 ← get _src (_i + 1) ;
  do x2 ← get _src (_i + 2) ;
  sort3 x0 x1 x2 @@ λ x0 x1 x2,
  do _dst ← set _dst _k x0 ;
  do _dst ← set _dst (_k + 1) x1 ;
  do _dst ← set _dst (_k + 2) x2 ;
  _dst.

Definition naive_sortto_segment_4 _src _i _dst _k :=
  do x0 ← get _src _i ;
  do x1 ← get _src (_i + 1) ;
  do x2 ← get _src (_i + 2) ;
  do x3 ← get _src (_i + 3) ;
  sort4 x0 x1 x2 x3 @@ λ x0 x1 x2 x3,
  do _dst ← set _dst _k x0 ;
  do _dst ← set _dst (_k + 1) x1 ;
  do _dst ← set _dst (_k + 2) x2 ;
  do _dst ← set _dst (_k + 3) x3 ;
  _dst.

End S.

(* The optimized versions. *)

Definition sortto_segment_2 :=
  Eval compute -[bind leb] in naive_sortto_segment_2.

Definition sortto_segment_3 :=
  Eval compute -[bind leb] in naive_sortto_segment_3.

Definition sortto_segment_4 :=
  Eval compute -[bind leb] in naive_sortto_segment_4.

(* Disable Notation "t .[ i ]" := (get t i). *)
(* Disable Notation "t .[ i <- a ]" := (set t i a). *)
(* Print sortto_segment_2. *)
(* Print sortto_segment_3. *)
(* Print sortto_segment_4. *)

(* The specification of the [sortto_segment] functions. *)

(* In this specification, [_src] and [_dst] are the same array.
   Aliasing the parameters is not a problem here because all of
   the reads take place before all of the writes. *)

(* The array is unmodified outside of the segment [k, k+n). Within this
   segment, a sorted copy of the data that initially existed in the
   segment [i, i+n) is written. This is a stable sort. *)

Definition wp_sortto_segment_spec sortto_segment n :=
  ∀ a xs _i i _k k,
  isArray a xs →
  isInt _i i →
  isInt _k k →
  valid_seg i (i + n) xs →
  valid_seg k (k + n) xs →
  Sorted R' (seg i (i + n) xs) →
  wp (sortto_segment a _i a _k) (λ a, ∃ xs',
    isArray a xs' ∧
    len xs = len xs' ∧
    unmodified_outside_seg xs xs' k (k + n) ∧
    seg k (k + n) xs' ≃ seg i (i + n) xs ∧
    sorted (seg k (k + n) xs')
  ).

(* Each of these functions is correct. *)

Lemma wp_sortto_segment_2 :
  wp_sortto_segment_spec sortto_segment_2 2.
Proof.
  unfold wp_sortto_segment_spec. intros.
  change sortto_segment_2 with naive_sortto_segment_2.
  unfold naive_sortto_segment_2.
  wp_get x0. wp_get x1.
  eapply wp_sort2.
  { pw. }
  intros. wp_last Hpermut.
  repeat wp_set. wp_ret.
  eexists. pack; eauto 2; list; eauto 2.
  (* Permutation. *)
  + rewrite <- Hpermut. eapply identity_permutation. lego.
  (* Sortedness. *)
  + sorted.
Qed.

Lemma wp_sortto_segment_3 :
  wp_sortto_segment_spec sortto_segment_3 3.
Proof.
  unfold wp_sortto_segment_spec. intros.
  change sortto_segment_3 with naive_sortto_segment_3.
  unfold naive_sortto_segment_3.
  wp_get x0. wp_get x1. wp_get x2.
  eapply wp_sort3;
    try solve [ subst; eapply exploit_sorted_seg; eauto with lia ].
  intros. wp_last Hpermut.
  repeat wp_set. wp_ret.
  eexists. pack; eauto 2; list in *; eauto 2.
  (* Permutation. *)
  + rewrite <- Hpermut. eapply identity_permutation. lego.
  (* Sortedness. *)
  + sorted.
Qed.

Lemma wp_sortto_segment_4 :
  wp_sortto_segment_spec sortto_segment_4 4.
Proof.
  unfold wp_sortto_segment_spec. intros.
  change sortto_segment_4 with naive_sortto_segment_4.
  unfold naive_sortto_segment_4.
  wp_get x0. wp_get x1. wp_get x2. wp_get x3.
  eapply wp_sort4;
    try solve [ subst; eapply exploit_sorted_seg; eauto with lia ].
  intros. wp_last Hpermut.
  repeat wp_set. wp_ret.
  eexists. pack; eauto 2; list in *; eauto 2.
  (* Permutation. *)
  + rewrite <- Hpermut. eapply identity_permutation. lego.
  (* Sortedness. *)
  + sorted.
Qed.

(* -------------------------------------------------------------------------- *)

(* Insertion sort: [isortto]. *)

Section ISortTo.
Open Scope uint63.

(* [isortto src _srcofs dst _dstofs _n] sorts the array segment described
   by [src], [_srcofs], [_n]. The resulting data is written into the array
   segment described by [dst], [_dstofs], [_n]. The source and destination
   arrays must be distinct. This is a stable sort. *)

Definition isortto _src _srcofs _dst _dstofs _n :=
  (* Let [i] scan the source segment upwards. *)
  int.iter_up 0 _n _dst @@ λ _i _dst ,
    (* Extract [xi] at offset [i] in the source segment. *)
    do xi ← get _src (_srcofs + _i) ;
    do (_dst, out) ← (
      (* Let [j] scan the sorted part of the destination segment, downwards. *)
      int.xiter_down (_dstofs + _i) _dstofs _dst @@
      λ _ _j _dst continue break ,
        (* Read an element [xj] at offset [j] in the destination segment.
           If [xj ≥ xi] holds then move [xj] upwards by one position and
           continue. Otherwise stop. *)
        do xj ← get _dst _j ;
        if (xj ≤? xi)%element then
          break _dst _j
        else
          do _dst ← set _dst (_j + 1) xj ;
          continue _dst
    );
    (* Write [xi] into the logically empty slot of the array [dst]. *)
    match out with
    | Break _j =>
        set _dst (_j + 1) xi
    | Continue =>
        set _dst  _dstofs xi
    end.

End ISortTo.

(* This is the invariant of the main loop. *)

(* [src] is the content of the source array;
   [dst] is the initial content of the destination array;
   [dst']  is the final content of the destination array. *)

Definition isortto_inv src srcofs dst dstofs := λ i _dst,
  ∃ dst',
  isArray _dst dst' ∧
  len dst = len dst' ∧
  (* Outside of the destination segment,
     the destination array is unmodified. *)
  unmodified_outside_seg dst dst' dstofs (dstofs + i) ∧
  (* The data found inside the destination segment is a permutation
     of the data that existed in the source segment. *)
  seg dstofs (dstofs + i) dst' ≃ seg srcofs (srcofs + i) src ∧
  (* The destination segment is sorted. *)
  sorted (seg dstofs (dstofs + i) dst').

Local Ltac intro_isortto_inv :=
  unfold isortto_inv; pack; list; tc3; list; tc3.

Local Ltac elim_isortto_inv dst' :=
  match goal with h: isortto_inv _ _ _ _ _ _ |- _ =>
    destruct h as (dst' & ? & ? & Hunmodified & Hdata & Hsorted)
  end.

(* The destination invariant, [dst_inv ...], is a conjunction of three
   assertions. *)

(* When we speak of an "extended source segment", we mean a source segment
   that extends up to index [srcofs + (i + 1)] in the source array.
   Similarly, an "extended destination segment" extends up to index
   [dstofs + (i + 1)] in the destination array. *)

Local Definition dst_inv src srcofs dst dstofs i j :=
  let xi := src !!! (srcofs + i) in
  (* Assertion 1: permutation. *)
  (* The data found in the extended destination segment, once updated
     with [xi] at index [j], is a permutation of the data that existed
     in the extended source segment. *)
  seg dstofs j dst ++ {[xi]} ++ seg (j + 1) (dstofs + (i + 1)) dst ≃
  seg srcofs (srcofs + (i + 1)) src ∧
  (* Assertion 2: sortedness except at index [j]. *)
  (* The extended destination segment, deprived of the logically empty
     slot at index [j], is sorted. *)
  sorted (seg dstofs j dst ++ seg (j + 1) (dstofs + (i + 1)) dst) ∧
  (* Assertion 3: ordering above [xi]. *)
  (* Every element in the second part of the extended destination
     segment, following the logically empty slot at index [j], is
     (strictly) above [xi]. *)
  {[xi]} ≼ seg (j + 1) (dstofs + i + 1) dst.

Local Ltac intro_dst_inv :=
  split; [| split ]; cbv zeta; list.

Local Ltac elim_dst_inv :=
  match goal with h: dst_inv _ _ _ _ _ _ |- _ =>
    unfold dst_inv in h;
    destruct h as (Hpermut & Hsortedx & Habove);
    list in Hpermut; z in Hsortedx
  end.

(* This is the invariant of the inner loop. *)

(* This invariant holds both while the loop is running and once the loop
   has ended. If the loop is running, [out] is [Continue]; if the loop
   has ended, [out] indicates how it has ended. *)

Local Definition inner_inv src srcofs dst dstofs i := λ j _dst out,
  ∃ dst',
  isArray _dst dst' ∧
  len dst' = len dst ∧
  (* Outside of the extended destination segment,
     the destination array is unmodified. *)
  unmodified_outside_seg dst dst' dstofs (dstofs + i + 1) ∧
  (* The content of the extended destination segment is described by
     the destination invariant [dst_inv ...]. If [out] is [Continue]
     then the logically empty slot lies at index [j]; otherwise it lies
     at index [j + 1]. Furthermore, in the latter case, [xj `lex` xi]
     holds. *)
  match out with
  | Continue =>
      dst_inv src srcofs dst' dstofs i j
  | Break _j =>
      dst_inv src srcofs dst' dstofs i (j + 1) ∧
      let xi := src !!! (srcofs + i) in
      let xj := dst' !!! j in
      isInt _j j ∧ dstofs ≤ j < dstofs + i ∧
      xj `lex` xi
  end.

Local Ltac intro_inner_inv :=
  unfold inner_inv; pack; list; tc3; list; tc3.

Local Ltac elim_inner_inv dst' :=
  match goal with h: inner_inv _ _ _ _ _ _ _ _ |- _ =>
    destruct h as (dst' & h); cbv zeta in h; list in h; unpack in h
  end.

(* The public specification of [isortto]. *)

Lemma wp_isortto _src src _dst dst :
  isArray _src src →
  ∀Int _srcofs srcofs,
  isArray _dst dst →
  ∀Int _dstofs dstofs,
  ∀Int _n n,
  valid_seg srcofs (srcofs + n) src →
  valid_seg dstofs (dstofs + n) dst →
  Sorted R' (seg srcofs (srcofs + n) src) →
  wp (isortto _src _srcofs _dst _dstofs _n)
     (isortto_inv src srcofs dst dstofs n).
Proof.
  intros. unfold isortto. arrays.
  (* The outer loop. *)
  wp_iter_up (isortto_inv src srcofs dst dstofs).
  (* Initialization of the outer loop. *)
  { intro_isortto_inv. }
  (* The body of the outer loop. *)
  { clear dependent _dst. wp_up_intros i _dst. intros _i ?.
    elim_isortto_inv dst'.
    (* [dst'] is the content of the destination array
       upon entry into the body of the outer loop. *)
    wp_get xi.
    eapply wp_bind.
    { (* The inner loop. *)
      wp_xiter_down (inner_inv src srcofs dst dstofs i).
      (* Initialization of the inner loop. *)
      { intro_inner_inv. intro_dst_inv; [| sorted | pw ].
        + rewrite Hdata. join_segments. reflexivity. }
      (* The body of the inner loop. *)
      clear dependent _dst.
      (* TODO need variant of [wp_down_intros] *)
      wp_loop_intros j0 j _dst. intros. subst j0.
      elim_inner_inv dst''.
      (* [dst''] is the content of the destination array
         upon entry into the body of the inner loop. *)
      wp_get xj.
      wp_if.
      (* Case [xj ≤ xi]. *)
      { wp_break. intro_inner_inv. elim_dst_inv.
        + recognize.
          eapply le_le_lex; [ assumption |].
          (* Proving [xj `precedes` xi] is the slightly tricky part.
             The argument is that [xj] comes from the extended source
             segment, whose rightmost element is [xi]. This is the only
             point where stability creates an extra proof obligation. *)
          assert (Hseg: xj ∈ seg srcofs (srcofs + i + 1) src).
          { rewrite <- Hpermut. subst xj. eauto with elem_of_app lia. }
          related. }
      (* Case [xi < xj]. *)
      { elim_dst_inv.
        wp_set. wp_continue.
        intro_inner_inv. intro_dst_inv; [| sorted | pw ].
        (* Permutation. *)
        { rewrite <- Hpermut. clarify. (* TODO slow *)
          rewrite (split_seg j dst'' dstofs (j + 1)) by lia. clarify.
          recognize. eapply Permutation_app_comm. }}}
    (* Epilogue of the inner loop. *)
    { clear dependent _dst. intros [ _dst out ].
      intros (j&Hj). z in Hj. unpack in Hj.
      (* Perform a case analysis on [out], so as to separately analyze
         the case where the loop has been stopped early and the case
         where it has finished normally. *)
      destruct out as [ _j' |]; elim_inner_inv dst''; elim_dst_inv.
      (* Case: we have broken out. *)
      { wp_set.
        intro_isortto_inv;
        rewrite insert_seg by listz_arith; z; [| sorted ].
        (* Permutation. *)
        { rewrite <- Hpermut. recognize. reflexivity. }}
      (* Case: the loop has finished normally. *)
      { assert (j = dstofs) by tauto. subst j. list in Hpermut.
        wp_set.
        intro_isortto_inv; [| sorted ].
        (* Permutation. *)
        { rewrite <- Hpermut. recognize. reflexivity. }}}}
Qed.

(* -------------------------------------------------------------------------- *)

(* In-place insertion sort: [isortto']. *)

(* [isortto' a _srcofs _dstofs _n] sorts the array segment described
   by [a], [_srcofs], [_n]. The resulting data is written into the array
   segment described by [a], [_dstofs], [_n]. The source and destination
   arrays are the same array. This is a stable sort. *)

(* The code is the same as in [isortto] except that the two arrays [src]
   and [dst] are replaced with a single array [a]. *)

Definition isortto' a _srcofs _dstofs _n :=
  int.iter_up 0 _n a @@ λ _i a ,
    do xi ← get a (_srcofs + _i)%uint63 ;
    do (a, out) ← (
      int.xiter_down (_dstofs + _i)%uint63 _dstofs a @@
      λ _ _j a continue break ,
        do xj ← get a _j ;
        if (xj ≤? xi)%element then
          break a _j
        else
          do a ← set a (_j + 1) xj ;
          continue a
    );
    match out with
    | Break _j =>
        set a (_j + 1) xi
    | Continue =>
        set a _dstofs xi
    end.

(* This code requires the source and destination segments to either be
   disjoint or to possibly overlap in a configuration where the destination
   segment lies closer to the left end of the array than the source
   segment. The latter situation includes the case where the two segments
   coincide. In any of these situations case, the code is correct because
   [xi] is read before it is overwritten (if it is ever overwritten). In
   other words, when [xi] is read from the current array, the same value
   is read as if [xi] had been read from the initial unmodified array. *)

(* The public specification of [isortto']. *)

Lemma wp_isortto' a xs :
  isArray a xs →
  ∀Int _srcofs srcofs,
  ∀Int _dstofs dstofs,
  ∀Int _n n,
  valid_seg srcofs (srcofs + n) xs →
  valid_seg dstofs (dstofs + n) xs →
  (srcofs + n ≤ dstofs ∨ dstofs ≤ srcofs)%Z → (* disjoint or overlap *)
  Sorted R' (seg srcofs (srcofs + n) xs) →
  wp (isortto' a _srcofs _dstofs _n)
     (isortto_inv xs srcofs xs dstofs n).
Proof.
  intros. unfold isortto'. arrays.
  (* The outer loop. *)
  wp_iter_up (isortto_inv xs srcofs xs dstofs).
  (* Initialization of the outer loop. *)
  { intro_isortto_inv. }
  (* The body of the outer loop. *)
  { clear dependent a. wp_up_intros i a. intros _i ?.
    elim_isortto_inv xs'.
    (* [xs'] is the content of the array
       upon entry into the body of the outer loop. *)
    wp_get xi. wp_last Hxi.
    (* [xi] is the same value that would have been read out of the initial
       unmodified array. This is the key reason why the proof goes through
       with almost no change. This exploits [Hunmodified]. *)
    assert (KEY: xs' !!! (srcofs + i) = xs !!! (srcofs + i)).
    { eapply equal_lookups_to_equal_segs; eauto with lia. }
    rewrite KEY in Hxi; clear KEY.
    eapply wp_bind.
    { (* The inner loop. *)
      wp_xiter_down (inner_inv xs srcofs xs dstofs i).
      (* Initialization of the inner loop. *)
      { intro_inner_inv. intro_dst_inv; [| sorted | pw ].
        + rewrite Hdata. join_segments. reflexivity. }
      (* The body of the inner loop. *)
      clear dependent a.
      (* TODO need variant of [wp_down_intros] *)
      wp_loop_intros j0 j a. intros. subst j0.
      elim_inner_inv xs''.
      (* [xs''] is the content of the array
         upon entry into the body of the inner loop. *)
      wp_get xj.
      wp_if.
      (* Case [xj ≤ xi]. *)
      { wp_break. intro_inner_inv. elim_dst_inv.
        + recognize.
          eapply le_le_lex; [ assumption |].
          (* Proving [xj `precedes` xi] is the slightly tricky part.
             The argument is that [xj] comes from the extended source
             segment, whose rightmost element is [xi]. This is the only
             point where stability creates an extra proof obligation. *)
          assert (Hseg: xj ∈ seg srcofs (srcofs + i + 1) xs).
          { rewrite <- Hpermut. subst xj. eauto with elem_of_app lia. }
          related. }
      (* Case [xi < xj]. *)
      { elim_dst_inv.
        wp_set. wp_continue.
        intro_inner_inv. intro_dst_inv; [| sorted | pw ].
        (* Permutation. *)
        { rewrite <- Hpermut. clarify.
          rewrite (split_seg j xs'' dstofs (j + 1)) by lia. clarify.
          recognize. eapply Permutation_app_comm. }}}
    (* Epilogue of the inner loop. *)
    { clear dependent a. intros [ a out ].
      intros (j&Hj). z in Hj. unpack in Hj.
      (* Perform a case analysis on [out], so as to separately analyze
         the case where the loop has been stopped early and the case
         where it has finished normally. *)
      destruct out as [ _j' |]; elim_inner_inv dst''; elim_dst_inv.
      (* Case: we have broken out. *)
      { wp_set.
        intro_isortto_inv;
        rewrite insert_seg by listz_arith; z; [| sorted ].
        (* Permutation. *)
        { rewrite <- Hpermut. recognize. reflexivity. }}
      (* Case: the loop has finished normally. *)
      { assert (j = dstofs) by tauto. subst j. list in Hpermut.
        wp_set.
        intro_isortto_inv; [| sorted ].
        (* The destination segment contains a permitted permutation. *)
        { rewrite <- Hpermut. recognize. reflexivity. }}}}
Qed.

(* -------------------------------------------------------------------------- *)

(* The well-founded relation [order _j1 _j2] is used to justify the
   termination of [merge_aux] and of its variants. In short, either
   [_i1] increases without exceeding [_j1], while [_i2] remains
   unchanged; or, symmetrically, [_i2] increases without exceeding
   [_j2], while [_i1] remains unchanged. *)

Section MergeOrder.

Variable _j1 _j2 : int.

Local Definition order1 : relation (int * int) :=
  λ '(_i1, _i2) '(_i'1, _i'2),
  rigt _j1 _i1 _i'1 ∧ _i2 = _i'2.

Local Definition order2 : relation (int * int) :=
  λ '(_i1, _i2) '(_i'1, _i'2),
  _i1 = _i'1 ∧ rigt _j2 _i2 _i'2.

Local Definition order : relation (int * int) :=
  λ p p', order1 p p' ∨ order2 p p'.

Lemma wf_order : well_founded order.
Proof.
  assert (wf_order1: well_founded order1).
  { eapply wf_incl; [|
      eapply wf_inverse_image with (f := fst); eapply rigt_wf ].
    intros (_i1, _i2) (_i'1, _i'2). simpl.
    intros. unpack. eauto. }
  assert (wf_order2: well_founded order2).
  { eapply wf_incl; [|
      eapply wf_inverse_image with (f := snd); eapply rigt_wf ].
    intros (_i1, _i2) (_i'1, _i'2). simpl.
    intros. unpack. eauto. }
  eapply wf_incl; [|
    eapply wf_union; [| eapply wf_order1 | eapply wf_order2 ] ].
  { intros (_i1, _i2) (_i'1, _i'2).
    unfold order, Relation_Operators.union. tauto. }
  (* Commutation. *)
  { intros (_i1, _i2) (_i'1, _i'2) Ho1 (_i''1, _i''2) Ho2.
    unfold order1, order2 in Ho1, Ho2. unpack. subst.
    exists (_i1, _i''2); simpl; tauto. }
Qed.

End MergeOrder.

Local Instance Wf_order _j1 _j2 : WellFounded (order _j1 _j2) :=
  wf_guard 32 (wf_order _j1 _j2).

Local Hint Extern 1 (order _ _ _ _) =>
  unfold order, order1, order2
: lia.

(* -------------------------------------------------------------------------- *)

(* [merge_aux] merges two sorted array segments and writes the resulting
   sorted data into an array segment. *)

Section MergeAux.

(* In the recursive definition of [merge_aux], the following four
   parameters remain fixed. [_src1] and [_src2] are the source arrays.
   [_j1] and [_j2] are the end indices of the two source segments. *)

Variable _src1 _src2 : array A.
Variable _j1 _j2 : int.

(* Here is the code of [merge_aux]. *)

(* [_i1] and [_i2] are the start indices of the source segments. Each
   of the two source segments must be nonempty; [x1] and [x2] are the
   first elements of the source segments. [_dst] is the destination
   array. [_k] is the start index of the destination segment. The end
   index of the destination segment is [k + (j1 - i1) + (j2 - i2)]. *)

Open Scope uint63.

Equations merge_aux _i1 x1 _i2 x2 _dst _k : array A
by wf (_i1, _i2) (order _j1 _j2) :=
merge_aux _i1 x1 _i2 x2 _dst _k :=
  if (x1 ≤? x2)%element then
    do _dst ← set _dst _k x1 ;
    let _i1 := _i1 + 1 in
    let _k := _k + 1 in
    IF (_i1 <? _j1) THEN
      do x1 ← get _src1 _i1 ;
      merge_aux _i1 x1 _i2 x2 _dst _k
    ELSE
      blit _src2 _i2 _dst _k (_j2 - _i2)
  else
    do _dst ← set _dst _k x2 ;
    let _i2 := _i2 + 1 in
    let _k := _k + 1 in
    IF (_i2 <? _j2) THEN
      do x2 ← get _src2 _i2 ;
      merge_aux _i1 x1 _i2 x2 _dst _k
    ELSE
      blit _src1 _i1 _dst _k (_j1 - _i1).

End MergeAux.

(* The postcondition of [merge_aux]. *)

Definition merge_aux_post src1 src2 i1 j1 i2 j2 dst k :=
  λ _dst,
  ∃ dst',
  isArray _dst dst' ∧
  len dst = len dst' ∧
  (* Outside of the destination segment [k, limit),
     the destination array is unmodified. *)
  let limit := k + (j1 - i1) + (j2 - i2) in
  unmodified_outside_seg dst dst' k limit ∧
  (* Inside the destination segment, we find a permutation
     of the data contained in the two source segments, *)
  seg k limit dst' ≃ seg i1 j1 src1 ++ seg i2 j2 src2 ∧
  (* and the destination segment is sorted. *)
  sorted (seg k limit dst').

Local Ltac intro_merge_aux_post :=
  unfold merge_aux_post; eexists;
  split; [ eauto 2 | split; [ listz_arith | pack ] ].

Local Ltac elim_merge_aux_post dst' :=
  match goal with h: merge_aux_post _ _ _ _ _ _ _ _ _ |- _ =>
    unfold merge_aux_post in h;
    destruct h as (dst' & h);
    list in h;
    zring in h;
    unpack in h
  end.
  (* TODO review *)

(* The following two lemmas represent the reasoning that must be performed
   after [merge_aux] calls itself. *)

(* The disjunctive hypotheses that appear in these statements allow these
   lemmas to be used in several situations. The first disjunction states:
   either the first source segment is unaffected by the write [k := _], or
   it is affected and we have [limit = j1], which means that the first
   source segment forms a suffix of the destination segment. Similarly, the
   second disjunction states: either the second source segment is unaffected
   by the write [k := _], or it is affected and we have [limit = j2], which
   means that the second source segment forms a suffix of the destination
   segment. *)

Lemma merge_aux_post_implication_1 src1 src1' src2 src2' i1 j1 i2 j2 x1 x2 k _dst dst :
  x1 = src1 !!! i1 →
  x2 = src2 !!! i2 →
  x1 ≤ x2 →
  sorted (seg i1 j1 src1) →
  sorted (seg i2 j2 src2) →
  seg i1 j1 src1 `precede` seg i2 j2 src2 →
  valid_seg i1 j1 src1 →
  valid_seg i2 j2 src2 →
  let limit := k + (j1 - i1) + (j2 - i2) in
  valid_seg k limit dst →
  (i1 < j1)%Z →
  (i2 ≤ j2)%Z →
  merge_aux_post src1' src2' (i1 + 1) j1 i2 j2 (<[k:=x1]> dst) (k + 1) _dst →
  (
    src1' = src1 ∨
    src1' = <[k:=x1]> src1 ∧ limit = j1 ∨
    src1' = <[k:=x1]> src1 ∧ limit = j2 ∧ disjoint_seg i1 j1 k limit
  ) →
  (
    src2' = src2 ∨
    src2' = <[k:=x1]> src2 ∧ limit = j2
  ) →
  merge_aux_post src1 src2 i1 j1 i2 j2 dst k _dst.
Proof.
  intros ??? ??? ???? ?? Hpost Hcases1 Hcases2.
  elim_merge_aux_post dst'.
  intro_merge_aux_post.
  (* Unmodified. *)
  { rewrite Hpost1 by lia. list. reflexivity. }
  (* Permutation. *)
  { split_seg (k + 1) dst'. rewrite Hpost1 by lia. list.
    split_seg (i1 + 1) src1. rewrite Hpost2. recognize.
    rewrite <- app_assoc. eapply perm_xys; [ eauto | |].
    { destruct Hcases1 as [|[|]]; unpack; subst src1'; list; reflexivity. }
    { destruct Hcases2; unpack; subst src2'; list; reflexivity. }}
  (* Sortedness. *)
  { split_seg (k + 1) dst'. rewrite Hpost1 by lia. list.
    sorted_app. rewrite Hpost2.
    pairwise. split.
    { destruct Hcases1 as [|[|]]; unpack; subst src1'; list; pw. }
    { destruct Hcases2; unpack; subst src2'; list; pw. }}
Qed.

Lemma merge_aux_post_implication_2 src1 src1' src2 src2' i1 j1 i2 j2 x1 x2 k _dst dst :
  x1 = src1 !!! i1 →
  x2 = src2 !!! i2 →
  x2 < x1 →
  sorted (seg i1 j1 src1) →
  sorted (seg i2 j2 src2) →
  seg i1 j1 src1 `precede` seg i2 j2 src2 →
  valid_seg i1 j1 src1 →
  valid_seg i2 j2 src2 →
  let limit := k + (j1 - i1) + (j2 - i2) in
  valid_seg k limit dst →
  (i1 ≤ j1)%Z →
  (i2 < j2)%Z →
  merge_aux_post src1' src2' i1 j1 (i2 + 1) j2 (<[k:=x2]> dst) (k + 1) _dst →
  (
    src1' = src1 ∨
    src1' = <[k:=x2]> src1 ∧ limit = j1 ∨
    src1' = <[k:=x2]> src1 ∧ limit = j2 ∧ disjoint_seg i1 j1 k limit
  ) →
  (
    src2' = src2 ∨
    src2' = <[k:=x2]> src2 ∧ limit = j2
  ) →
  merge_aux_post src1 src2 i1 j1 i2 j2 dst k _dst.
Proof.
  intros ??? ??? ???? ?? Hpost Hcases1 Hcases2.
  elim_merge_aux_post dst'.
  intro_merge_aux_post.
  (* Unmodified. *)
  { rewrite Hpost1 by lia. list. reflexivity. }
  (* Permutation. *)
  { split_seg (k + 1) dst'. rewrite Hpost1 by lia. list.
    split_seg (i2 + 1) src2. rewrite Hpost2. recognize.
    eapply perm_yxs; [| eauto |].
    { destruct Hcases1 as [|[|]]; unpack; subst src1'; list; reflexivity. }
    { destruct Hcases2; unpack; subst src2'; list; reflexivity. }}
  (* Sortedness. *)
  { split_seg (k + 1) dst'. rewrite Hpost1 by lia. list.
    sorted_app. rewrite Hpost2.
    pairwise. split.
    { destruct Hcases1 as [|[|]]; unpack; subst src1'; list; pw. }
    { destruct Hcases2; unpack; subst src2'; list; pw. }}
Qed.

(* The following two lemmas represent the reasoning that must be performed
   after [merge_aux] has used [blit]. *)

Lemma merge_aux_post_init_1 src1 src2 i1 j1 i2 j2 x1 x2 k _dst dst :
  x1 = src1 !!! i1 →
  x2 = src2 !!! i2 →
  x1 ≤ x2 →
  i1 + 1 = j1 →
  sorted (seg i2 j2 src2) →
  seg i1 j1 src1 `precede` seg i2 j2 src2 →
  valid i1 src1 →
  valid_seg i2 j2 src2 →
  valid_seg k (k + 1 + j2 - i2) dst →
  isArray _dst (
    initial_seg k dst ++
    {[x1]} ++ seg i2 j2 src2 ++
    final_seg (k + 1 + j2 - i2) dst
  ) →
  merge_aux_post src1 src2 i1 j1 i2 j2 dst k _dst.
Proof.
  intros. intro_merge_aux_post.
  { unmodified_outside_seg. }
  { list. recognize. reflexivity. }
  { list. sorted_app.
    case (decide (i2 = j2)); intros; subst; list; pw. }
Qed.

Lemma merge_aux_post_init_2 src1 src2 i1 j1 i2 j2 x1 x2 k _dst dst :
  x1 = src1 !!! i1 →
  x2 = src2 !!! i2 →
  x2 < x1 →
  sorted (seg i1 j1 src1) →
  i2 + 1 = j2 →
  (* seg i1 j1 src1 `precede` seg i2 j2 src2 → *)
  valid_seg i1 j1 src1 →
  valid i2 src2 →
  valid_seg k (k + 1 + j1 - i1) dst →
  isArray _dst (
    initial_seg k dst ++
    {[x2]} ++ seg i1 j1 src1 ++
    final_seg (k + 1 + j1 - i1) dst
  ) →
  merge_aux_post src1 src2 i1 j1 i2 j2 dst k _dst.
Proof.
  intros. intro_merge_aux_post.
  { unmodified_outside_seg. }
  { list. zring. recognize. eapply Permutation_app_comm. }
  { list. sorted_app.
    case (decide (i1 = j1)); intros; subst; list; pw. }
Qed.

(* The following lemma is exploited by [optimistic_merge]. *)

Lemma merge_aux_post_init_optimistic src1 src2 i1 j1 i2 j2 x1 x2 k _dst dst :
  x1 = src1 !!! (j1 - 1) →
  x2 = src2 !!! i2 →
  x1 ≤ x2 →
  sorted (seg i1 j1 src1) →
  sorted (seg i2 j2 src2) →
  seg i1 j1 src1 `precede` seg i2 j2 src2 →
  valid_seg i1 j1 src1 →
  valid_seg i2 j2 src2 →
  valid_seg k (k + (j1 - i1) + (j2 - i2)) dst →
  isArray _dst (
    initial_seg k dst ++
    seg i1 j1 src1 ++
    seg i2 j2 src2 ++
    final_seg (k + j1 - i1 + j2 - i2) dst
  ) →
  merge_aux_post src1 src2 i1 j1 i2 j2 dst k _dst.
Proof.
  intros. intro_merge_aux_post.
  { unmodified_outside_seg. }
  { clarify. }
  { list. zring. rewrite seg_seg by lia. z. sorted. }
Qed.

(* The specification of [merge_aux]. *)

(* Because this function has 10 parameters, it is a bit verbose. *)

(* The source segments must be valid, nonempty, and sorted. *)

(* The first source segment must precede the second source segment. *)

Definition merge_aux_spec _j1 _j2 '((_i1, _i2) : int * int) :=
  ∀ _src1 src1 _src2 src2,
  isArray _src1 src1 →
  isArray _src2 src2 →
  ∀ i1, isInt _i1 i1 →
  ∀ j1, isInt _j1 j1 →
  valid_seg i1 j1 src1 →
  (i1 < j1)%Z →
  ∀ x1,
  x1 = src1 !!! i1 →
  ∀ i2, isInt _i2 i2 →
  ∀ j2, isInt _j2 j2 →
  valid_seg i2 j2 src2 →
  (i2 < j2)%Z →
  ∀ x2,
  x2 = src2 !!! i2 →
  sorted (seg i1 j1 src1) →
  sorted (seg i2 j2 src2) →
  seg i1 j1 src1 `precede` seg i2 j2 src2 →
  ∀Int _k k,
  ∀ _dst dst,
  isArray _dst dst →
  let limit := k + (j1 - i1) + (j2 - i2) in
  valid_seg k limit dst →
  wp (merge_aux _src1 _src2 _j1 _j2 _i1 x1 _i2 x2 _dst _k)
     (merge_aux_post src1 src2 i1 j1 i2 j2 dst k).

(* TODO?
Local Ltac tc ::=
  eauto 7 with typeclass_instances lia.
 *)

(* TODO *)
Local Ltac wp_precondition_hook ::=
  autorewrite with z clength wp_precondition_hook;
  match goal with
  | |- Sorted _ _ =>
      sorted
  | |- pairwise _ _ _ =>
      pw
  | _ =>
      eauto 6 with lia
  end.

Lemma wp_merge_aux _j1 _j2 _i1 _i2 :
  merge_aux_spec _j1 _j2 (_i1, _i2).
Proof.
  simple eapply (well_founded_ind (Wf_order _j1 _j2)). clear _i1 _i2.
  intros (_i1, _i2) IH.
  unfold merge_aux_spec. intros. arrays.
  autorewrite with merge_aux.
  wp_if.
  (* Case [x1 ≤ x2]. *)
  { wp_set.
    wp_if.
    (* Subcase [i1 + 1 < j1]. *)
    { wp_get x'1.
      wp_op_shadow (IH (_i1 + 1, _i2)%uint63) _dst.
      eapply merge_aux_post_implication_1; eauto with lia. }
    (* Subcase [i1 + 1 = j1]. *)
    { wp_blit.
      eapply merge_aux_post_init_1; eauto with lia. }}
  (* Case [x2 < x1]. *)
  { wp_set.
    wp_if.
    (* Subcase [i2 + 1 < j2]. *)
    { wp_get x'2.
      wp_op_shadow (IH (_i1, _i2 + 1)%uint63) _dst.
      eapply merge_aux_post_implication_2; eauto with lia. }
    (* Subcase [i2 + 1 = j2]. *)
    { wp_blit.
      eapply merge_aux_post_init_2; eauto with lia. }}
Qed.

(* -------------------------------------------------------------------------- *)

(* [merge_aux_1] is identical to [merge_aux], except the first source array
   [_src1] and the destination array [_dst] are the same array. The first
   source segment must then form a suffix of the destination segment. This
   implies that the data is moved left and cannot be overwritten before it
   is read. *)

(* The first source segment must form a suffix of the destination segment:
   that is, these segments must have the same end index. In other words, [j1]
   must be equal to [limit]; i.e., [i1] must be equal to [k + (j2 - i2)]. *)

(* We could relax this requirement by requesting just [i1 ≤ k + (j2 - i2)].
   Then, in the last branch, an additional test would be required in order
   to determine whether a call to [blit'] is necessary or redundant. We do
   not need this flexibility, so we require [i1 = k + (j2 - i2)] and we are
   able to eliminate the call to [blit'] unconditionally. *)

Section MergeAux1.

Variable _src2 : array A.
Variable _j1 _j2 : int.

Open Scope uint63.

Equations merge_aux_1 _i1 x1 _i2 x2 _dst _k : array A
by wf (_i1, _i2) (order _j1 _j2) :=
merge_aux_1 _i1 x1 _i2 x2 _dst _k :=
  if (x1 ≤? x2)%element then
    do _dst ← set _dst _k x1 ;
    let _i1 := _i1 + 1 in
    let _k := _k + 1 in
    IF (_i1 <? _j1) THEN
      do x1 ← get _dst _i1 ;
      merge_aux_1 _i1 x1 _i2 x2 _dst _k
    ELSE
      blit _src2 _i2 _dst _k (_j2 - _i2)
  else
    do _dst ← set _dst _k x2 ;
    let _i2 := _i2 + 1 in
    let _k := _k + 1 in
    IF (_i2 <? _j2) THEN
      do x2 ← get _src2 _i2 ;
      merge_aux_1 _i1 x1 _i2 x2 _dst _k
    ELSE
      (* There is nothing to do in this case. *)
      _dst.

End MergeAux1.

(* The specification of [merge_aux_1]. *)

Definition merge_aux_1_spec _j1 _j2 '((_i1, _i2) : int * int) :=
  ∀ _src1 src1 _src2 src2,
  isArray _src1 src1 →
  isArray _src2 src2 →
  ∀ i1, isInt _i1 i1 →
  ∀ j1, isInt _j1 j1 →
  valid_seg i1 j1 src1 →
  (i1 < j1)%Z →
  ∀ x1,
  x1 = src1 !!! i1 →
  ∀ i2, isInt _i2 i2 →
  ∀ j2, isInt _j2 j2 →
  valid_seg i2 j2 src2 →
  (i2 < j2)%Z →
  ∀ x2,
  x2 = src2 !!! i2 →
  sorted (seg i1 j1 src1) →
  sorted (seg i2 j2 src2) →
  seg i1 j1 src1 `precede` seg i2 j2 src2 →
  ∀Int _k k,
  (* The destination array is the first source array. *)
  let _dst := _src1 in
  let dst := src1 in
  (* The first source segment must form a suffix of the destination segment. *)
  let limit := k + (j1 - i1) + (j2 - i2) in
  limit = j1 →
  valid_seg k limit dst →
  wp (merge_aux_1 _src2 _j1 _j2 _i1 x1 _i2 x2 _dst _k)
     (merge_aux_post src1 src2 i1 j1 i2 j2 dst k).

Local Ltac wp_precondition_hook ::=
  list;
  match goal with
  | |- Sorted _ _ =>
      sorted
  | |- pairwise _ _ _ =>
      pw
  | _ =>
      eauto 6 with lia
  end.

Lemma wp_merge_aux_1 _j1 _j2 _i1 _i2 :
  merge_aux_1_spec _j1 _j2 (_i1, _i2).
Proof.
  simple eapply (well_founded_ind (Wf_order _j1 _j2)). clear _i1 _i2.
  intros (_i1, _i2) IH.
  unfold merge_aux_1_spec. intros. arrays.
  autorewrite with merge_aux_1.
  wp_if.
  (* Case [x1 ≤ x2]. *)
  { wp_set.
    wp_if.
    (* Subcase [i1 + 1 < j1]. *)
    { wp_get x'1.
      wp_op_shadow (IH (_i1 + 1, _i2)%uint63) _src1.
      eapply merge_aux_post_implication_1; eauto with lia. }
    (* Subcase [i1 + 1 = j1]. *)
    { wp_blit.
      eapply merge_aux_post_init_1; eauto with lia. }}
  (* Case [x2 < x1]. *)
  { wp_set.
    wp_if.
    (* Subcase [i2 + 1 < j2]. *)
    { wp_get x'2.
      wp_op_shadow (IH (_i1, _i2 + 1)%uint63) _src1.
      eapply merge_aux_post_implication_2; eauto with lia. }
    (* Subcase [i2 + 1 = j2]. *)
    { assert (i1 = k + 1) by lia. subst i1.
      wp_ret.
      eapply merge_aux_post_init_2; eauto with lia.
      join_segments. rewrite <- insert_seg_all by lia. assumption. }}
Qed.

(* -------------------------------------------------------------------------- *)

(* [merge_aux_2] is the symmetric counterpart of [merge_aux_1]. *)

(* The second source segment must form a suffix of the destination segment:
   that is, these segments must have the same end index. In other words, [j2]
   must be equal to [limit]; i.e., [i2] must be equal to [k + (j1 - i1)]. *)

Section MergeAux2.

Variable _src1 : array A.
Variable _j1 _j2 : int.

Open Scope uint63.

Equations merge_aux_2 _i1 x1 _i2 x2 _dst _k : array A
by wf (_i1, _i2) (order _j1 _j2) :=
merge_aux_2 _i1 x1 _i2 x2 _dst _k :=
  if (x1 ≤? x2)%element then
    do _dst ← set _dst _k x1 ;
    let _i1 := _i1 + 1 in
    let _k := _k + 1 in
    IF (_i1 <? _j1) THEN
      do x1 ← get _src1 _i1 ;
      merge_aux_2 _i1 x1 _i2 x2 _dst _k
    ELSE
      (* There is nothing to do in this case. *)
      _dst
  else
    do _dst ← set _dst _k x2 ;
    let _i2 := _i2 + 1 in
    let _k := _k + 1 in
    IF (_i2 <? _j2) THEN
      do x2 ← get _dst _i2 ;
      merge_aux_2 _i1 x1 _i2 x2 _dst _k
    ELSE
      blit _src1 _i1 _dst _k (_j1 - _i1).

End MergeAux2.

(* The specification of [merge_aux_2]. *)

Definition merge_aux_2_spec _j1 _j2 '((_i1, _i2) : int * int) :=
  ∀ _src1 src1 _src2 src2,
  isArray _src1 src1 →
  isArray _src2 src2 →
  ∀ i1, isInt _i1 i1 →
  ∀ j1, isInt _j1 j1 →
  valid_seg i1 j1 src1 →
  (i1 < j1)%Z →
  ∀ x1,
  x1 = src1 !!! i1 →
  ∀ i2, isInt _i2 i2 →
  ∀ j2, isInt _j2 j2 →
  valid_seg i2 j2 src2 →
  (i2 < j2)%Z →
  ∀ x2,
  x2 = src2 !!! i2 →
  sorted (seg i1 j1 src1) →
  sorted (seg i2 j2 src2) →
  seg i1 j1 src1 `precede` seg i2 j2 src2 →
  ∀Int _k k,
  (* The destination array is the second source array. *)
  let _dst := _src2 in
  let dst := src2 in
  (* The second source segment must form a suffix of the destination segment. *)
  let limit := k + (j1 - i1) + (j2 - i2) in
  limit = j2 →
  valid_seg k limit dst →
  wp (merge_aux_2 _src1 _j1 _j2 _i1 x1 _i2 x2 _dst _k)
     (merge_aux_post src1 src2 i1 j1 i2 j2 dst k).

Lemma wp_merge_aux_2 _j1 _j2 _i1 _i2 :
  merge_aux_2_spec _j1 _j2 (_i1, _i2).
Proof.
  simple eapply (well_founded_ind (Wf_order _j1 _j2)). clear _i1 _i2.
  intros (_i1, _i2) IH.
  unfold merge_aux_2_spec. intros. arrays.
  autorewrite with merge_aux_2.
  wp_if.
  (* Case [x1 ≤ x2]. *)
  { wp_set.
    wp_if.
    (* Subcase [i1 + 1 < j1]. *)
    { wp_get x'1.
      wp_op_shadow (IH (_i1 + 1, _i2)%uint63) _src2.
      eapply merge_aux_post_implication_1; eauto with lia. }
    (* Subcase [i1 + 1 = j1]. *)
    { assert (i2 = k + 1) by lia. subst i2.
      wp_ret.
      eapply merge_aux_post_init_1; eauto with lia.
      join_segments. rewrite <- insert_seg_all by lia. assumption. }}
  (* Case [x2 < x1]. *)
  { wp_set.
    wp_if.
    (* Subcase [i2 + 1 < j2]. *)
    { wp_get x'2.
      wp_op_shadow (IH (_i1, _i2 + 1)%uint63) _src2.
      eapply merge_aux_post_implication_2; eauto with lia. }
    (* Subcase [i2 + 1 = j2]. *)
    { wp_blit.
      eapply merge_aux_post_init_2; eauto with lia. }}
Qed.

(* -------------------------------------------------------------------------- *)

(* [merge_aux_12] is a variant of [merge_aux] where all three segments
   inhabit the same array. The first source segment and the destination
   segment must be disjoint. The second source segment must be a suffix of
   the destination segment. *)

Section MergeAux12.

Variable _j1 _j2 : int.

Open Scope uint63.

Equations merge_aux_12 _i1 x1 _i2 x2 _dst _k : array A
by wf (_i1, _i2) (order _j1 _j2) :=
merge_aux_12 _i1 x1 _i2 x2 _dst _k :=
  if (x1 ≤? x2)%element then
    do _dst ← set _dst _k x1 ;
    let _i1 := _i1 + 1 in
    let _k := _k + 1 in
    IF (_i1 <? _j1) THEN
      do x1 ← get _dst _i1 ;
      merge_aux_12 _i1 x1 _i2 x2 _dst _k
    ELSE
      _dst
  else
    do _dst ← set _dst _k x2 ;
    let _i2 := _i2 + 1 in
    let _k := _k + 1 in
    IF (_i2 <? _j2) THEN
      do x2 ← get _dst _i2 ;
      merge_aux_12 _i1 x1 _i2 x2 _dst _k
    ELSE
      blit' _dst _i1 _k (_j1 - _i1).

End MergeAux12.

(* The specification of [merge_aux_12]. *)

Definition merge_aux_12_spec _j1 _j2 '((_i1, _i2) : int * int) :=
  ∀ _dst dst,
  isArray _dst dst →
  ∀ i1, isInt _i1 i1 →
  ∀ j1, isInt _j1 j1 →
  valid_seg i1 j1 dst →
  (i1 < j1)%Z →
  ∀ x1,
  x1 = dst !!! i1 →
  ∀ i2, isInt _i2 i2 →
  ∀ j2, isInt _j2 j2 →
  valid_seg i2 j2 dst →
  (i2 < j2)%Z →
  ∀ x2,
  x2 = dst !!! i2 →
  sorted (seg i1 j1 dst) →
  sorted (seg i2 j2 dst) →
  seg i1 j1 dst `precede` seg i2 j2 dst →
  ∀Int _k k,
  (* The second source segment must be a suffix of the destination segment. *)
  let limit := k + (j1 - i1) + (j2 - i2) in
  limit = j2 →
  (* The first source segment and the destination segment must be disjoint. *)
  disjoint_seg i1 j1 k limit →
  valid_seg k limit dst →
  wp (merge_aux_12 _j1 _j2 _i1 x1 _i2 x2 _dst _k)
     (merge_aux_post dst dst i1 j1 i2 j2 dst k).

Lemma wp_merge_aux_12 _j1 _j2 _i1 _i2 :
  merge_aux_12_spec _j1 _j2 (_i1, _i2).
Proof.
  simple eapply (well_founded_ind (Wf_order _j1 _j2)). clear _i1 _i2.
  intros (_i1, _i2) IH.
  unfold merge_aux_12_spec. intros. arrays.
  autorewrite with merge_aux_12.
  wp_if.
  (* Case [x1 ≤ x2]. *)
  { wp_set.
    wp_if.
    (* Subcase [i1 + 1 < j1]. *)
    { wp_get x'1.
      wp_op_shadow (IH (_i1 + 1, _i2)%uint63) _dst.
      eapply merge_aux_post_implication_1; eauto with lia. }
    (* Subcase [i1 + 1 = j1]. *)
    { assert (i2 = k + 1) by lia. subst i2.
      wp_ret.
      eapply merge_aux_post_init_1; eauto with lia.
      join_segments. rewrite <- insert_seg_all by lia. assumption. }}
  (* Case [x2 < x1]. *)
  { wp_set.
    wp_if.
    (* Subcase [i2 + 1 < j2]. *)
    { wp_get x'2.
      wp_op_shadow (IH (_i1, _i2 + 1)%uint63) _dst.
      eapply merge_aux_post_implication_2; eauto with lia. }
    (* Subcase [i2 + 1 = j2]. *)
    { wp_blit.
      eapply merge_aux_post_init_2; eauto with lia. }}
Qed.

(* -------------------------------------------------------------------------- *)

(* [optimistic_merge] is a wrapper for [merge_aux]. It performs the two
   initial reads and invokes [merge_aux]. Furthermore, it detects the
   special case where the data in the first source segment is ordered
   below the data in the second source segment. Then, two blits suffice;
   thus we save a linear number of comparisons and conditional jumps. *)

(* The two source segments must be nonempty. *)

Section OptimisticMerge.

Open Scope uint63.

Definition optimistic_merge _src1 _i1 _j1 _src2 _i2 _j2 _dst _k :=
  (* Read the last element of the first source segment. *)
  do x1 ← get _src1 (_j1 - 1) ;
  (* Read the first element of the second source segment. *)
  do x2 ← get _src2 _i2 ;
  (* Compare them. *)
  if (x1 ≤? x2)%element then
    (* If they are suitably ordered then two blits suffice. *)
    let _n1 := _j1 - _i1 in
    do _dst ← blit _src1 _i1 _dst _k _n1 ;
    let _n2 := _j2 - _i2 in
    do _dst ← blit _src2 _i2 _dst (_k + _n1) _n2 ;
    _dst
  else
    do x1 ← get _src1 _i1 ;
    merge_aux _src1 _src2 _j1 _j2 _i1 x1 _i2 x2 _dst _k.

End OptimisticMerge.

Definition optimistic_merge_spec _j1 _j2 '((_i1, _i2) : int * int) :=
  ∀ _src1 src1 _src2 src2,
  isArray _src1 src1 →
  isArray _src2 src2 →
  ∀ i1, isInt _i1 i1 →
  ∀ j1, isInt _j1 j1 →
  valid_seg i1 j1 src1 →
  (i1 < j1)%Z →
  ∀ i2, isInt _i2 i2 →
  ∀ j2, isInt _j2 j2 →
  valid_seg i2 j2 src2 →
  (i2 < j2)%Z →
  sorted (seg i1 j1 src1) →
  sorted (seg i2 j2 src2) →
  seg i1 j1 src1 `precede` seg i2 j2 src2 →
  ∀Int _k k,
  ∀ _dst dst,
  isArray _dst dst →
  let limit := k + (j1 - i1) + (j2 - i2) in
  valid_seg k limit dst →
  wp (optimistic_merge _src1 _i1 _j1 _src2  _i2 _j2 _dst _k)
     (merge_aux_post src1 src2 i1 j1 i2 j2 dst k).

(* TODO does not work *)
Tactic Notation "shadow" tactic(cont) ident(x) :=
  let x' := fresh x in
  cont x';
  clear dependent x;
  rename x' into x.

Lemma wp_optimistic_merge _j1 _j2 _i1 _i2 :
  optimistic_merge_spec _j1 _j2 (_i1, _i2).
Proof.
  unfold optimistic_merge_spec. intros.
  unfold optimistic_merge.
  wp_get x1.
  wp_get x2.
  wp_if.
  (* Case [x1 ≤ x2]. *)
  { wp_blit.
    wp_blit.
    wp_last Hdst.
    (* Automatic simplification does not quite work here. *)
    rewrite !seg_seg in Hdst by lia. z in Hdst. zring in Hdst.
    wp_ret.
    eapply merge_aux_post_init_optimistic; eauto. }}
  (* Case [x2 < x1]. *)
  { clear dependent x1. wp_get x1.
    wp_op_shadow wp_merge_aux _dst.
    assumption. }
Qed.

(* -------------------------------------------------------------------------- *)

(* [optimistic_merge_1 is a variant of [optimistic_merge] where the
   first source array and the destination array are the same array.
   The first source segment must be a suffix of the destination segment. *)

(* The two source segments must be nonempty. *)

Section OptimisticMerge1.

Open Scope uint63.

Definition optimistic_merge_1 _i1 _j1 _src2 _i2 _j2 _dst _k :=
  (* Read the last element of the first source segment. *)
  do x1 ← get _dst (_j1 - 1) ;
  (* Read the first element of the second source segment. *)
  do x2 ← get _src2 _i2 ;
  (* Compare them. *)
  if (x1 ≤? x2)%element then
    (* If they are suitably ordered then two blits suffice. *)
    let _n1 := _j1 - _i1 in
    do _dst ← blit' _dst _i1 _k _n1 ;
    let _n2 := _j2 - _i2 in
    do _dst ← blit _src2 _i2 _dst (_k + _n1) _n2 ;
    _dst
  else
    do x1 ← get _dst _i1 ;
    merge_aux_1 _src2 _j1 _j2 _i1 x1 _i2 x2 _dst _k.

End OptimisticMerge1.

Definition optimistic_merge_1_spec _j1 _j2 '((_i1, _i2) : int * int) :=
  ∀ _src1 src1 _src2 src2,
  isArray _src1 src1 →
  isArray _src2 src2 →
  ∀ i1, isInt _i1 i1 →
  ∀ j1, isInt _j1 j1 →
  valid_seg i1 j1 src1 →
  (i1 < j1)%Z →
  ∀ i2, isInt _i2 i2 →
  ∀ j2, isInt _j2 j2 →
  valid_seg i2 j2 src2 →
  (i2 < j2)%Z →
  sorted (seg i1 j1 src1) →
  sorted (seg i2 j2 src2) →
  seg i1 j1 src1 `precede` seg i2 j2 src2 →
  ∀Int _k k,
  (* The destination array is the first source array. *)
  let _dst := _src1 in
  let dst := src1 in
  (* The first source segment must form a suffix of the destination segment. *)
  let limit := k + (j1 - i1) + (j2 - i2) in
  limit = j1 →
  valid_seg k limit dst →
  wp (optimistic_merge_1 _i1 _j1 _src2 _i2 _j2 _dst _k)
     (merge_aux_post src1 src2 i1 j1 i2 j2 dst k).

Lemma wp_optimistic_merge_1 _j1 _j2 _i1 _i2 :
  optimistic_merge_1_spec _j1 _j2 (_i1, _i2).
Proof.
  unfold optimistic_merge_1_spec. intros.
  unfold optimistic_merge_1.
  wp_get x1.
  wp_get x2.
  wp_if.
  (* Case [x1 ≤ x2]. *)
  { wp_blit.
    wp_blit.
    wp_last Hdst.
    (* Automatic simplification does not quite work here. *)
    rewrite !seg_seg in Hdst by lia. z in Hdst. zring in Hdst.
    wp_ret.
    eapply merge_aux_post_init_optimistic; eauto. }
  (* Case [x2 < x1]. *)
  { clear dependent x1. wp_get x1.
    wp_op wp_merge_aux_1 _dst'.
    assumption. }
Qed.

(* -------------------------------------------------------------------------- *)

(* [optimistic_merge_2] is a variant of [optimistic_merge] where the
   second source segment is a suffix of the destination segment. *)

(* The two source segments must be nonempty. *)

Section OptimisticMerge2.

Open Scope uint63.

Definition optimistic_merge_2 _src1 _i1 _j1 _i2 _j2 _dst _k :=
  (* Read the last element of the first source segment. *)
  do x1 ← get _src1 (_j1 - 1) ;
  (* Read the first element of the second source segment. *)
  do x2 ← get _dst _i2 ;
  (* Compare them. *)
  if (x1 ≤? x2)%element then
    (* If they are suitably ordered then one blit suffices. *)
    let _n1 := _j1 - _i1 in
    do _dst ← blit _src1 _i1 _dst _k _n1 ;
    _dst
  else
    do x1 ← get _src1 _i1 ;
    merge_aux_2 _src1 _j1 _j2 _i1 x1 _i2 x2 _dst _k.

End OptimisticMerge2.

Definition optimistic_merge_2_spec _j1 _j2 '((_i1, _i2) : int * int) :=
  ∀ _src1 src1 _src2 src2,
  isArray _src1 src1 →
  isArray _src2 src2 →
  ∀ i1, isInt _i1 i1 →
  ∀ j1, isInt _j1 j1 →
  valid_seg i1 j1 src1 →
  (i1 < j1)%Z →
  ∀ i2, isInt _i2 i2 →
  ∀ j2, isInt _j2 j2 →
  valid_seg i2 j2 src2 →
  (i2 < j2)%Z →
  sorted (seg i1 j1 src1) →
  sorted (seg i2 j2 src2) →
  seg i1 j1 src1 `precede` seg i2 j2 src2 →
  ∀Int _k k,
  (* The destination array is the second source array. *)
  let _dst := _src2 in
  let dst := src2 in
  (* The second source segment must form a suffix of the destination segment. *)
  let limit := k + (j1 - i1) + (j2 - i2) in
  limit = j2 →
  valid_seg k limit dst →
  wp (optimistic_merge_2 _src1 _i1 _j1 _i2 _j2 _dst _k)
     (merge_aux_post src1 src2 i1 j1 i2 j2 dst k).

Lemma wp_optimistic_merge_2 _j1 _j2 _i1 _i2 :
  optimistic_merge_2_spec _j1 _j2 (_i1, _i2).
Proof.
  unfold optimistic_merge_2_spec. intros.
  unfold optimistic_merge_2.
  wp_get x1.
  wp_get x2.
  wp_if.
  (* Case [x1 ≤ x2]. *)
  { wp_blit.
    wp_ret.
    eapply merge_aux_post_init_optimistic; eauto. isArray. }
  (* Case [x2 < x1]. *)
  { clear dependent x1. wp_get x1.
    wp_op wp_merge_aux_2 _dst'.
    assumption. }
Qed.

(* -------------------------------------------------------------------------- *)

(* [optimistic_merge_12] is a variant of [optimistic_merge] where all
   three segments inhabit the same array. The first source segment and the
   destination segment must be disjoint. The second source segment must be
   a suffix of the destination segment. *)

(* The two source segments must be nonempty. *)

Section OptimisticMerge12.

Open Scope uint63.

Definition optimistic_merge_12 _dst _i1 _j1 _i2 _j2 _k :=
  do x1 ← get _dst (_j1 - 1) ;
  do x2 ← get _dst _i2 ;
  if (x1 ≤? x2)%element then
    let _n1 := _j1 - _i1 in
    do _dst ← blit' _dst _i1 _k _n1 ;
    _dst
  else
    do x1 ← get _dst _i1 ;
    merge_aux_12 _j1 _j2 _i1 x1 _i2 x2 _dst _k.

End OptimisticMerge12.

Definition optimistic_merge_12_spec _j1 _j2 '((_i1, _i2) : int * int) :=
  ∀ _dst dst,
  isArray _dst dst →
  ∀ i1, isInt _i1 i1 →
  ∀ j1, isInt _j1 j1 →
  valid_seg i1 j1 dst →
  (i1 < j1)%Z →
  ∀ i2, isInt _i2 i2 →
  ∀ j2, isInt _j2 j2 →
  valid_seg i2 j2 dst →
  (i2 < j2)%Z →
  sorted (seg i1 j1 dst) →
  sorted (seg i2 j2 dst) →
  seg i1 j1 dst `precede` seg i2 j2 dst →
  ∀Int _k k,
  (* The second source segment must be a suffix of the destination segment. *)
  let limit := k + (j1 - i1) + (j2 - i2) in
  limit = j2 →
  (* The first source segment and the destination segment must be disjoint. *)
  disjoint_seg i1 j1 k limit →
  valid_seg k limit dst →
  wp (optimistic_merge_12 _dst _i1 _j1 _i2 _j2 _k)
     (merge_aux_post dst dst i1 j1 i2 j2 dst k).

Lemma wp_optimistic_merge_12 _j1 _j2 _i1 _i2 :
  optimistic_merge_12_spec _j1 _j2 (_i1, _i2).
Proof.
  unfold optimistic_merge_12_spec. intros.
  unfold optimistic_merge_12.
  wp_get x1.
  wp_get x2.
  wp_if.
  (* Case [x1 ≤ x2]. *)
  { wp_blit.
    wp_ret.
    eapply merge_aux_post_init_optimistic; eauto. isArray. }
  (* Case [x2 < x1]. *)
  { clear dependent x1. wp_get x1.
    wp_op wp_merge_aux_12 _dst'.
    assumption. }
Qed.

(* -------------------------------------------------------------------------- *)

(* [sortto' _i _dst _k _n] sorts the source array segment described by the
   array [_dst], the start index [_i], and the length [_n]. The sorted data
   is written into the array segment described by [_dst], [_k], and [_n].
   The source and destination segments must be disjoint. This is a merge
   sort. It is stable. *)

Section SortTo'.

Open Scope uint63.

(* The cutoff determines where to switch from merge sort to insertion
   sort. OCaml uses 5. *)

Notation cutoff := 5.

Equations sortto' _dst _i _k _n : array A
by wf _n ilt :=
sortto' _dst _i _k _n :=
  IF _n ≤? cutoff THEN
    (* Under the cutoff, use insertion sort. *)
    isortto' _dst _i _k _n
  ELSE
    (* Divide the source segment into two halves. The second half may
       be longer by one unit. *)
    let _n1 := _n / 2 in
    let _n2 := _n - _n1 in
    let _dm := _k + _n1 in
    (* Sort the second half of the source segment and move it to the
       second half of the destination segment. *)
    do _dst ← sortto' _dst (_i + _n1) _dm _n2 ;
    (* Sort the first half of the source segment and move it to the second
       half of the source segment. This requires [n1 ≤ n2]. *)
    let _sm := _i + _n2 in
    do _dst ← sortto' _dst _i _sm _n1 ;
    (* Merge the sorted halves, moving the data to the destination segment. *)
    do _dst ← optimistic_merge_12 _dst _sm (_sm + _n1) _dm (_dm + _n2) _k ;
    _dst.

End SortTo'.

(* The postcondition of [sortto']. *)

Definition sortto'_post dst i k n _dst :=
  ∃ dst',
  isArray _dst dst' ∧
  len dst = len dst' ∧
  (* Outside of the source and destination segments,
     the destination array is unmodified. *)
  ( ∀ a b,
    valid_seg a b dst →
    disjoint_seg a b i (i + n) →
    disjoint_seg a b k (k + n) →
    seg a b dst' = seg a b dst
  ) ∧
  (* The destination segment now contains a permutation
     of the data that existed in the source segment. *)
  seg k (k + n) dst' ≃ seg i (i + n) dst ∧
  (* The destination segment is sorted. *)
  sorted (seg k (k + n) dst').

Local Ltac intro_sortto'_post :=
  unfold sortto'_post; eexists;
  split; [ eauto 2 | split; [ listz_arith | pack ] ];
  (* 3 subgoals remain: *)
  [ try solve [unmodified_outside_seg] | eauto | sorted ].

Local Ltac elim_sortto'_post dst' :=
  match goal with h: sortto'_post _ _ _ _ _ |- _ =>
    destruct h as (dst' & h); unpack in h
  end.

(* The specification of [sortto']. *)

Definition sortto'_spec _n :=
  ∀ _dst dst _i i _k k n,
  isArray _dst dst →
  isInt _i i →
  isInt _k k →
  isInt _n n →
  valid_seg i (i + n) dst →
  valid_seg k (k + n) dst →
  disjoint_seg i (i + n) k (k + n) →
  Sorted R' (seg i (i + n) dst) →
  wp (sortto' _dst _i _k _n)
     (sortto'_post dst i k n).

Lemma wp_sortto' : ∀ _n, sortto'_spec _n.
Proof.
  simple eapply (well_founded_ind Wf_ilt).
  intros _n IH.
  unfold sortto'_spec. intros. arrays.
  autorewrite with sortto'.
  wp_if.
  (* Case [n ≤ cutoff]. *)
  { wp_op_shadow wp_isortto' _dst.
    elim_isortto_inv dst'. intro_sortto'_post. }
  (* Case [cutoff < n]. We actually need only [2 ≤ n]. *)
  {
    set (_n1 := (_n / 2)%uint63). set (n1 := (n / 2)).
    assert (isInt _n1 n1) by tc.
    set (_n2 := (_n - _n1)%uint63). set (n2 := (n - n1)).
    assert (isInt _n2 n2) by tc.
    replace n with (n1 + n2) in * by lia.
    (* The first recursive call. *)
    wp_op_shadow IH _dst. wp_last HpostA.
    elim_sortto'_post dst'.
    (* This call has not affected the first half of the source segment. *)
    assert (frameA: seg i (i + n1) dst' = seg i (i + n1) dst)
      by eauto with lia.
    assert (Sorted R' (seg i (i + n1) dst'))
      by (rewrite frameA; sorted).
    (* The second recursive call. *)
    wp_op_shadow IH _dst. wp_last HpostB.
    elim_sortto'_post dst''.
    (* This call has not affected the destination segment.
       In particular, its second half is unmodified. *)
    assert (frameB: seg (k + n1) (k + n1 + n2) dst'' =
                    seg (k + n1) (k + n1 + n2) dst').
    { eauto using seg_equality_implication with lia. }
    (* The following facts are needed by the next call. *)
    assert (sorted (seg (k + n1) (k + n1 + n2) dst'')).
    { rewrite frameB. assumption. }
    assert (seg (i + n2) (i + n2 + n1) dst'' `precede`
            seg (k + n1) (k + n1 + n2) dst'').
    { rewrite frameB. rewrite HpostB2. rewrite HpostA2. rewrite frameA.
      eapply split_sorted_seg; eauto 2 with lia; sorted. }
    (* The third call: merging the sorted halves. *)
    wp_op_shadow wp_optimistic_merge_12 _dst. wp_last HpostC.
    elim_merge_aux_post dst'''.
    (* Conclude. *)
    wp_ret. intro_sortto'_post.
    (* Nothing has been modified outside of the two segments. *)
    { rewrite HpostC1, HpostB1, HpostA1 by lia. reflexivity. }
    (* Permutation. *)
    { z.
      rewrite HpostC2.
      rewrite HpostB2, frameB.
      rewrite frameA, HpostA2.
      join_segments. reflexivity. }}
Qed.

(* -------------------------------------------------------------------------- *)

(* [sortto _src _i _dst _k _n] sorts the source array segment described by
   the array [_src], the start index [_i], and the length [_n]. The sorted
   data is written into the array segment described by [_dst], [_k], and
   [_n]. The arrays [_src] and [_dst] must be distinct. This is a merge
   sort. It is stable sort. *)

Section SortTo.
Open Scope uint63.

(* The cutoff determines where to switch from merge sort to insertion
   sort. OCaml uses 5. *)

Notation cutoff := 5.

Equations sortto _src _dst _i _k _n : array A * array A
by wf _n ilt :=
sortto _src _dst _i _k _n :=
  IF _n ≤? cutoff THEN
    (* Under the cutoff, use insertion sort. *)
    do _dst ← isortto _src _i _dst _k _n ;
    (_src, _dst)
  ELSE
    (* Divide the source segment into two halves. The second half may
       be longer by one unit. *)
    let _n1 := _n / 2 in
    let _n2 := _n - _n1 in
    let _dm := _k + _n1 in
    (* Sort the second half of the source segment and move it to the
       second half of the destination segment. *)
    do (_src, _dst) ← sortto _src _dst (_i + _n1) _dm _n2 ;
    (* Sort the first half of the source segment and move it to the second
       half of the source segment. This requires [n1 ≤ n2]. *)
    let _sm := _i + _n2 in
    do _src ← sortto' _src _i _sm _n1 ;
    (* Merge the sorted halves, moving the data to the destination segment. *)
    do _dst ← optimistic_merge_2 _src _sm (_sm + _n1) _dm (_dm + _n2) _dst _k ;
    (_src, _dst).

End SortTo.

(* The postcondition of [sortto]. *)

Definition sortto_post src dst i k n '(_src, _dst) :=
  ∃ src' dst',
  isArray _src src' ∧
  len src = len src' ∧
  isArray _dst dst' ∧
  len dst = len dst' ∧
  (* Outside of the source segment, the source array is unmodified. *)
  (* And an analogous statement about the destination array. *)
  unmodified_outside_seg src src' i (i + n) ∧
  unmodified_outside_seg dst dst' k (k + n) ∧
  (* The destination segment now contains a permutation
     of the data that existed in the source segment. *)
  seg k (k + n) dst' ≃ seg i (i + n) src ∧
  (* The destination segment is sorted. *)
  sorted (seg k (k + n) dst').

Local Ltac intro_sortto_post :=
  unfold sortto_post; pack; tc3; length; tc3.

Local Ltac elim_sortto_post src' dst' :=
  match goal with h: sortto_post _ _ _ _ _ _ |- _ =>
    destruct h as (src' & dst' & h); unpack in h
  end.

(* The specification of [sortto]. *)

Definition sortto_spec _n :=
  ∀ _src src _dst dst _i i _k k n,
  isArray _src src →
  isArray _dst dst →
  isInt _i i →
  isInt _k k →
  isInt _n n →
  valid_seg i (i + n) src →
  valid_seg k (k + n) dst →
  Sorted R' (seg i (i + n) src) →
  wp (sortto _src _dst _i _k _n)
     (sortto_post src dst i k n).

Lemma wp_sortto : ∀ _n, sortto_spec _n.
Proof.
  simple eapply (well_founded_ind Wf_ilt).
  intros _n IH.
  unfold sortto_spec. intros. arrays.
  autorewrite with sortto.
  wp_if.
  (* Case [n ≤ cutoff]. *)
  { wp_op_shadow wp_isortto _dst.
    elim_isortto_inv dst'.
    wp_ret. intro_sortto_post. }
  (* Case [cutoff < n]. We actually need only [2 ≤ n]. *)
  { set (_n1 := (_n / 2)%uint63). set (n1 := (n / 2)).
    assert (isInt _n1 n1) by tc.
    set (_n2 := (_n - _n1)%uint63). set (n2 := (n - n1)).
    assert (isInt _n2 n2) by tc.
    replace n with (n1 + n2) in * by lia.
    (* The first recursive call. *)
    wp_op_shadow_pair IH _src _dst. wp_last HpostA.
    elim_sortto_post src' dst'.
    (* This call has not affected the first half of the source segment. *)
    assert (frameA: seg i (i + n1) src' = seg i (i + n1) src)
      by eauto with lia.
    assert (Sorted R' (seg i (i + n1) src'))
      by (rewrite frameA; sorted).
    (* The second call: a call to [sortto']. *)
    wp_op_shadow wp_sortto' _src. wp_last HpostB.
    elim_sortto'_post src''.
    assert (seg (i + n2) (i + n2 + n1) src'' `precede`
            seg (k + n1) (k + n1 + n2) dst').
    { rewrite HpostB2. rewrite HpostA5. rewrite frameA.
      eapply split_sorted_seg; eauto 2 with lia; sorted. }
    (* The third call: merging the sorted halves. *)
    wp_op_shadow wp_optimistic_merge_2 _dst. wp_last HpostC.
    elim_merge_aux_post dst'''.
    (* Conclude. *)
    wp_ret. intro_sortto_post.
    (* Nothing has been modified outside of the two segments. *)
    { rewrite HpostB1, HpostA3 by lia. reflexivity. }
    { rewrite HpostC1, HpostA4 by lia. reflexivity. }
    (* Permutation. *)
    { rewrite HpostC2.
      rewrite HpostB2.
      rewrite frameA, HpostA5.
      join_segments. reflexivity. }}
Qed.

(* -------------------------------------------------------------------------- *)

(* [sort_seg a _i _n] sorts the array segment described by the array [a],
   the start index [_i], and the length [_n]. The data is sorted in place.
   This is a merge sort. It is stable. *)

Section SortSeg.
Open Scope uint63.

(* The cutoff determines where to switch from merge sort to insertion
   sort. OCaml uses 5. *)

Notation cutoff := 5.

Definition sort_seg a _i _n :=
  if _n ≤? cutoff then
    (* Under the cutoff, use insertion sort. *)
    isortto' a _i _i _n
  else
    (* Divide the source segment into two halves. The second half may
       be longer by one unit. *)
    let _n1 := _n / 2 in
    let _n2 := _n - _n1 in
    (* Allocate a temporary array that can host the second half. *)
    do t ← make _n2 inhabitant ;
    (* Sort the second half of [a] and move it to [t]. *)
    do (a, t) ← sortto a t (_i + _n1) 0 _n2 ;
    (* Sort the first half of [a] and move it to the second half of [a]. *)
    (* This requires [n1 ≤ n2]. *)
    do a ← sortto' a _i (_i + _n2) _n1 ;
    (* Merge the sorted halves, moving the data to [a]. *)
    do a ← optimistic_merge_1 (_i + _n2) (_i + _n) t 0 _n2 a _i ;
    a.

End SortSeg.

(* The postcondition of [sort_seg]. *)

Definition sort_seg_post xs i n a :=
  ∃ xs',
  isArray a xs' ∧
  len xs = len xs' ∧
  (* Outside of the designated segment, the array is unmodified. *)
  unmodified_outside_seg xs xs' i (i + n) ∧
  (* This segment contains a permutation of the data
     that initially existed in this segment. *)
  seg i (i + n) xs' ≃ seg i (i + n) xs ∧
  (* The segment is sorted. *)
  sorted (seg i (i + n) xs').

Local Ltac intro_sort_seg_post :=
  unfold sort_seg_post; pack; tc3; length; tc3.

Local Ltac elim_sort_seg_post xs' :=
  match goal with h: sort_seg_post _ _ _ _ |- _ =>
    destruct h as (xs' & h); unpack in h
  end.

(* The specification of [sort_seg]. *)

Lemma wp_sort_seg : ∀ a xs _i i _n n,
  isArray a xs →
  isInt _i i →
  isInt _n n →
  valid_seg i (i + n) xs →
  Sorted R' (seg i (i + n) xs) →
  wp (sort_seg a _i _n)
     (sort_seg_post xs i n).
Proof.
  intros. unfold sort_seg. arrays.
  wp_if.
  (* Case [n ≤ cutoff]. *)
  { wp_op_shadow wp_isortto' a.
    elim_isortto_inv xs'.
    intro_sort_seg_post. }
  (* Case [cutoff < n]. We actually need only [2 ≤ n]. *)
  { set (_n1 := (_n / 2)%uint63). set (n1 := (n / 2)).
    assert (isInt _n1 n1) by tc.
    set (_n2 := (_n - _n1)%uint63). set (n2 := (n - n1)).
    assert (isInt _n2 n2) by tc.
    replace n with (n1 + n2) in * by lia.
    (* Allocation of an array. *)
    wp_make t.
    (* The first call. *)
    wp_op_shadow_pair wp_sortto a t. wp_last HpostA.
    elim_sortto_post xs' dst'. length in *.
    (* This call has not affected the first half of [a]. *)
    assert (frameA: seg i (i + n1) xs' = seg i (i + n1) xs)
      by eauto with lia.
    assert (Sorted R' (seg i (i + n1) xs'))
      by (rewrite frameA; sorted).
    (* The second call. *)
    wp_op_shadow wp_sortto' a. wp_last HpostB.
    elim_sortto'_post xs''.
    replace (i + n2 + n1) with (i + n1 + n2) in * by lia.
    assert (seg (i + n2) (i + n1 + n2) xs'' `precede`
            seg 0 n2 dst').
    { rewrite HpostB2. rewrite HpostA5. rewrite frameA.
      eapply split_sorted_seg; eauto 2 with lia. }
    (* The third call: merging the sorted halves. *)
    wp_op_shadow wp_optimistic_merge_1 a. wp_last HpostC.
    elim_merge_aux_post xs'''.
    (* Conclude. *)
    wp_ret. intro_sort_seg_post.
    (* Nothing has been modified outside of this segment. *)
    { rewrite HpostC1, HpostB1, HpostA3 by lia. reflexivity. }
    (* Permutation. *)
    { rewrite HpostC2.
      rewrite HpostB2.
      rewrite frameA, HpostA5.
      join_segments. reflexivity. }}
Qed.

(* -------------------------------------------------------------------------- *)

(* [sort a] sorts the array [a] in place. This is a merge sort.
   It is stable. *)

Section Sort.
Open Scope uint63.

Definition sort a :=
  do _n ← length a ;
  sort_seg a 0 _n.

(* The postcondition of [sort]. *)

Definition sort_post xs a :=
  ∃ xs',
  isArray a xs' ∧
  len xs = len xs' ∧
  (* This array contains a permutation of the data
     that initially existed in it. *)
  xs' ≃ xs ∧
  (* The array is sorted. *)
  sorted xs'.

Local Ltac intro_sort_post :=
  unfold sort_post; pack; tc3; length; tc3.

Ltac elim_sort_post xs' :=
  match goal with h: sort_post _ _ |- _ =>
    destruct h as (xs' & h); unpack in h
  end.

(* The specification of [sort]. *)

Lemma wp_sort a xs :
  isArray a xs →
  Sorted R' xs →
  wp (sort a) (sort_post xs).
Proof.
  intros. unfold sort. arrays.
  wp_length _n.
  assert (Sorted R' (initial_seg (0 + len xs) xs))
    by (list; assumption).
  wp_op_shadow wp_sort_seg a. wp_last Hpost.
  elim_sort_seg_post xs'. list in *.
  intro_sort_post.
Qed.

End Sort.

(* -------------------------------------------------------------------------- *)

(* Merging two sorted arrays: [merge]. *)

Section Merge.
Open Scope uint63.

Definition merge a b :=
  do _m ← length a ;
  do _n ← length b ;
  if _m =? 0 then
    copy b
  else if _n =? 0 then
    copy a
  else
    do c ← make (_m + _n) inhabitant ;
    optimistic_merge a 0 _m b 0 _n c 0.

(* The public specification of [merge]. *)

Lemma wp_merge :
  ∀ a xs,
  isArray a xs →
  sorted xs →
  ∀ b ys,
  isArray b ys →
  sorted ys →
  xs `precede` ys →
  (len xs + len ys ≤ max_array_length)%Z →
  wp (merge a b) (λ c, ∃ zs,
    isArray c zs ∧
    zs ≃ xs ++ ys ∧
    sorted zs
  ).
Proof.
  intros. unfold merge. arrays.
  wp_length _m.
  wp_length _n.
  wp_if.
  { rewrite length_zero_iff_nil in *. subst. list.
    wp_copy c. eexists; pack; eauto. }
  wp_if.
  { rewrite length_zero_iff_nil in *. subst. list.
    wp_copy c. eexists; pack; eauto. }
  wp_make c.
  wp_op_shadow wp_optimistic_merge c.
  elim_merge_aux_post zs.
  eexists; pack; eauto.
Qed.

End Merge.

End Sorting.

(* -------------------------------------------------------------------------- *)

(* Repeated tactics, for our end users. *)

Global Ltac elim_sort_seg_post xs' :=
  match goal with h: sort_seg_post _ _ _ _ |- _ =>
    destruct h as (xs' & h); unpack in h
  end.

Global Ltac elim_sort_post xs' :=
  match goal with h: sort_post _ _ |- _ =>
    destruct h as (xs' & h); unpack in h
  end.

Infix "≃" := Permutation
  (at level 70, no associativity).

Arguments lex {A}%_type_scope R R' x y.

(* -------------------------------------------------------------------------- *)

(* These lemma help get rid of the stability concern. *)

Section NoStability.
Context `{Inhabited A, PreOrder A R, LebSpec A R}.

(* As we do not care about stability, we let [R'] be the relation that
   is everywhere true. This is a preorder, and every array is sorted
   with respect to this relation. *)

Notation R' := (λ x y : A, True).

Local Instance PreOrder_R' : PreOrder R'.
Proof. constructor; eauto. Qed.

Local Lemma Sorted_R' xs : Sorted R' xs.
Proof. eapply Sorted_top; eauto. Qed.
Local Hint Resolve Sorted_R' : core.

Local Hint Unfold lex : core.

(* The lexicographic ordering of [R] and [R']
   is the same thing as [R]. *)

Local Lemma Sorted_lex_R'_iff xs :
  Sorted (lex R R') xs ↔ Sorted R xs.
Proof.
  specialize (@lex_elim A R R'); intro.
  split; intros; eapply Sorted_covariant; eauto.
Qed.

Local Lemma Sorted_lex_R'_intro xs :
  Sorted R xs → Sorted (lex R R') xs.
Proof.
  rewrite Sorted_lex_R'_iff. eauto.
Qed.

Local Lemma Sorted_lex_R'_elim xs :
  Sorted (lex R R') xs → Sorted R xs.
Proof.
  rewrite Sorted_lex_R'_iff. eauto.
Qed.

Local Lemma pairwise_R'_intro xs ys :
  pairwise R' xs ys.
Proof.
  unfold pairwise. eauto.
Qed.

Local Hint Resolve
  Sorted_lex_R'_intro
  Sorted_lex_R'_elim
  pairwise_R'_intro
: core.

(* -------------------------------------------------------------------------- *)

(* A simplified specification of [sort_seg], without stability. *)

Lemma wp_sort_seg' a xs _i i _n n :
  isArray a xs →
  isInt _i i →
  isInt _n n →
  valid_seg i (i + n) xs →
  wp (sort_seg a _i _n) (λ a, ∃ xs',
    isArray a xs' ∧
    len xs = len xs' ∧
    (* Outside of the designated segment, the array is unmodified. *)
    unmodified_outside_seg xs xs' i (i + n) ∧
    (* This segment contains a permutation of the data
       that initially existed in this segment. *)
    seg i (i + n) xs' ≃ seg i (i + n) xs ∧
    (* The segment is sorted. *)
    Sorted R (seg i (i + n) xs')
  ).
Proof.
  intros.
  wp_op_shadow (@wp_sort_seg A _ R _ _ _ R' _) a.
  elim_sort_seg_post xs'.
  eauto 7 using Sorted_covariant.
Qed.

(* -------------------------------------------------------------------------- *)

(* A simplified specification of [sort], without stability. *)

Lemma wp_sort' `{Inhabited A, PreOrder A R, LebSpec A R} a xs :
  isArray a xs →
  wp (sort a) (λ a, ∃ xs',
    isArray a xs' ∧
    len xs = len xs' ∧
    (* This array contains a permutation of the data
       that initially existed in it. *)
    xs' ≃ xs ∧
    (* The array is sorted. *)
    Sorted R xs'
  ).
Proof.
  intros.
  wp_op_shadow (@wp_sort A _ R _ _ _ R' _) a.
  elim_sort_post xs'.
  eauto 6 using Sorted_covariant.
Qed.

(* -------------------------------------------------------------------------- *)

(* A simplified specification of [merge], without stability. *)

Lemma wp_merge' `{Inhabited A, PreOrder A R, LebSpec A R} :
  ∀ a xs,
  isArray a xs →
  Sorted R xs →
  ∀ b ys,
  isArray b ys →
  Sorted R ys →
  (len xs + len ys ≤ max_array_length)%Z →
  wp (merge a b) (λ c, ∃ zs,
    isArray c zs ∧
    zs ≃ xs ++ ys ∧
    Sorted R zs
  ).
Proof.
  intros.
  wp_op (@wp_merge A _ R _ _ _ R' _) c.
  eauto using Sorted_covariant.
Qed.

End NoStability.

Global Ltac wp_sort_seg a :=
  wp_op_shadow @wp_sort_seg' a.

Global Ltac wp_sort a :=
  wp_op_shadow @wp_sort' a.

Global Ltac wp_merge c :=
  wp_op @wp_merge' c.
