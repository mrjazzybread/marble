From stdpp Require Import numbers list well_founded.
From Stdlib Require Import Uint63.
From Stdlib Require Import Array.PArray.
From Stdlib Require Import Sorting.Permutation Sorting.Sorted.
From Corelib Require Import Classes.RelationClasses.
From marble Require Import equations.
From marble Require Import tactics list_extra iteration int wp wp_tactics array orders sorting.
Implicit Types _i _j _k : int.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

Open Scope nat_scope.

(* Documentation:
   https://rocq-prover.org/doc/V9.1.0/corelib/Corelib.Classes.RelationClasses.html
   https://rocq-prover.org/doc/v9.0/stdlib/Stdlib.Sorting.Sorted.html
 *)

(* -------------------------------------------------------------------------- *)

(* A couple local tactics. *)

(* The tactic [recognize_named_lookups] detects hypotheses of the form
   [x = xs !!! i] and uses them to replace [xs !!! i] with [x] both in
   the goal and in all hypotheses. *)

Local Ltac recognize_named_lookups :=
  repeat match goal with h: ?x = ?xs !!! ?i |- _ =>
    try rewrite <- !h in *;
    revert h
  end;
  intros.

(* The tactic [use_known_permutation] detects a hypothesis of the form
   [xs ≃ ys], where [xs] occurs in the goal, and uses it to replace [xs]
   with [ys] in the goal. (Of course this requires the surrounding context
   to be compatible with such a rewriting step.) *)

Local Ltac use_known_permutation :=
  match goal with h: Permutation ?xs ?ys |- context[?xs] =>
    rewrite h
  end.

(* -------------------------------------------------------------------------- *)

(* Facts and lemmas about sortedness. *)

(* These lemmas use some of our notations about lists, so they cannot be
   moved to sorting.v, unless we allow this file to depend on list_extra.v. *)

(* Many of the lemmas in this section concern the predicate [sorted]. They
   are currently unused, because we now use [smt_sorted] instead, which is
   equivalent. *)

Declare Scope element_scope.
Delimit Scope element_scope with element.

Section Sortedness.

(* We assume that there is a preorder [R], also written [≤], on the type [A]. *)

Context `{Inhabited A} `{PreOrder A R}.

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

(* We write [sorted xs] when the list [xs] is sorted with respect to [≤]. *)

(* We write [xs ≼ ys] when every element [x ∈ xs]
   and every element [y ∈ ys] satisfy [x ≤ y]. *)

Notation sorted xs   := (Sorted R xs).
Notation "xs '≼' ys" := (pairwise R xs ys) (at level 80).

(* A singleton list is sorted. *)

Lemma sorted_singleton x :
  sorted {[x]}.
Proof.
  unfold singleton, singleton_list. eauto.
Qed.

(* Two singleton segments are ordered in the same way as their elements. *)

Lemma pairwise_singleton_singleton x y :
  x ≤ y →
  {[x]} ≼ {[y]}.
Proof.
  intros.
  unfold singleton, singleton_list.
  unfold pairwise. intros x' y'. rewrite !list_elem_of_singleton.
  intros. subst. tauto.
Qed.

(* If [xs] is sorted and nonempty then its first element is a lower
   bound for every element of [xs]. *)

Lemma sorted_implies_bounded_l xs :
  sorted xs →
  len xs ≠ 0 →
  {[xs !!! 0]} ≼ xs.
  (* ∀ x, x ∈ xs → xs !!! 0 ≤ x *)
Proof.
  intros Hsorted Hlen.
  assert (Heq: xs = {[xs !!! 0]} ++ final_seg 1 xs) by (list; eauto).
  clear Hlen. rewrite Heq in Hsorted. rewrite Heq at 2. clear Heq.
  rewrite Sorted_app_iff in Hsorted; unpack.
  rewrite pairwise_app_right_iff; split.
  - eapply pairwise_singleton_singleton. reflexivity.
  - assumption.
Qed.

(* If [xs] is sorted and nonempty then its last element is an upper
   bound for every element of [xs]. *)

Lemma sorted_implies_bounded_r xs :
  sorted xs →
  len xs ≠ 0 →
  xs ≼ {[xs !!! (len xs - 1)]}.
  (* ∀ x, x ∈ xs → x ≤ xs !!! (len xs - 1) *)
Proof.
  intros Hsorted Hlen.
  assert (Heq: xs = initial_seg (len xs - 1) xs ++ {[xs !!! (len xs - 1)]})
    by (list; eauto).
  clear Hlen. rewrite Heq in Hsorted. rewrite Heq at 1. clear Heq.
  rewrite Sorted_app_iff in Hsorted; unpack.
  rewrite pairwise_app_left_iff; split.
  - assumption.
  - eapply pairwise_singleton_singleton. reflexivity.
Qed.

(* If [xs] and [ys] are both sorted and nonempty then, to guarantee
   [xs ≼ ys], it suffices to check that the last element of [xs] is
   ordered before the first element of [ys]. *)

Lemma boundary_test xs ys :
  sorted xs →
  sorted ys →
  len xs ≠ 0 →
  len ys ≠ 0 →
  xs !!! (len xs - 1) ≤ ys !!! 0 →
  xs ≼ ys.
Proof.
  intros.
  eapply pairwise_transitive_singleton with (y := ys !!! 0).
  + eapply pairwise_transitive_singleton with (y := xs !!! (len xs - 1)).
    - eauto using sorted_implies_bounded_r.
    - eauto using pairwise_singleton_singleton.
  + eauto using sorted_implies_bounded_l.
Qed.

(* If [xs] and [ys] are both sorted and nonempty then, to guarantee
   [sorted (xs ++ ys)], it suffices to check that the last element
   of [xs] is ordered before the first element of [ys]. *)

Lemma sorted_app_boundary xs ys :
  sorted xs →
  sorted ys →
  len xs ≠ 0 →
  len ys ≠ 0 →
  xs !!! (len xs - 1) ≤ ys !!! 0 →
  sorted (xs ++ ys).
Proof.
  eauto using Sorted_app, boundary_test with typeclass_instances.
Qed.

(* The definition of sortedness that is best suited for use with SMT
   solvers is this: *)

Definition smt_sorted xs :=
  ∀ i j,
  valid i xs →
  valid j xs →
  (i ≤ j)%nat →
  xs !!! i ≤ xs !!! j.

Lemma smt_sorted_nil :
  smt_sorted [].
Proof.
  unfold smt_sorted. list. lia.
Qed.

Lemma smt_sorted_cons x xs :
  smt_sorted xs →
  (∀ y, y ∈ xs → x ≤ y) →
  smt_sorted (x :: xs).
Proof.
  unfold smt_sorted. intros Hxs Hxy. intros.
  destruct (decide (i = 0)); destruct (decide (j = 0));
  subst; try lia; list in *.
  { reflexivity. }
  { eauto using list_elem_of_lookup_total_2 with lia. }
  { eauto with lia. }
Qed.

Lemma smt_sorted_uncons x xs :
  smt_sorted (x :: xs) →
  smt_sorted xs.
Proof.
  unfold smt_sorted. intros Hsorted. intros.
  change (xs !!! i) with ((x :: xs) !!! (S i)).
  change (xs !!! j) with ((x :: xs) !!! (S j)).
  eauto with lia.
Qed.

(* [sorted] implies [smt_sorted]. *)

Lemma sorted_smt_sorted xs :
  sorted xs →
  smt_sorted xs.
Proof.
  rewrite Sorted_iff_StronglySorted.
  induction 1.
  + eauto using smt_sorted_nil.
  + rename a into x, l into xs.
    rewrite Forall_forall in *.
    eauto using smt_sorted_cons.
Qed.

(* [smt_sorted] implies [sorted]. *)

Lemma smt_sorted_sorted xs :
  smt_sorted xs →
  sorted xs.
Proof.
  rewrite Sorted_iff_StronglySorted.
  induction xs as [|x xs]; intros Hsmt; constructor.
  + eauto using smt_sorted_uncons.
  + rewrite Forall_forall.
    unfold smt_sorted in Hsmt.
    intros y Hy.
    rewrite list_elem_of_lookup_total in Hy.
    destruct Hy as (j & ? & ?). subst y.
    change x with ((x :: xs) !!! 0).
    change (xs !!! j) with ((x :: xs) !!! (S j)).
    eauto with lia.
Qed.

Lemma smt_sorted_iff xs :
  smt_sorted xs ↔ sorted xs.
Proof.
  split; eauto using smt_sorted_sorted, sorted_smt_sorted.
Qed.

(* A statement that allows [smt_sorted] to be more easily exploited. *)

Lemma exploit_smt_sorted xs x y i j :
  smt_sorted xs →
  x = xs !!! i →
  y = xs !!! j →
  valid i xs →
  valid j xs →
  (i ≤ j)%nat →
  x ≤ y.
Proof.
  intros Hsorted. intros; subst. eauto.
Qed.

(* An SMT-style definition of the existence of a sorted segment. *)

Definition smt_sorted_seg i k xs :=
  ∀ j1 j2,
  valid j1 xs →
  valid j2 xs →
  (i ≤ j1) %nat → (j1 ≤ j2)%nat → (j2 < k)%nat →
  xs !!! j1 ≤ xs !!! j2.

Lemma smt_sorted_seg_iff i k xs :
  smt_sorted_seg i k xs ↔
  smt_sorted (seg i k xs).
Proof.
  unfold smt_sorted_seg, smt_sorted. split; intros Hsorted j1 j2; intros.
  + list in *. list.
    eauto with lia.
  + replace (xs !!! j1) with (seg i k xs !!! (j1 - i)) by (list; eauto).
    replace (xs !!! j2) with (seg i k xs !!! (j2 - i)) by (list; eauto).
    eauto with lia.
Qed.

Lemma smt_sorted_seg_iff' i k xs :
  smt_sorted_seg i k xs ↔
  sorted (seg i k xs).
Proof.
  rewrite <- smt_sorted_iff, smt_sorted_seg_iff. tauto.
Qed.

Lemma smt_sorted_seg_variance i k i' k' xs :
  smt_sorted_seg i k xs →
  (i ≤ i')%nat → (k' ≤ k)%nat →
  smt_sorted_seg i' k' xs.
Proof.
  unfold smt_sorted_seg, smt_sorted. eauto with lia.
Qed.

(* [smt_sorted_seg_except i k xs j] means that the segment [seg i k xs],
   deprived of its element at index [j], is sorted. *)

Definition smt_sorted_seg_except i k xs j :=
  ∀ j1 j2,
  valid j1 xs →
  valid j2 xs →
  (i ≤ j1) %nat → (j1 ≤ j2)%nat → (j2 < k)%nat →
  j1 ≠ j → j2 ≠ j →
  xs !!! j1 ≤ xs !!! j2.

Lemma smt_sorted_seg_except_iff i k xs j :
  i ≤ j ≤ k →
  smt_sorted_seg_except i k xs j ↔
  sorted (seg i j xs ++ seg (j + 1) k xs).
Proof.
Abort. (* TODO *)

End Sortedness.

Arguments smt_sorted {A H} R xs.
Arguments smt_sorted_seg {A H} R i k xs.
Arguments smt_sorted_seg_except {A H} R i k xs j.

(* -------------------------------------------------------------------------- *)

(* Three-way comparisons. *)

(* This type exists in the standard library:
Inductive comparison := Eq | Lt | Gt.
 *)

(* A [compare] function performs a three-way comparison. *)

(* [Compare A] means that the type [A] has a [compare] function. *)

Class Compare (A : Type) :=
  { compare : A → A → comparison }.

(* [Comparable A] means that the [compare] function at type [A]
   is correct with respect to the default preorder on this type. *)

Section Comparable.

Open Scope element_scope.

Context (A : Type) (R : relation A).

(* Standard mathematical notation. *)

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

(* Standard mathematical facts about the above definitions. *)

Lemma equiv_le x y :  x ≡ y → x ≤ y.
Proof. unfold equivalent. tauto. Qed.
Lemma lt_le x y :  x < y → x ≤ y.
Proof. unfold strict. tauto. Qed.
Lemma equiv_ge x y :  x ≡ y → x ≥ y.
Proof. unfold equivalent. tauto. Qed.
Lemma gt_ge x y :  x > y → x ≥ y.
Proof. eauto using lt_le. Qed.

Context `{Compare A}.

Class Comparable := {
  compare_spec :
    ∀ x y : A, CompareSpec (x ≡ y) (x < y) (x > y) (compare x y)
}.

Lemma wp_compare_Gt_Le `{Comparable} {B} (x y : A) (e1 e2 : B) (Q : B → Prop) :
  (x > y → wp e1 Q) →
  (x ≤ y → wp e2 Q) →
  wp (match compare x y with Gt => e1 | _ => e2 end) Q.
Proof.
  intros. destruct (compare_spec x y).
  + eauto using equiv_le.
  + eauto using lt_le.
  + eauto.
Qed.

End Comparable.

Global Ltac wp_compare :=
  simple eapply wp_compare_Gt_Le; [ eauto | intro | intro ].

(* -------------------------------------------------------------------------- *)

(* Insertion sort: [isortto]. *)

Section Sorting.

(* We assume that there is a preorder [R], also written [≤], on the type [A]. *)

(* We also assume that there is a three-way comparison function [compare].
   We use it only in 2-way comparisons.  *)

Context `{Inhabited A} `{PreOrder A R} `{Comparable A R}.

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
   in the input array. *)

Context `{PreOrder A R'}.

Infix "`precedes`" := R'
  (at level 70, no associativity) : element_scope.

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

Local Hint Unfold lex : core.

(* [lex] is a preorder. *)

Global Instance : PreOrder lex.
Proof.
  constructor; unfold lex.
  + intros x. eauto.
  + intros x y z. intuition eauto 8.
Qed.

(* Our definition of [lex] implies the usual definition. *)

Lemma lt_lex x y : x < y → lex x y.
Proof.
  split.
  + eauto.
  + intro. exfalso. unfold strict in *. tauto.
Qed.

Lemma le_le_lex x y : x ≤ y → x `precedes` y → lex x y.
Proof. eauto. Qed.

Local Hint Resolve lt_lex : core.

(* We write [sorted xs] when the list [xs] is sorted with respect to [lex]. *)

(* We write [xs ≼ ys] when every element [x ∈ xs]
   and every element [y ∈ ys] satisfy [x ≤ y]. *)

Notation sorted xs   := (Sorted lex xs).
Notation "xs '≼' ys" := (pairwise lex xs ys) (at level 80).

(* When stating the invariants of insertion sort, we have a choice between
   two styles: we can either reason in terms of list segments or reason in
   terms of the elements of these segments. In other words, we can either
   write [sorted (seg ...)] or write [smt_sorted_seg ...]. The first style
   is somewhat higher-level and makes intermediate goals more readable; the
   second style is somewhat lower-level and more amenable to SMT-style
   automation. *)

(* In the following, we use the low-level SMT style. This saves 10 to 15
   lines in the main proof. The earlier high-level style is visible in
   commit 8ecbec7bae8cb942b6e200f3e0fc719e444b87fb. *)

Notation smt_sorted_seg i k xs :=
  (smt_sorted_seg lex i k xs).
Notation smt_sorted_seg_except i k xs j :=
  (smt_sorted_seg_except lex i k xs j).

Ltac smt_reasoning :=
  unfold smt_sorted_seg, smt_sorted_seg_except in *;
  intros; list in *;
  rewrite ?list_lookup_total_insert;
  repeat case_decide; unpack; subst;
  (* Iterative deepening is required to avoid needless uses of
     transitivity, which create unresolved metavariables. *)
  eauto 2 with lia; eauto 3 with lia;
  eauto 4 with lia; eauto 5 with lia.

(* We write [xs ≃ ys] when the lists [xs] and [ys] are equivalent up to
   a permutation of their elements. *)

Local Infix "≃" := (@Permutation A)
  (at level 70, no associativity).

(* Insertion sort: the code. *)

Implicit Types _src _dst : array A.
Implicit Types src dst : list A.
Implicit Types _srcofs _dstofs _n : int.
Implicit Types srcofs dstofs n : nat.

(* [isortto src _srcofs dst _dstofs _n] sorts the array segment described
   by [src], [_srcofs], [_n]. The resulting data is written into the array
   segment described by [dst], [_dstofs], [_n]. The source and destination
   arrays must be distinct. *)

Definition isortto _src _srcofs _dst _dstofs _n :=
  (* Let [i] scan the source segment upwards. *)
  int.iter_up 0 _n _dst @@ λ _i _dst ,
    (* Extract [xi] at offset [i] in the source segment. *)
    do xi ← get _src (_srcofs + _i)%uint63 ;
    do (_dst, out) ← (
      (* Let [j] scan the sorted part of the destination segment, downwards. *)
      int.xiter_down (_dstofs + _i)%uint63 _dstofs _dst @@
      λ _ _j _dst continue break ,
        (* Read an element [xj] at offset [j] in the destination segment.
           If [xj ≥ xi] holds then move [xj] upwards by one position and
           continue. Otherwise stop. *)
        do xj ← get _dst _j ;
        match compare xj xi with
        | Gt      => do _dst ← set _dst (_j + 1) xj; continue _dst
        | Lt | Eq => break _dst _j
        end
    );
    (* Write [xi] into the logically empty slot of the array [dst]. *)
    match out with
    | Break _j =>
        set _dst (_j + 1) xi
    | Continue =>
        set _dst  _dstofs xi
    end.

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
  initial_seg dstofs dst = initial_seg dstofs dst' ∧
  final_seg (dstofs + i) dst = final_seg (dstofs + i) dst' ∧
  (* Inside the destination segment,
     we find a permutation of the data in the source segment. *)
  seg srcofs (srcofs + i) src
    ≃
  seg dstofs (dstofs + i) dst' ∧
  (* The destination segment is sorted. *)
  smt_sorted_seg dstofs (dstofs + i) dst'.
  (* in high-level style: sorted (seg dstofs (dstofs + i) dst') *)

Local Ltac intro_isortto_inv :=
  unfold isortto_inv; pack; list; tc3; list; tc3.

Local Ltac elim_isortto_inv dst' :=
  match goal with h: isortto_inv _ _ _ _ _ _ |- _ =>
    destruct h as (dst' & h); unpack in h
  end.

(* The invariant of the inner loop involves three auxiliary predicates,
   which we now define. We give them short names: [transported], [punched],
   and [above]. To find out what they mean, read on. *)

(* When we speak of an "extended source segment", we mean a source segment
   that extends up to index [srcofs + (i + 1)] in the source array.
   Similarly, an "extended destination segment" extends up to index
   [dstofs + (i + 1)] in the destination array. *)

(* [transported ...] states that, after performing the last write of [xi]
   into the destination array at offset [j], the extended source segment
   and the extended destination segment have the same content, up to a
   permutation. *)

Local Notation transported src srcofs dst dstofs i j := (
  let xi := src%list !!! (srcofs + i) in
  (* the extended source segment is a permutation of *)
  seg srcofs (srcofs + (i + 1)) src ≃
  (* the extended destination segment, updated with [xi] at index [j]. *)
  seg dstofs j dst ++ {[xi]} ++ seg (j + 1) (dstofs + (i + 1)) dst
) (only parsing).

(* [punched ...] states that the extended destination segment,
   deprived of the logically empty slot at index [j], is sorted. *)

(* In high-level style, one would write
   sorted (seg dstofs j dst ++ seg (j + 1) (dstofs + (i + 1)) dst *)

Local Notation punched dst dstofs i j := (
  smt_sorted_seg_except dstofs (dstofs + (i + 1)) dst (* except: *) j
) (only parsing).

(* [above ...] states that every element that lies in the second part of
   the extended destination segment (that is, the part that follows the
   logically empty slot at index [j]) is above [xi]. *)

(* Actually, every such element is *strictly* above [xi], but this fact
   does not seem to be needed. *)

(* In high-level style, one would write:
   sorted ({[xi]} ++ seg (j + 1) (dstofs + (i + 1)) dst) *)

Local Notation above src srcofs dst dstofs i j := (
  let xi := src !!! (srcofs + i) in
  ∀ j', j + 1 ≤ j' ≤ dstofs + i → lex xi (dst !!! j')
) (only parsing).

(* We refer to the conjunction of these three facts as [dst_inv ...],
   the destination invariant. *)

Local Definition dst_inv src srcofs dst dstofs i j :=
  transported src srcofs dst dstofs i j ∧
  punched dst dstofs i j ∧
  above src srcofs dst dstofs i j.

Local Ltac intro_dst_inv :=
  split; [| split ]; cbv zeta.

Local Ltac elim_dst_inv :=
  match goal with h: dst_inv _ _ _ _ _ _ |- _ =>
    destruct h as (Htransported & Hpunched & Habove);
    cbv zeta in Htransported, Habove;
    list in Htransported; list in Hpunched
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
  initial_seg dstofs dst = initial_seg dstofs dst' ∧
  final_seg (dstofs + (i + 1)) dst = final_seg (dstofs + (i + 1)) dst' ∧
  (* The content of the extended destination segment is described by
     the destination invariant [dst_inv ...]. If [out] is [Continue]
     then the logically empty slot lies at index [j]; otherwise it lies
     at index [j + 1]. Furthermore, in the latter case, [lex xj xi]
     holds. *)
  match out with
  | Continue =>
      dst_inv src srcofs dst' dstofs i j
  | Break _j =>
      dst_inv src srcofs dst' dstofs i (j + 1) ∧
      let xi := src !!! (srcofs + i) in
      let xj := dst' !!! j in
      isInt _j j ∧ dstofs ≤ j < dstofs + i ∧
      lex xj xi
  end.

Local Ltac intro_inner_inv :=
  unfold inner_inv; pack; list; tc3; list; tc3.

Local Ltac elim_inner_inv dst' :=
  match goal with h: inner_inv _ _ _ _ _ _ _ _ |- _ =>
    destruct h as (dst' & h); cbv zeta in h; list in h; unpack in h
  end.

(* The public specification of [isortto]. *)

Lemma wp_isortto _src src _srcofs srcofs _dst dst _dstofs dstofs _n n :
  isArray _src src →
  isInt _srcofs srcofs →
  isArray _dst dst →
  isInt _dstofs dstofs →
  isInt _n n →
  valid_seg srcofs (srcofs + n) src →
  valid_seg dstofs (dstofs + n) dst →
  smt_sorted R' src →
  wp (isortto _src _srcofs _dst _dstofs _n) (λ _dst,
    isortto_inv src srcofs dst dstofs n _dst
  ).
Proof.
  intros. unfold isortto.
  (* The outer loop. *)
  wp_iter_up (isortto_inv src srcofs dst dstofs).
  (* Initialization of the outer loop. *)
  { intro_isortto_inv. smt_reasoning. }
  (* The body of the outer loop. *)
  { clear dependent _dst. wp_up_intros i _dst. intros _i ?.
    elim_isortto_inv dst'.
    (* [dst'] is the content of the destination array upon entry into
       the body of the outer loop. *)
    wp_get xi.
    eapply wp_bind.
    { (* The inner loop. *)
      int.wp_xiter_down (inner_inv src srcofs dst dstofs i).
      (* Initialization of the inner loop. *)
      { intro_inner_inv; eauto using seg_equality_implication with lia.
        intro_dst_inv; list; recognize_singleton_segments;
        smt_reasoning.
        + split_seg_singleton_r src. use_known_permutation. list. eauto. }
      (* The body of the inner loop. *)
      clear dependent _dst.
      (* TODO need variant of [wp_down_intros] *)
      wp_loop_intros j0 j _dst. intros. subst j0.
      elim_inner_inv dst''.
      (* [dst''] is the content of the destination array upon entry into
         the body of the inner loop. *)
      wp_get xj.
      wp_compare.
      (* Case [xi < xj]. *)
      { elim_dst_inv.
        wp_set. wp_continue.
        intro_inner_inv. intro_dst_inv; try solve [ smt_reasoning ].
        (* The destination segment contains a permitted permutation. *)
        { list. use_known_permutation.
          recognize_singleton_segments.
          split_seg_singleton_r dst''.
          recognize_named_lookups.
          simplify_list_permutation_goal.
          (* Argue that swapping [xi] and [xj] is permitted. *)
          eapply Permutation_app_comm. }
      }
      (* Case [xj ≤ xi]. *)
      { wp_break. intro_inner_inv.
        + recognize_named_lookups.
          eapply le_le_lex. assumption.
          (* Proving [xj `precedes` xi] is the slightly tricky part.
             The argument is that [xj] comes from the extended source
             segment, whose rightmost element is [xi]. This is the only
             point where stability creates an extra proof obligation. *)
          elim_dst_inv.
          assert (Hseg: xj ∈ seg srcofs (srcofs + i + 1) src).
          { use_known_permutation. subst xj. eauto with elem_of_app lia. }
          rewrite lookup_total_elem_seg in Hseg by lia.
          destruct Hseg as (j' & ? & ?).
          eapply exploit_smt_sorted; eauto with lia. }
    }
    (* Epilogue of the inner loop. *)
    { clear dependent _dst. intros [ _dst out ].
      intros (j&Hj). list in Hj. unpack in Hj.
      (* Perform a case analysis on [out], so as to separately analyze
         the case where the loop has been stopped early and the case
         where it has finished normally. *)
      destruct out as [ _j' |]; elim_inner_inv dst''; elim_dst_inv.
      (* Case: we have broken out. *)
      { wp_set.
        intro_isortto_inv.
        (* The destination segment contains a permitted permutation. *)
        { use_known_permutation.
          recognize_singleton_segments.
          recognize_named_lookups.
          rewrite insert_seg by (list; lia); autorewrite with nat.
          reflexivity. }
        (* The destination segment is sorted. *)
        { smt_reasoning.
          + eapply transitivity; [| eassumption ]. eauto with lia. }
      }
      (* Case: the loop has finished normally. *)
      { assert (j = dstofs) by tauto. subst j.
        wp_set.
        intro_isortto_inv; try solve [ smt_reasoning ].
        (* The destination segment contains a permitted permutation. *)
        { use_known_permutation.
          recognize_singleton_segments. recognize_named_lookups.
          list. reflexivity. }
      }
    }
  }
Qed.

(* -------------------------------------------------------------------------- *)

(* In-place insertion sort: [isortto']. *)

(* [isortto' a _srcofs _dstofs _n] sorts the array segment described
   by [a], [_srcofs], [_n]. The resulting data is written into the array
   segment described by [a], [_dstofs], [_n]. The source and destination
   arrays are the same array. *)

(* The code is the same as in [isortto] except that the two arrays [src] and
   [dst] are replaced with a single array [a]. This change is necessary in
   order to ensure that the code always accesses the most recent version of
   the array, with time complexity O(1). If the same array was used as the
   source array and as the destination array in a call to [isortto] then
   every array access would become expensive, if a persistent array is used,
   or would fail, if a defensive non-persistent array is used (in OCaml). *)

Definition isortto' a _srcofs _dstofs _n :=
  int.iter_up 0 _n a @@ λ _i a ,
    do xi ← get a (_srcofs + _i)%uint63 ;
    do (a, out) ← (
      int.xiter_down (_dstofs + _i)%uint63 _dstofs a @@
      λ _ _j a continue break ,
        do xj ← get a _j ;
        match compare xj xi with
        | Gt      => do a ← set a (_j + 1) xj; continue a
        | Lt | Eq => break a _j
        end
    );
    match out with
    | Break _j =>
        set a (_j + 1) xi
    | Continue =>
        set a _dstofs xi
    end.

(* This code requires the source and destination segments to either be
   disjoint or to possibly overlap in a configuration the destination
   segment lies closer to the left end of the array than the source
   segment. The latter situation includes the case where the two segments
   coincide. In any of these situations case, the code is correct because
   [xi] is read before it is overwritten (if it is ever overwritten). In
   other words, when [xi] is read from the current array, the same value
   is read as if [xi] had been read from the initial unmodified array. *)

Definition isortto'_precondition srcofs dstofs n :=
  (srcofs + n ≤ dstofs ∨ dstofs ≤ srcofs)%nat.

Local Ltac destruct_isortto'_precondition :=
  match goal with h: isortto'_precondition _ _ _ |- _ =>
    destruct h end.

(* The public specification of [isortto']. *)

Lemma wp_isortto' a xs _srcofs srcofs _dstofs dstofs _n n :
  isArray a xs →
  isInt _srcofs srcofs →
  isInt _dstofs dstofs →
  isInt _n n →
  valid_seg srcofs (srcofs + n) xs →
  valid_seg dstofs (dstofs + n) xs →
  isortto'_precondition srcofs dstofs n →
  smt_sorted R' xs →
  wp (isortto' a _srcofs _dstofs _n) (λ a,
    isortto_inv xs srcofs xs dstofs n a
  ).
Proof.
  intros. unfold isortto'.
  (* The outer loop. *)
  wp_iter_up (isortto_inv xs srcofs xs dstofs).
  (* Initialization of the outer loop. *)
  { intro_isortto_inv. smt_reasoning. }
  (* The body of the outer loop. *)
  { clear dependent a. wp_up_intros i a. intros _i ?.
    elim_isortto_inv xs'.
    (* [xs'] is the content of the array upon entry into the body
       of the outer loop. *)
    wp_get xi.
    (* [xi] is the same value that would have been read out of the initial
       unmodified array. This is the key reason why the proof goes through
       with almost no change. *)
    assert (KEY: xs' !!! (srcofs + i) = xs !!! (srcofs + i)).
    { destruct_isortto'_precondition; lookup_through_seg. }
    eapply wp_bind.
    { (* The inner loop. *)
      int.wp_xiter_down (inner_inv xs srcofs xs dstofs i).
      (* Initialization of the inner loop. *)
      { intro_inner_inv; eauto using seg_equality_implication with lia.
        intro_dst_inv; list; recognize_singleton_segments;
        smt_reasoning.
        + split_seg_singleton_r xs. use_known_permutation. list. eauto. }
      (* The body of the inner loop. *)
      clear dependent a.
      (* TODO need variant of [wp_down_intros] *)
      wp_loop_intros j0 j a. intros. subst j0.
      elim_inner_inv xs''.
      (* [xs''] is the content of the array upon entry into the body of
         the inner loop. *)
      wp_get xj.
      wp_compare.
      (* Case [xi < xj]. *)
      { elim_dst_inv.
        wp_set. wp_continue.
        intro_inner_inv. intro_dst_inv; try solve [ smt_reasoning ].
        (* The destination segment contains a permitted permutation. *)
        { list. use_known_permutation.
          recognize_singleton_segments.
          split_seg_singleton_r xs''.
          recognize_named_lookups.
          simplify_list_permutation_goal.
          (* Argue that swapping [xi] and [xj] is permitted. *)
          eapply Permutation_app_comm. }
        (* The destination segment is sorted. [KEY] is exploited here. *)
        { smt_reasoning. recognize_named_lookups. eauto. }
      }
      (* Case [xj ≤ xi]. *)
      { wp_break. intro_inner_inv.
        + recognize_named_lookups.
          eapply le_le_lex. assumption.
          (* Proving [xj `precedes` xi] is the slightly tricky part.
             The argument is that [xj] comes from the extended source
             segment, whose rightmost element is [xi]. This is the only
             point where stability creates an extra proof obligation. *)
          elim_dst_inv.
          assert (Hseg: xj ∈ seg srcofs (srcofs + i + 1) xs).
          { use_known_permutation. subst xj. eauto with elem_of_app lia. }
          rewrite lookup_total_elem_seg in Hseg by lia.
          destruct Hseg as (j' & ? & ?).
          eapply exploit_smt_sorted; eauto with lia. }
    }
    (* Epilogue of the inner loop. *)
    { clear dependent a. intros [ a out ].
      intros (j&Hj). list in Hj. unpack in Hj.
      (* Perform a case analysis on [out], so as to separately analyze
         the case where the loop has been stopped early and the case
         where it has finished normally. *)
      destruct out as [ _j' |]; elim_inner_inv dst''; elim_dst_inv.
      (* Case: we have broken out. *)
      { wp_set.
        intro_isortto_inv.
        (* The destination segment contains a permitted permutation. *)
        { use_known_permutation.
          recognize_singleton_segments. recognize_named_lookups.
          rewrite insert_seg by (list; lia); autorewrite with nat.
          reflexivity. }
        (* The destination segment is sorted. [KEY] is used here. *)
        { smt_reasoning; rewrite KEY.
          + smt_reasoning.
          + eapply transitivity; [| eauto ]. eauto with lia. }
      }
      (* Case: the loop has finished normally. *)
      { assert (j = dstofs) by tauto. subst j.
        wp_set.
        intro_isortto_inv; try solve [ smt_reasoning ].
        (* The destination segment contains a permitted permutation. *)
        { use_known_permutation.
          recognize_singleton_segments. recognize_named_lookups.
          list. reflexivity. }
        (* The destination segment is sorted. [KEY] is used here. *)
        { smt_reasoning. rewrite KEY. smt_reasoning. }
      }
    }
  }
Qed.

(* -------------------------------------------------------------------------- *)

(* Merging two sorted arrays: [merge]. *)

Section MergeAux.

Variable _src1 _src2 : array A.
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

Global Instance Wf_order : WellFounded order :=
  wf_guard 32 wf_order.

Local Hint Extern 1 (order _ _) =>
  unfold order, order1, order2
: lia.

Section Code.
Open Scope uint63.

Equations merge_aux _i1 x1 _i2 x2 _dst _k : array A
by wf (_i1, _i2) order :=
merge_aux _i1 x1 _i2 x2 _dst _k :=
  match compare x1 x2 with
  | Lt | Eq =>
      do _dst ← set _dst _k x1 ;
      let _i1 := _i1 + 1 in
      let _k := _k + 1 in
      IF (_i1 <? _j1) THEN
        do x1 ← get _src1 _i1 ;
        merge_aux _i1 x1 _i2 x2 _dst _k
      ELSE
        blit _src2 _i2 _dst _k (_j2 - _i2)
  | Gt =>
      do _dst ← set _dst _k x2 ;
      let _i2 := _i2 + 1 in
      let _k := _k + 1 in
      IF (_i2 <? _j2) THEN
        do x2 ← get _src2 _i2 ;
        merge_aux _i1 x1 _i2 x2 _dst _k
      ELSE
        blit _src1 _i1 _dst _k (_j1 - _i1)
  end.

End Code.

(* TODO prove that if the two source segments are sorted for [lex]
   then so is the destination segment *)

Definition merge_aux_post src1 src2 i1 j1 i2 j2 dst k :=
  λ _dst,
  ∃ dst',
  isArray _dst dst' ∧
  len dst = len dst' ∧
  (* Outside of the destination segment [k, limit),
     the destination array is unmodified. *)
  let limit := k + (j1 - i1) + (j2 - i2) in
  initial_seg k dst = initial_seg k dst' ∧
  final_seg limit dst = final_seg limit dst' ∧
  (* Inside the destination segment, we find a permutation
     of the data contained in the two source segments, *)
  seg i1 j1 src1 ++ seg i2 j2 src2 ≃ seg k limit dst' ∧
  (* and the destination segment is sorted. *)
  smt_sorted_seg k limit dst'.

Local Ltac intro_merge_aux_post :=
  unfold merge_aux_post; pack.

Local Ltac decompose_segment :=
  match goal with
  h: seg ?i ?j ?xs ++ {[?x]} = seg ?i (?j + 1) ?ys |- _ =>
    rewrite (split_seg j ys) in h by lia;
    eapply app_inj_1 in h; [| list; lia ];
    unpack in h
  end.

Local Ltac elim_merge_aux_post :=
  let dst' := fresh "dst'" in
  match goal with h: merge_aux_post _ _ _ _ _ _ _ _ _ |- _ =>
    unfold merge_aux_post in h;
    destruct h as (dst' & h);
    list in h; unpack in h;
    repeat decompose_segment
  end.

Definition merge_aux_spec '((_i1, _i2) : int * int) :=
  ∀ src1 src2,
  isArray _src1 src1 →
  isArray _src2 src2 →
  ∀ j1 j2,
  isInt _j1 j1 →
  isInt _j2 j2 →
  ∀ i1, isInt _i1 i1 →
  valid_seg i1 j1 src1 →
  (i1 < j1)%nat →
  ∀ x1,
  x1 = src1 !!! i1 →
  ∀ i2, isInt _i2 i2 →
  valid_seg i2 j2 src2 →
  (i2 < j2)%nat →
  ∀ x2,
  x2 = src2 !!! i2 →
  smt_sorted_seg i1 j1 src1 →
  smt_sorted_seg i2 j2 src2 →
  ∀ _dst dst,
  isArray _dst dst →
  ∀Int _k k,
  let limit := k + (j1 - i1) + (j2 - i2) in
  valid_seg k limit dst →
  wp (merge_aux _i1 x1 _i2 x2 _dst _k)
     (merge_aux_post src1 src2 i1 j1 i2 j2 dst k).

Local Lemma foo k (x y : nat) :
  (0 < y)%nat →
  k + 1 + x + (y - 1) =
  k + x + y.
Proof. lia. Qed.

Local Hint Rewrite foo using lia : nat list.

Local Hint Resolve smt_sorted_seg_variance : lia.

Lemma wp_merge_aux _i1 _i2 : merge_aux_spec (_i1, _i2).
Proof.
  simple eapply (well_founded_ind Wf_order). clear _i1 _i2.
  intros (_i1, _i2) IH.
  unfold merge_aux_spec. intros. autorewrite with merge_aux.
  wp_compare.
  (* Case [x2 < x1]. *)
  { wp_set.
    wp_if.
    { simple eapply isBool_ltb; tc3. } (* TODO why not automated? *)
    (* Subcase [i2 + 1 < j2]. *)
    { wp_get x'2.
      (* We are now looking at the recursive call. *)
      eapply wp_conseq.
      + eapply (IH (_i1, _i2 + 1)%uint63); tc; try (list; lia).
      + clear dependent _dst. intros _dst Hpost.
        elim_merge_aux_post.
        intro_merge_aux_post; eauto 2.
        (* Prove that we have a permutation. *)
        { rewrite (split_seg (i2 + 1) src2) by lia.
          rewrite (split_seg (k + 1) dst') by lia.
          rewrite <- Hpost3.
          simplify_list_permutation_goal.
          rewrite Permutation_app_comm.
          simplify_list_permutation_goal.
          rewrite <- Hpost5.
          subst x2. list. reflexivity. }
        (* Prove that the destination segment is sorted. *)
        { admit. }
    }
    (* Subcase [i2 + 1 = j2]. *)
    { assert (j2 = i2 + 1) by lia. subst j2.
      wp_blit.
      intro_merge_aux_post; eauto 2; autorewrite with nat in *.
      + list. lia.
      + simplify_list_equality_goal. reflexivity.
      + simplify_list_equality_goal. reflexivity.
      + list.
        (* TODO [list] misses this rewriting step: *)
        erewrite (seg_none' _ _ dst) by lia. list.
        eapply Permutation_app_comm.
      + rewrite smt_sorted_seg_iff. list.
        erewrite (seg_none' _ _ dst) by lia. list. (* TODO again *)
        recognize_singleton_segments. recognize_named_lookups.
        admit.
    }
  }
  (* Case [x1 ≤ x2]. *)
  { wp_set.
    wp_if.
    { simple eapply isBool_ltb; tc3. } (* TODO why not automated? *)
    (* Subcase [i1 + 1 < j1]. *)
    { wp_get x'1.
      (* We are now looking at the recursive call. *)
      eapply wp_conseq.
      + eapply (IH (_i1 + 1, _i2)%uint63); tc; try (list; lia).
      + clear dependent _dst. intros _dst Hpost.
        elim_merge_aux_post.
        intro_merge_aux_post; eauto 2.
        (* Prove that we have a permutation. *)
        { rewrite (split_seg (i1 + 1) src1) by lia.
          rewrite (split_seg (k + 1) dst') by lia.
          rewrite <- Hpost3.
          simplify_list_permutation_goal.
          rewrite <- Hpost5.
          subst x1. list. reflexivity. }
        (* Prove that the destination segment is sorted. *)
        { admit. }
    }
    (* Subcase [i1 + 1 = j1]. *)
    { assert (j1 = i1 + 1) by lia. subst j1.
      wp_blit.
      intro_merge_aux_post; eauto 2; autorewrite with nat in *.
      + list. lia.
      + simplify_list_equality_goal. reflexivity.
      + simplify_list_equality_goal. reflexivity.
      + list.
        (* TODO [list] misses this rewriting step: *)
        erewrite (seg_none' _ _ dst) by lia. list.
        reflexivity.
      + rewrite smt_sorted_seg_iff. list.
        erewrite (seg_none' _ _ dst) by lia. list. (* TODO again *)
        recognize_singleton_segments. recognize_named_lookups.
        admit.
    }
  }
Admitted.

End MergeAux.

End Sorting.
