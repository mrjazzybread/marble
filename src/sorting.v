From Stdlib Require Import Program.Equality.
From Stdlib Require Export Sorting.Sorted.
Require Import stdpp.sorting.
From listz Require Import listz.
From marble Require Import orders.
  (* [strict_order_irreflexive] *)
  (* [strict_transitive_l], [strict_transitive_r] *)

(* This file establishes several properties of sorted lists. *)

(* It complements the libraries Coq.Sorting.Sorted and stdpp.sorting,
   which seem quite poor. *)

Local Ltac Zify.zify_pre_hook ::=
  lengths; ulength in *.

(* -------------------------------------------------------------------------- *)

(* We prefer {[x]} over [x] for singletons, because the former is more
   robust; it is not simplified away by [simpl]. *)

Local Lemma cons_is_append {A} x (xs : list A) :
  x :: xs = {[x]} ++ xs.
Proof. eauto. Qed.

(* -------------------------------------------------------------------------- *)

Section JustTransitive.

(* We assume a type [A] and a relation [R] on this type. *)

(* We assume that this relation is transitive. We do not assume anything
   else; e.g., [R] could be irreflexive, or it could be reflexive. *)

Context {A : Type}.
Context {R : A → A → Prop}.
Context {TR : Transitive R}.

(* Here, we write [x `R` y] when [x] is less than [y]. *)

Notation "x '`R`' y" := (R x y) (at level 70, no associativity).

Implicit Types x y z : A.
Implicit Types xs ys zs : list A.

(* Coq defines [Sorted] and [StronglySorted]; these notions are equivalent. *)

Lemma Sorted_iff_StronglySorted xs :
  Sorted R xs ↔ StronglySorted R xs.
Proof.
  split; eauto using Sorted_StronglySorted, StronglySorted_Sorted.
Qed.

(* Here, we write just [sorted]. *)

Notation sorted xs :=
  (Sorted R xs).

(* -------------------------------------------------------------------------- *)

(* We write [xs ≺ ys] when every element of the list [xs] is less than
   every element of the list [ys]. This notion is used in the statement
   of the lemma [Sorted_app_iff], which is as follows:

     sorted (xs ++ ys) ↔
     sorted xs ∧ sorted ys ∧ xs ≺ ys

   The notation [xs ≺ ys] looks nice inside this section. Unfortunately,
   outside this section, one must write [pairwise R xs ys], or redefine
   a new infix notation; it seems difficult to invent a generic infix
   notation. *)

Definition pairwise xs ys :=
  ∀ x y, x ∈ xs → y ∈ ys → x `R` y.

Notation "xs '≺' ys" := (pairwise xs ys) (at level 80).

(* -------------------------------------------------------------------------- *)

(* A paraphrase of the definition. *)

Lemma exploit_pairwise x y xs ys :
  xs ≺ ys → x ∈ xs → y ∈ ys → x `R` y.
Proof. unfold pairwise. eauto. Qed.

(* When an empty list appears on one side, [xs ≺ ys] is true. *)

Lemma pairwise_nil_left_iff ys :
  [] ≺ ys ↔ True.
Proof.
  unfold pairwise. split; [ tauto | intros _ ].
  + intros x y. rewrite elem_of_nil. tauto.
Qed.

Lemma pairwise_nil_right_iff xs :
  xs ≺ [] ↔ True.
Proof.
  unfold pairwise. split; [ tauto | intros _ ].
  + intros x y. rewrite elem_of_nil. tauto.
Qed.

Lemma pairwise_nil_left ys :
  [] ≺ ys.
Proof.
  rewrite pairwise_nil_left_iff. tauto.
Qed.

Lemma pairwise_nil_right xs :
  xs ≺ [].
Proof.
  rewrite pairwise_nil_right_iff. tauto.
Qed.

(* When a singleton appears on one side, [xs ≺ ys] can be simplified. *)

Lemma pairwise_singleton_singleton_iff x y :
  {[x]} ≺ {[y]} ↔
  x `R` y.
Proof.
  intros. unfold pairwise. split.
  + intros Hpw. eapply Hpw; rewrite list_elem_of_singleton; eauto.
  + intros Hpw x' y'. rewrite !list_elem_of_singleton. congruence.
Qed.

Lemma pairwise_singleton_left_iff x ys :
  {[x]} ≺ ys ↔ ∀ y, y ∈ ys → x `R` y.
Proof.
  unfold pairwise. split.
  + intros Hpw y Hy. eapply Hpw; rewrite ?list_elem_of_singleton; eauto.
  + intros H x' y. rewrite list_elem_of_singleton. intros. subst. eauto.
Qed.

Lemma pairwise_singleton_right_iff xs y :
  xs ≺ {[y]} ↔ ∀ x, x ∈ xs → x `R` y.
Proof.
  unfold pairwise. split.
  + intros Hpw x Hx. eapply Hpw; rewrite ?list_elem_of_singleton; eauto.
  + intros H x y'. rewrite list_elem_of_singleton. intros. subst. eauto.
Qed.

(* [pairwise] is transitive in the following restricted sense: transitivity
   requires the middle list to be nonempty. *)

Lemma pairwise_transitive_singleton xs y zs :
  xs ≺ {[y]} → {[y]} ≺ zs → xs ≺ zs.
Proof.
  unfold pairwise. intros Hl Hr x z.
  specialize (Hl x y).
  specialize (Hr y z).
  rewrite list_elem_of_singleton in *.
  eauto.
Qed.

Lemma pairwise_transitive_nonempty xs ys zs :
  ys ≠ [] →
  xs ≺ ys → ys ≺ zs → xs ≺ zs.
Proof.
  unfold pairwise. intros Hys Hl Hr x z.
  destruct ys as [| y ys]; [ congruence | clear Hys ].
  specialize (Hl x y).
  specialize (Hr y z).
  rewrite elem_of_cons in *.
  intuition eauto.
Qed.

(* [pairwise] interacts with list concatenation in a simple way. *)

Lemma pairwise_app_left_iff xs ys zs :
  xs ++ ys ≺ zs ↔ xs ≺ zs ∧ ys ≺ zs.
Proof.
  unfold pairwise. split; intros H.
  { split; intros x y ? ?; specialize (H x y);
    rewrite elem_of_app in H; tauto. }
  { intros x y. rewrite elem_of_app. firstorder. }
Qed.

Lemma pairwise_app_right_iff xs ys zs :
  xs ≺ ys ++ zs ↔ xs ≺ ys ∧ xs ≺ zs.
Proof.
  unfold pairwise. split; intros H.
  { split; intros x y ? ?; specialize (H x y);
    rewrite elem_of_app in H; tauto. }
  { intros x y. rewrite elem_of_app. firstorder. }
Qed.

(* We usually avoid using [::], as it can be expressed in terms of
   singletons and concatenation.  *)

Lemma pairwise_cons_left_iff x xs ys :
  x :: xs ≺ ys ↔ {[x]} ++ xs ≺ ys.
Proof. tauto. Qed.

Lemma pairwise_cons_right_iff xs y ys :
  xs ≺ y :: ys ↔ xs ≺ {[y]} ++ ys.
Proof. tauto. Qed.

(* An ad hoc combination. *)

Lemma pairwise_singleton_cons x y ys :
  x `R` y → {[x]} ≺ ys → {[x]} ≺ y :: ys.
Proof.
  rewrite pairwise_cons_right_iff.
  rewrite pairwise_app_right_iff.
  rewrite pairwise_singleton_singleton_iff.
  tauto.
Qed.

(* [Forall (R x) ys] can be reformulated in terms of [pairwise]. *)

(* This technical lemma is used below. *)

Local Lemma Forall_R_iff x ys :
  Forall (R x) ys ↔ {[x]} ≺ ys.
Proof.
  rewrite Forall_forall, pairwise_singleton_left_iff. eauto.
Qed.

(* In a context of the form [xs ≺ ys], one may rewrite
   using a list permutation fact. *)

Global Instance pairwise_permut :
  Proper (Permutation ==> Permutation ==> impl) pairwise.
Proof.
  intros xs xs' Hxs ys ys' Hys Hpw x y Hx Hy.
  eapply Hpw.
  + rewrite Hxs. eauto.
  + rewrite Hys. eauto.
Qed.

(* This lemma rephrases [exploit_pairwise], in a situation where the
   left-hand side is a singleton, and exploits a permutation on the
   right-hand side. *)

Lemma exploit_pairwise_singleton_left_permut x y xs ys :
  Permutation xs ys →
  {[x]} ≺ xs →
  y ∈ ys →
  x `R` y.
Proof.
  intros Hpermut Hpairwise Hy.
  rewrite Hpermut in Hpairwise.
  rewrite pairwise_singleton_left_iff in Hpairwise.
  eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* The empty list is sorted. *)

Lemma Sorted_empty :
  sorted [].
Proof.
  econstructor.
Qed.

Lemma Sorted_empty_iff :
  sorted [] ↔ True.
Proof.
  split; eauto using Sorted_empty.
Qed.

(* A singleton list is sorted. *)

Lemma Sorted_singleton x :
  sorted {[x]}.
Proof.
  econstructor.
  + eauto using Sorted_empty.
  + econstructor.
Qed.

Lemma Sorted_singleton_iff x :
  sorted {[x]} ↔ True.
Proof.
  split; eauto using Sorted_singleton.
Qed.

(* The concatenation [xs ++ ys] is sorted if and only if [xs] is sorted
   and [ys] is sorted and [xs ≺ ys] holds. *)

Lemma Sorted_app_inv_l xs ys :
  sorted (xs ++ ys) →
  sorted xs.
Proof.
  rewrite !Sorted_iff_StronglySorted. eauto using StronglySorted_app_1_l.
Qed.

Lemma Sorted_app_inv_r xs ys :
  sorted (xs ++ ys) →
  sorted ys.
Proof.
  rewrite !Sorted_iff_StronglySorted. eauto using StronglySorted_app_1_r.
Qed.

Lemma Sorted_app_inv_c xs ys :
  sorted (xs ++ ys) →
  xs ≺ ys.
Proof.
  rewrite !Sorted_iff_StronglySorted. intros.
  unfold pairwise. intros.
  eapply StronglySorted_app_1_elem_of; eauto.
Qed.

Lemma Sorted_app xs ys :
  sorted xs →
  sorted ys →
  xs ≺ ys →
  sorted (xs ++ ys).
Proof.
  rewrite !Sorted_iff_StronglySorted. revert xs ys.
  induction xs as [| x xs ]; intros ys Hxs Hys Hlt.
  { rewrite app_nil_l. assumption. }
  { rewrite <- app_comm_cons.
    dependent destruction Hxs. rewrite Forall_R_iff in *.
    rewrite cons_is_append in Hlt.
    rewrite pairwise_app_left_iff in Hlt. destruct Hlt.
    econstructor; rewrite ?Forall_R_iff, ?pairwise_app_right_iff; eauto. }
Qed.

Lemma Sorted_app_iff xs ys :
  sorted (xs ++ ys) ↔
  sorted xs ∧ sorted ys ∧ xs ≺ ys.
Proof.
  intuition eauto
    using Sorted_app_inv_l, Sorted_app_inv_c, Sorted_app_inv_r, Sorted_app.
Qed.

Lemma Sorted_app_app xs y zs :
  sorted (xs ++ zs) →
  xs ≺ {[y]} →
  {[y]} ≺ zs →
  sorted (xs ++ {[y]} ++ zs).
Proof.
  rewrite !Sorted_app_iff, pairwise_app_right_iff, Sorted_singleton_iff.
  tauto.
Qed.

Lemma split_sorted_seg i j k xs :
  sorted (seg i k xs) →
  valid_seg i j xs →
  valid_seg j k xs →
  seg i j xs ≺ seg j k xs.
Proof.
  intros Hsorted ??.
  rewrite (split_seg j) in Hsorted by lia.
  rewrite Sorted_app_iff in Hsorted.
  tauto.
Qed.

(* -------------------------------------------------------------------------- *)

Section SMT.

Context `{Inhabited A}.

(* [pairwise] applied to two segments remains true if the segments are
   shrunk. *)

Lemma seg_pairwise_seg_variance i1 j1 i2 j2 i'1 j'1 i'2 j'2 xs1 xs2 :
  seg i1 j1 xs1 ≺ seg i2 j2 xs2 →
  i1 ≤ i'1 → j'1 ≤ j1 → i2 ≤ i'2 → j'2 ≤ j2 →
  seg i'1 j'1 xs1 ≺ seg i'2 j'2 xs2.
Proof.
  (* The hypothesis [Inhabited A] should not be necessary for this
     result to hold, but it is used in this proof. *)
  unfold pairwise. intros. eauto using elem_seg_variance with lia.
Qed.

(* [pairwise] applied to two segments can be exploited as follows. *)

Lemma exploit_seg_pairwise_seg i1 j1 xs1 i2 j2 xs2 x1 k1 x2 k2 :
  seg i1 j1 xs1 ≺ seg i2 j2 xs2 →
  x1 = xs1 !!! k1 →
  x2 = xs2 !!! k2 →
  i1 `max` 0 ≤ k1 < j1 `min` length xs1 →
  i2 `max` 0 ≤ k2 < j2 `min` length xs2 →
  x1 `R` x2.
Proof.
  unfold pairwise. intros Hpw -> -> ??.
  erewrite (@lookup_total_through_seg _ _ i1 j1 k1) by eauto with lia.
  erewrite (@lookup_total_through_seg _ _ i2 j2 k2) by eauto with lia.
  eapply Hpw; eapply list_elem_of_lookup_total_2; ulength; lia.
Qed.

(* The definition of sortedness that seems best suited for use
   with SMT solvers is this. *)

(* The definition uses the strict hypothesis [j1 < j2], so as to be
   usable also in a context where [R] is possibly irreflexive. In a
   context where [R] is reflexive, this is equivalent to assuming
   [j1 ≤ j2]. See the lemmas [exploit_smt_sorted_strict] and
   [exploit_smt_sorted]. *)

Definition smt_sorted xs :=
  ∀ i j,
  valid i xs →
  valid j xs →
  i < j →
  xs !!! i `R` xs !!! j.

Lemma smt_sorted_nil :
  smt_sorted [].
Proof.
  unfold smt_sorted. list. lia.
Qed.

Lemma smt_sorted_cons x xs :
  smt_sorted xs →
  (∀ y, y ∈ xs → x `R` y) →
  smt_sorted ({[x]} ++ xs).
Proof.
  unfold smt_sorted. intros Hxs Hxy. intros.
  repeat case_lookup_app; length in *.
  { eauto using list_elem_of_lookup_total_2 with lia. }
  { eauto with lia. }
Qed.

Lemma smt_sorted_uncons x xs :
  smt_sorted ({[x]} ++ xs) →
  smt_sorted xs.
Proof.
  unfold smt_sorted. intros Hsorted. intros. length in *.
  rewrite <- (lookup_total_app_singleton_succ x xs i) by lia.
  rewrite <- (lookup_total_app_singleton_succ x xs j) by lia.
  eauto with lia.
Qed.

(* [sorted] implies [smt_sorted]. *)

Lemma sorted_smt_sorted xs :
  sorted xs →
  smt_sorted xs.
Proof.
  rewrite Sorted_iff_StronglySorted.
  induction 1; rewrite ?cons_is_append.
  + eauto using smt_sorted_nil.
  + rewrite Forall_forall in *.
    eauto using smt_sorted_cons.
Qed.

(* [smt_sorted] implies [sorted]. *)

Lemma smt_sorted_sorted xs :
  smt_sorted xs →
  sorted xs.
Proof.
  rewrite Sorted_iff_StronglySorted.
  induction xs as [|x xs]; intros Hsmt; constructor;
  rewrite cons_is_append in Hsmt.
  + eauto using smt_sorted_uncons.
  + rewrite Forall_forall.
    unfold smt_sorted in Hsmt.
    intros y Hy.
    rewrite list_elem_of_lookup_total in Hy.
    destruct Hy as (j & ? & ?). subst y.
    rewrite <- (lookup_total_app_singleton_zero x xs).
    rewrite <- (lookup_total_app_singleton_succ x xs j) by lia.
    eapply Hsmt; length; lia.
Qed.

Lemma smt_sorted_iff xs :
  smt_sorted xs ↔ sorted xs.
Proof.
  split; eauto using smt_sorted_sorted, sorted_smt_sorted.
Qed.

(* These lemmas allow [sorted] and [smt_sorted] to be easily exploited. *)

Lemma exploit_smt_sorted_strict xs x y i j :
  smt_sorted xs →
  x = xs !!! i →
  y = xs !!! j →
  valid i xs →
  valid j xs →
  i < j →
  x `R` y.
Proof.
  intros Hsorted. intros; subst. eapply Hsorted; eauto.
Qed.

Lemma exploit_smt_sorted {_ : Reflexive R} xs x y i j :
  smt_sorted xs →
  x = xs !!! i →
  y = xs !!! j →
  valid i xs →
  valid j xs →
  i ≤ j →
  x `R` y.
Proof.
  intros Hsorted; intros; subst.
  destruct (decide (i = j)).
  { subst j. eauto. }
  { eauto with lia. }
Qed.

Lemma exploit_sorted_strict xs x y i j :
  sorted xs →
  x = xs !!! i →
  y = xs !!! j →
  valid i xs →
  valid j xs →
  i < j →
  x `R` y.
Proof.
  rewrite <- smt_sorted_iff.
  eauto using exploit_smt_sorted_strict.
Qed.

Lemma exploit_sorted {_ : Reflexive R} xs x y i j :
  sorted xs →
  x = xs !!! i →
  y = xs !!! j →
  valid i xs →
  valid j xs →
  i ≤ j →
  x `R` y.
Proof.
  rewrite <- smt_sorted_iff.
  eauto using exploit_smt_sorted.
Qed.

(* An SMT-style definition of the existence of a sorted segment. *)

(* The definition uses the strict hypothesis [j1 < j2], so as to be
   usable also in a context where [R] is irreflexive. *)

Definition smt_sorted_seg i k xs :=
  ∀ j1 j2,
  valid j1 xs →
  valid j2 xs →
  i ≤ j1 → j1 < j2 → j2 < k →
  xs !!! j1 `R` xs !!! j2.

Lemma exploit_smt_sorted_seg {_ : Reflexive R} i k xs :
  smt_sorted_seg i k xs →
  ∀ j1 j2,
  valid j1 xs →
  valid j2 xs →
  i ≤ j1 → j1 ≤ j2 → j2 < k →
  xs !!! j1 `R` xs !!! j2.
Proof.
  intro Hsorted. intros.
  destruct (decide (j1 = j2)).
  { subst j2. eauto. }
  { eauto with lia. }
Qed.

Lemma smt_sorted_seg_iff i k xs :
  smt_sorted_seg i k xs ↔
  smt_sorted (seg i k xs).
Proof.
  unfold smt_sorted_seg, smt_sorted.
  split; intros Hsorted j1 j2; intros.
  + rewrite !lookup_total_seg by lia. eauto 2 with lia.
  + (* This looks like a situation that the tactic [lookup_through_seg]
       can handle; however, here, we are dealing with `R`, not equality. *)
    erewrite (@lookup_total_through_seg _ _ i k j1) by eauto with lia.
    erewrite (@lookup_total_through_seg _ _ i k j2) by eauto with lia.
    eauto 2 with lia.
Qed.

Lemma smt_sorted_seg_iff' i k xs :
  smt_sorted_seg i k xs ↔
  sorted (seg i k xs).
Proof.
  rewrite <- smt_sorted_iff, smt_sorted_seg_iff. tauto.
Qed.

Lemma exploit_sorted_seg {_ : Reflexive R} i k xs :
  sorted (seg i k xs) →
  ∀ j1 j2,
  valid j1 xs →
  valid j2 xs →
  i ≤ j1 → j1 ≤ j2 → j2 < k →
  xs !!! j1 `R` xs !!! j2.
Proof.
  rewrite <- smt_sorted_seg_iff'.
  eauto using exploit_smt_sorted_seg.
Qed.

(* If a segment is sorted, then a smaller segment is sorted. *)

Lemma smt_sorted_seg_variance i k i' k' xs :
  smt_sorted_seg i k xs →
  i ≤ i' → k' ≤ k →
  smt_sorted_seg i' k' xs.
Proof.
  unfold smt_sorted_seg, smt_sorted. eauto 2 with lia.
Qed.

Lemma sorted_seg_variance i k i' k' xs :
  sorted (seg i k xs) →
  i ≤ i' → k' ≤ k →
  sorted (seg i' k' xs).
Proof.
  rewrite <- !smt_sorted_seg_iff'. eauto using smt_sorted_seg_variance.
Qed.

(* [smt_sorted_seg_except i k xs j] means that the segment [seg i k xs],
   deprived of its element at index [j], is sorted. *)

Definition smt_sorted_seg_except i k xs j :=
  ∀ j1 j2,
  valid j1 xs →
  valid j2 xs →
  i ≤ j1 → j1 < j2 → j2 < k →
  j1 ≠ j → j2 ≠ j →
  xs !!! j1 `R` xs !!! j2.

Lemma exploit_smt_sorted_seg_except {_ : Reflexive R} i k xs j :
  smt_sorted_seg_except i k xs j →
  ∀ j1 j2,
  valid j1 xs →
  valid j2 xs →
  i ≤ j1 → j1 ≤ j2 → j2 < k →
  j1 ≠ j → j2 ≠ j →
  xs !!! j1 `R` xs !!! j2.
Proof.
  intro Hsorted. intros.
  destruct (decide (j1 = j2)).
  { subst j2. eauto. }
  { eauto with lia. }
Qed.

(* If the segment [seg i k xs] is sorted except at index [j],
   then once a suitable element [x] is written into this slot,
   the whole segment is sorted. *)

Lemma smt_sorted_seg_fill i k xs j x :
  smt_sorted_seg_except i k xs j →
  (i < j → xs !!! (j - 1) `R` x) →
  (j + 1 < k → x `R` xs !!! (j + 1)) →
  smt_sorted_seg i k (<[j := x]>xs).
Proof.
  unfold smt_sorted_seg_except, smt_sorted_seg.
  intros Hsorted Hleft Hright.
  intros j1 j2. intros. length in *.
  repeat case_lookup_insert.
  + destruct (decide (j2 = j + 1)).
    { subst j2. eauto. }
    { transitivity (xs !!! (j + 1)); eauto 2 with lia. }
  + destruct (decide (j1 = j - 1)).
    { subst j1. eauto with lia. }
    { transitivity (xs !!! (j - 1)); eauto 2 with lia. }
  + eapply Hsorted; lia.
Qed.

(* An alternate definition of [smt_sorted_seg_except]. *)

Lemma smt_sorted_seg_except_iff i k xs j :
  0 ≤ i ≤ j →
  j < k ≤ length xs →
  smt_sorted_seg_except i k xs j ↔
  sorted (seg i j xs ++ seg (j + 1) k xs).
Proof.
  (* This proof is a bit slow. *)
  rewrite <- smt_sorted_iff.
  unfold smt_sorted, smt_sorted_seg_except.
  split.
  + intros HsortedExcept. intros j1 j2. intros. length in *.
    repeat case_lookup_app; eauto 2 with lia.
  + intros Hsorted. intros j1 j2. intros.
    destruct (decide (valid (j1 - i) (seg i j xs))) as [Hcase1|Hcase1];
    destruct (decide (valid (j2 - i) (seg i j xs))) as [Hcase2|Hcase2];
    try lia; length in Hcase1; length in Hcase2.
    - specialize (Hsorted (j1 - i) (j2 - i)).
      list in Hsorted. zring in Hsorted. eauto 2 with lia.
    - specialize (Hsorted (j1 - i) (j2 - 1 - i)).
      list in Hsorted. zring in Hsorted. eauto 2 with lia.
    - specialize (Hsorted (j1 - 1 - i) (j2 - 1 - i)).
      list in Hsorted. zring in Hsorted. eauto 2 with lia.
Qed.

End SMT.

(* -------------------------------------------------------------------------- *)

Section AlsoReflexive.

Context {HRR : Reflexive R}.

Notation "xs '≼' ys" := (pairwise xs ys) (at level 80).

(* If [xs] is sorted and nonempty then its first element is a lower
   bound for every element of [xs]. *)

Lemma sorted_implies_bounded_l `{Inhabited A} x xs :
  sorted xs →
  (length xs ≠ 0 → x = xs !!! 0) →
  {[x]} ≼ xs.
Proof.
  intros Hsorted Hlookup.
  destruct (decide (length xs = 0)) as [ Hlen | Hlen ].
  { rewrite length_zero_iff_nil in *. subst xs.
    rewrite pairwise_nil_right_iff. eauto. }
  specialize (Hlookup Hlen). subst x.
  assert (Heq: xs = {[xs !!! 0]} ++ final_seg 1 xs)
    by chop_list_equality_goal.
  clear Hlen. rewrite Heq in Hsorted. rewrite Heq at 2. clear Heq.
  rewrite Sorted_app_iff in Hsorted. destruct Hsorted as (?&?&?).
  rewrite pairwise_app_right_iff; split.
  - rewrite pairwise_singleton_singleton_iff. reflexivity.
  - assumption.
Qed.

(* If [xs] is sorted and nonempty then its last element is an upper
   bound for every element of [xs]. *)

Lemma sorted_implies_bounded_r `{Inhabited A} x xs :
  sorted xs →
  (length xs ≠ 0 → x = xs !!! (length xs - 1)) →
  xs ≺ {[x]}.
Proof.
  intros Hsorted Hlookup.
  destruct (decide (length xs = 0)) as [ Hlen | Hlen ].
  { rewrite length_zero_iff_nil in *. subst xs.
    rewrite pairwise_nil_left_iff. eauto. }
  specialize (Hlookup Hlen). subst x.
  assert (Heq: xs = initial_seg (length xs - 1) xs
                    ++ {[xs !!! (length xs - 1)]})
    by chop_list_equality_goal.
  clear Hlen. rewrite Heq in Hsorted. rewrite Heq at 1. clear Heq.
  rewrite Sorted_app_iff in Hsorted. destruct Hsorted as (?&?&?).
  rewrite pairwise_app_left_iff; split.
  - assumption.
  - rewrite pairwise_singleton_singleton_iff. reflexivity.
Qed.

(* If [xs] and [ys] are both sorted and nonempty then, to guarantee
   [xs ≼ ys], it suffices to check that the last element of [xs] is
   ordered before the first element of [ys]. *)

Lemma boundary_test `{Inhabited A} xs ys :
  sorted xs →
  sorted ys →
  (
    length xs ≠ 0 →
    length ys ≠ 0 →
    xs !!! (length xs - 1) `R` ys !!! 0
  ) →
  xs ≼ ys.
Proof.
  intros ? ? Hleq.
  destruct (decide (length xs = 0)) as [ Hxs | Hxs ].
  { rewrite length_zero_iff_nil in *. subst xs.
    rewrite pairwise_nil_left_iff. eauto. }
  destruct (decide (length ys = 0)) as [ Hys | Hys ].
  { rewrite length_zero_iff_nil in *. subst ys.
    rewrite pairwise_nil_right_iff. eauto. }
  specialize (Hleq Hxs Hys).
  eapply pairwise_transitive_singleton with (y := ys !!! 0).
  + eapply pairwise_transitive_singleton with (y := xs !!! (length xs - 1)).
    - eauto using sorted_implies_bounded_r.
    - rewrite pairwise_singleton_singleton_iff. assumption.
  + eauto using sorted_implies_bounded_l.
Qed.

(* If [xs] and [ys] are both sorted and nonempty then, to guarantee
   [sorted (xs ++ ys)], it suffices to check that the last element
   of [xs] is ordered before the first element of [ys]. *)

Lemma sorted_app_boundary `{Inhabited A} xs ys :
  sorted xs →
  sorted ys →
  (
    length xs ≠ 0 →
    length ys ≠ 0 →
    xs !!! (length xs - 1) `R` ys !!! 0
  ) →
  sorted (xs ++ ys).
Proof.
  eauto using Sorted_app, boundary_test with typeclass_instances.
Qed.

End AlsoReflexive.

(* -------------------------------------------------------------------------- *)

(* Some lemmas about [HdRel]. *)

Lemma HdRel_trans xs x y :
  R x y -> HdRel R y xs -> HdRel R x xs.
Proof.
  intros. destruct xs; constructor.
  transitivity y;  [ done | by eapply HdRel_inv ].
Qed.

(* If a list is sorted, then being smaller than the head is equivalent to
   being smaller than all elements of the list. *)

Lemma Sorted_HdRel_iff x xs :
  Sorted R xs ->
  HdRel R x xs <-> Forall (R x) xs.
Proof.
  intros Hsort. induction xs as [| y ys ].
  { split; constructor. }
  { split.
    - intros Hhdrel.
      apply Sorted_inv in Hsort as [??].
      apply HdRel_inv in Hhdrel.
      constructor; auto.
      apply IHys; eauto using HdRel_trans.
    - intros Hforall. apply Forall_inv in Hforall; auto. }
Qed.

(* Let [xs] be a sorted list. Let [xs1] and [xs2] be two sorted lists
   that form a partitioning of [xs]. An arbitrary element [x] is less
   than the head of [xs] if it is less than the head of [xs1] and
   less than the head of [xs2]. *)

Lemma HdRel_Sorted_Permutation xs xs1 xs2 x :
  Sorted R xs ->
  xs1 ++ xs2 ≡ₚ xs ->
  Sorted R xs1 -> Sorted R xs2 ->
  HdRel R x xs1 -> HdRel R x xs2 ->
  HdRel R x xs.
Proof.
  intros ? Hperm ????.
  apply Sorted_HdRel_iff; try auto.
  rewrite <- Hperm.
  apply Forall_app.
  split; apply Sorted_HdRel_iff; auto.
Qed.

End JustTransitive.

Arguments pairwise {A} R xs ys.

Hint Rewrite
  @pairwise_nil_left_iff
  @pairwise_nil_right_iff
  @pairwise_singleton_singleton_iff
  @pairwise_app_left_iff
  @pairwise_app_right_iff
  @pairwise_cons_left_iff
  @pairwise_cons_right_iff
  using (eauto with typeclass_instances)
: pairwise.

Arguments smt_sorted {A} R {H} xs.
Arguments smt_sorted_seg {A} R {H} i k xs.
Arguments smt_sorted_seg_except {A} R {H} i k xs j.

(* -------------------------------------------------------------------------- *)

(* [Sorted] is covariant in the relation [R]. *)

Lemma HdRel_covariant {A} {R1 R2 : relation A} x xs :
  HdRel R1 x xs →
  (∀ x y, R1 x y → R2 x y) →
  HdRel R2 x xs.
Proof.
  induction 1; intros; econstructor; eauto.
Qed.

Lemma Sorted_covariant {A} {R1 R2 : relation A} xs :
  Sorted R1 xs →
  (∀ x y, R1 x y → R2 x y) →
  Sorted R2 xs.
Proof.
  induction 1; intros; econstructor; eauto using HdRel_covariant.
Qed.

(* If [R] is everywhere true then [Sorted R xs] is true. *)

Lemma HdRel_top {A} {R : relation A} x xs :
  (∀ x y, R x y) →
  HdRel R x xs.
Proof.
  induction xs; intros; econstructor; eauto.
Qed.

Lemma Sorted_top {A} {R : relation A} xs :
  (∀ x y, R x y) →
  Sorted R xs.
Proof.
  induction xs; intros; econstructor; eauto using HdRel_top.
Qed.

(* -------------------------------------------------------------------------- *)

(* We now assume that [R] is a strict order, that is, both transitive and
   irreflexive. *)

Section TransitiveAndIrreflexive.

Context {A : Type}.
Context {R : A → A → Prop}.
Context {Olt : StrictOrder R}.
Notation "x '<' y" := (R x y).
Notation "xs '≺' ys" := (pairwise R xs ys) (at level 80).
Implicit Types x y z : A.
Implicit Types xs ys zs : list A.

(* -------------------------------------------------------------------------- *)

(* If [{[x]} ≺ ys] holds then [x] cannot be an element of the list [ys]. *)

Lemma pairwise_contradiction_left x ys :
  {[x]} ≺ ys →
  x ∈ ys →
  False.
Proof.
  unfold pairwise. intros Hlt Hmember.
  specialize (Hlt x x). rewrite list_elem_of_singleton in Hlt.
  eauto using strict_order_irreflexive.
Qed.

(* A symmetric statement. *)

Lemma pairwise_contradiction_right xs y :
  xs ≺ {[y]} →
  y ∈ xs →
  False.
Proof.
  unfold pairwise. intros Hlt Hmember.
  specialize (Hlt y y). rewrite list_elem_of_singleton in Hlt.
  eauto using strict_order_irreflexive.
Qed.

(*[x < y] implies [{[x]} ≺ {[y]}]. *)

Lemma lt_pairwise x y :
  x < y →
  {[x]} ≺ {[y]}.
Proof.
  unfold pairwise. intros ? x' y'.
  rewrite !list_elem_of_singleton. intros; subst.
  assumption.
Qed.

(* A characteristic property of sorted lists, which is exploited in binary
   search trees: if [x] is less than [y], and if the elements of [zs] are
   greater than [y], then searching for [x] in the list [xs ++ {[y]} ++ zs]
   boils down to searching for [x] in the list [xs]. *)

Lemma bst_search_left x xs y zs :
  x < y →
  {[y]} ≺ zs →
  x ∈ xs ++ {[y]} ++ zs ↔ x ∈ xs.
Proof.
  assert (Transitive R) by typeclasses eauto.
  intros.
  rewrite !elem_of_app, list_elem_of_singleton.
  split; [| eauto ].
  intros [|[|]]; [| subst y; exfalso | exfalso ].
  { eauto. }
  { eauto using strict_order_irreflexive. }
  { eauto using lt_pairwise, pairwise_transitive_singleton,
                pairwise_contradiction_left. }
Qed.

(* A symmetric statement. *)

Lemma bst_search_right x xs y zs :
  y < x →
  xs ≺ {[y]} →
  x ∈ xs ++ {[y]} ++ zs ↔ x ∈ zs.
Proof.
  assert (Transitive R) by typeclasses eauto.
  intros.
  rewrite !elem_of_app, list_elem_of_singleton.
  split; [| eauto ].
  intros [|[|]]; [ exfalso | subst y; exfalso |].
  { eauto using lt_pairwise, pairwise_transitive_singleton,
                pairwise_contradiction_right. }
  { eauto using strict_order_irreflexive. }
  { eauto. }
Qed.

End TransitiveAndIrreflexive.

(* -------------------------------------------------------------------------- *)

(* Two useful tautologies. *)

Local Lemma share_common_conjunct (P Q Q' : Prop) :
  (P →      Q ↔ Q') →
  P ∧ Q  ↔  P ∧ Q'.
Proof.
  tauto.
Qed.

Lemma share_common_hypothesis {X} (Q Q' : X → Prop) :
  (∀ x,          Q x ↔ Q' x) →
  (∀ x, Q x)  ↔  (∀ x, Q' x).
Proof.
  firstorder.
Qed.

(* -------------------------------------------------------------------------- *)

(* We now assume not only that [lt] is a strict preorder, but also that [lt]
   is [strict le], where [le] is a preorder. *)

(* We define a notion of membership in a list modulo the preorder [le] and
   we establish a few key properties of this notion. These properties help
   reason about binary search trees in a setting where [le] is not
   necessarily antisymmetric. *)

Section PreOrder.

Context {A : Type}.
Context (le : A → A → Prop).
Context {Ple : PreOrder le}.
Local Set Warnings "-notation-overridden".
Notation "x '≤' y" := (le x y).

Notation lt := (strict le).
Notation "x '<' y" := (lt x y).
Notation "xs '≺' ys" := (pairwise lt xs ys) (at level 80).

Notation eq := (equivalent le).
Notation "x '≡' y" := (eq x y).

Implicit Types x y z : A.
Implicit Types xs ys zs : list A.
Implicit Type ox : option A.

(* We define membership in a list, up to the preorder [le], as a 3-place
   relation [member x xs ox'], where [x] is the desired element, [xs] is
   the list of interest, and [ox'] is the result of searching for [x] in
   the list: it is an element of the list that is equivalent to [x], if
   there is one. *)

(* Outside of this section, one must write [member le x xs ox']. *)

Definition member x xs ox' :=
  match ox' with
  | None =>
      (* If [ox'] is [None] then no element that is equivalent to [x]
         appears in the list. *)
      ∀ x', x ≡ x' → x' ∉ xs
  | Some x' =>
      (* If [ox'] is [Some x'] then [x'] is equivalent to [x] and
         appears in the list. *)
      x ≡ x' ∧ x' ∈ xs
  end.

(* No element is a member of the empty list. *)

Lemma member_empty x ox' :
  member x [] ox' ↔
  ox' = None.
Proof.
  destruct ox' as [x'|]; simpl member.
  (* Case: [Some]. *)
  { rewrite elem_of_nil. split; [ tauto | congruence ]. }
  (* Case: [None]. *)
  { split; [ tauto | intros ]. rewrite elem_of_nil. tauto. }
Qed.

(* A characteristic property of sorted lists, which is exploited in binary
   search trees: if [x] is less than [y], and if the elements of [zs] are
   greater than [y], then searching for [x] in the list [xs ++ [y] ++ zs]
   boils down to searching for [x] in the list [xs]. *)

(* This lemma is analogous to [bst_search_left], but uses [member x xs]
   instead of [x ∈ xs]. *)

Lemma bst_member_left x xs y zs ox' :
  x < y →
  {[y]} ≺ zs →
  member x (xs ++ {[y]} ++ zs) ox' ↔
  member x xs ox'.
Proof.
  intros. destruct ox' as [x'|]; unfold member.
  (* Case: [Some]. *)
  { apply share_common_conjunct; intro. destruct_equivalent.
    rewrite (@bst_search_left _ lt _) by eauto using strict_transitive_r.
    tauto. }
  (* Case: [None]. *)
  { apply share_common_hypothesis; intro x'.
    apply share_common_hypothesis; intro. destruct_equivalent.
    rewrite (@bst_search_left _ lt _) by eauto using strict_transitive_r.
    tauto. }
Qed.

(* A symmetric statement. *)

Lemma bst_member_right x xs y zs ox' :
  y < x →
  xs ≺ {[y]} →
  member x (xs ++ {[y]} ++ zs) ox' ↔
  member x zs ox'.
Proof.
  intros. destruct ox' as [x'|]; unfold member.
  (* Case: [Some]. *)
  { apply share_common_conjunct; intro. destruct_equivalent.
    rewrite (@bst_search_right _ lt _) by eauto using strict_transitive_l.
    tauto. }
  (* Case: [None]. *)
  { apply share_common_hypothesis; intro x'.
    apply share_common_hypothesis; intro. destruct_equivalent.
    rewrite (@bst_search_right _ lt _) by eauto using strict_transitive_l.
    tauto. }
Qed.

End PreOrder.

(* -------------------------------------------------------------------------- *)

(* The following tactics can prove that a list is sorted. *)

(* They are heavily used in sort.v. *)

(* [related] proves that two elements are related: that is, it solves a goal
   of the form [?R ?x ?y]. It either solves the goal or fails. *)

Ltac related :=
  (* [derecognize] substitutes away [lhs] and [rhs], if they are variables,
     and substitutes away any variables that are known to be equal to [lhs]
     and [rhs]. We use it as a preparatory step. Possibly one could adopt
     the opposite approach and use [recognize] as a preparatory step. *)
  derecognize;
  (* Now proceed. *)
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
   [Sorted R (xs ++ ys)]. It solves the first two subgoals and leaves the
   third one open. This subgoal is [R (xs !!! (length xs - 1)) (ys !!! 0)]
   and has access to the hypotheses [length xs ≠ 0] and [length ys ≠ 0]. *)

Ltac boundary :=
  eapply boundary_test; [ sorted | sorted | length; intros ? ?; list ]

(* [sorted_app] applies the lemma [Sorted_app] to a goal of the form
   [Sorted R (xs ++ ys)]. It solves the first two subgoals and leaves
   the third subgoal open. This subgoal is [xs ≼ ys]. *)

with sorted_app :=
  eapply Sorted_app; [ sorted | sorted |]

(* [pw] solves a goal of the form [xs ⋅≼ ys]. *)

(* [pw] either solves the goal or fails. *)

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
      (* Another option is to decompose concatenations. In an ideal world,
         [boundary; related] (above) would always succeed and there would
         be no need for this technique. (TODO) *)
      rewrite pairwise_app_right_iff; split; pw
  | |- pairwise _ (_ ++ _) _ =>
      rewrite pairwise_app_left_iff; split; pw

  | _ =>
      (* An assumption? *)
      solve [ eauto 2 ]
  end

(* [sorted] solves a goal of the form [Sorted ?R ?xs]. *)

(* [sorted] either solves the goal or fails. *)

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
