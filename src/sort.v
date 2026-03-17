From stdpp Require Import numbers list.
From Stdlib Require Import Uint63.
From Stdlib Require Import Array.PArray.
From Stdlib Require Import Sorting.Permutation Sorting.Sorted.
From Corelib Require Import Classes.RelationClasses.
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

(* A usable corollary of [sorted_smt_sorted]. *)

Lemma exploit_smt_sorted xs x y i j :
  sorted xs →
  x = xs !!! i →
  y = xs !!! j →
  valid i xs →
  valid j xs →
  (i ≤ j)%nat →
  x ≤ y.
Proof.
  intros Hsorted. intros; subst. eapply sorted_smt_sorted; eauto.
Qed.

End Sortedness.

Local Hint Resolve
  @sorted_singleton
  @Sorted_app_inv_l
  @Sorted_app_inv_r
: sorted.

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

Section InsertionSort.

(* We assume that there is a preorder [R], also written [≤], on the type [A]. *)

(* We also assume that there is a three-way comparison function [compare].
   We use it only in 2-way comparisons.  *)

Context `{Inhabited A} `{PreOrder A R} `{Comparable A R}.

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

Local Infix "≃" := (@Permutation A)
  (at level 70, no associativity).

(* We write [sorted xs] when the list [xs] is sorted with respect to [≤]. *)

(* We write [xs ≼ ys] when every element [x ∈ xs]
   and every element [y ∈ ys] satisfy [x ≤ y]. *)

Notation sorted xs   := (Sorted R xs).
Notation "xs '≼' ys" := (pairwise R xs ys) (at level 80).

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
    do (dst, out) ← (
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
        set dst (_j + 1) xi
    | Continue =>
        set dst  _dstofs xi
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
  sorted (seg dstofs (dstofs + i) dst').

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

Local Definition transported src srcofs dst dstofs i j :=
  let xi := src !!! (srcofs + i) in
  (* the extended source segment: *)
  seg srcofs (srcofs + (i + 1)) src
  (* is a permutation of: *)
    ≃
  (* the extended destination segment,
     updated with [xi] at index [j]. *)
  seg dstofs j dst ++ {[xi]} ++ seg (j + 1) (dstofs + (i + 1)) dst.

(* [punched ...] states that the extended destination segment,
   deprived of the logically empty slot at index [j], is sorted. *)

Local Definition punched dst dstofs i j :=
  sorted (
    seg dstofs j dst ++
    seg (j + 1) (dstofs + (i + 1)) dst
  ).

(* [above ...] states that every element that lies in the second part of
   the extended destination segment (that is, the part that follows the
   logically empty slot at index [j]) is above [xi]. *)

(* Actually, every such element is *strictly* above [xi], but this fact
   does not seem to be needed. *)

(* One could also write this fact under the form:
     {[xi]} ≼ seg (j + 1) (dstofs + (i + 1)) dst
   but this form does not seem to be significantly easier to work with. *)

Local Definition above src srcofs dst dstofs i j :=
  let xi := src !!! (srcofs + i) in
  sorted ({[xi]} ++ seg (j + 1) (dstofs + (i + 1)) dst).

(* We refer to the conjunction of these three facts as [dst_inv ...],
   the destination invariant. *)

Local Definition dst_inv src srcofs dst dstofs i j :=
  transported src srcofs dst dstofs i j ∧
  punched dst dstofs i j ∧
  above src srcofs dst dstofs i j.

Local Ltac intro_dst_inv :=
  split; [
    unfold transported in *
  | split; [
    unfold punched in *
  | unfold punched, above in *
  ]];
  autorewrite with nat in *.

Local Ltac elim_dst_inv :=
  match goal with h: dst_inv _ _ _ _ _ _ |- _ =>
    destruct h as (Htransported & Hpunched & Habove)
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
     at index [j + 1]. Furthermore, in the latter case, [xj ≤ xi] holds. *)
  match out with
  | Continue =>
      dst_inv src srcofs dst' dstofs i j
  | Break _j =>
      dst_inv src srcofs dst' dstofs i (j + 1) ∧
      let xi := src !!! (srcofs + i) in
      let xj := dst' !!! j in
      isInt _j j ∧ dstofs ≤ j < dstofs + i ∧
      xj ≤ xi
  end.

Local Ltac intro_inner_inv :=
  unfold inner_inv; pack; list; tc3; list; tc3.

Local Ltac elim_inner_inv dst' :=
  match goal with h: inner_inv _ _ _ _ _ _ _ _ |- _ =>
    destruct h as (dst' & h); cbv zeta in h; unpack in h
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
  wp (isortto _src _srcofs _dst _dstofs _n) (λ _dst,
    isortto_inv src srcofs dst dstofs n _dst
  ).
Proof.
  intros. unfold isortto.
  (* The outer loop. *)
  wp_iter_up (isortto_inv src srcofs dst dstofs).
  (* Initialization of the outer loop. *)
  { intro_isortto_inv. }
  (* The body of the outer loop. *)
  { clear dependent _dst. wp_loop_intros _i i _dst.
    elim_isortto_inv dst'.
    (* [dst'] is the content of the destination array upon entry into
       the body of the outer loop. *)
    wp_get xi.
    eapply wp_bind.
    { (* The inner loop. *)
      int.wp_xiter_down (inner_inv src srcofs dst dstofs i).
      (* Initialization of the inner loop. *)
      { intro_inner_inv; eauto using seg_equality_implication with lia.
        intro_dst_inv; list; rewrite ?(seg_is_singleton src) by lia;
        eauto 2 with sorted.
        + split_seg_singleton_r src. use_known_permutation. list. eauto. }
      (* The body of the inner loop. *)
      clear dependent _dst. wp_loop_intros _j j _dst.
      elim_inner_inv dst''.
      (* [dst''] is the content of the destination array upon entry into
         the body of the inner loop. *)
      wp_get xj.
      wp_compare.
      (* Case [xi < xj]. *)
      { elim_dst_inv.
        wp_set. wp_continue.
        intro_inner_inv. intro_dst_inv.
        (* The destination segment contains a permitted permutation. *)
        { list. use_known_permutation.
          rewrite (seg_is_singleton src) by lia.
          split_seg_singleton_r dst''.
          recognize_named_lookups.
          simplify_list_permutation_goal.
          (* Argue that swapping [xi] and [xj] is permitted. *)
          eapply Permutation_app_comm. }
        (* The destination segment, minus the hole, is sorted. *)
        { subst xj. list.
          rewrite app_assoc. list. (* associativity enables fusion *)
          exact Hpunched. }
        (* Following the hole, every element is above [xi]. *)
        { rewrite (split_seg_singleton_r dst'') in Hpunched by lia;
          autorewrite with nat in Hpunched.
          rewrite <- app_assoc in Hpunched.
          recognize_named_lookups.
          list.
          eapply sorted_app_boundary; list;
          eauto with lia sorted typeclass_instances. } }
      (* Case [xj ≤ xi]. *)
      { wp_break. intro_inner_inv.
        + recognize_named_lookups. assumption. }
    }
    (* Epilogue of the inner loop. *)
    { clear dependent _dst. intros [ _dst out ].
      intros (j&Hj). list in Hj. unpack in Hj.
      (* Perform a case analysis on [out], so as to separately analyze
         the case where the loop has been stopped early and the case
         where it has finished normally. *)
      destruct out as [ _j |]; elim_inner_inv dst''; elim_dst_inv.
      (* Case: we have broken out. *)
      { wp_set.
        intro_isortto_inv.
        (* The destination segment contains a permitted permutation. *)
        { unfold transported in *.
          use_known_permutation. recognize_named_lookups.
          rewrite insert_seg by (list; lia); autorewrite with nat.
          eauto. }
        (* The destination segment is sorted. *)
        { unfold above, punched in *.
          autorewrite with nat in Habove.
          rewrite insert_seg by (list; lia); autorewrite with nat.
          recognize_named_lookups.
          eapply sorted_app_boundary; list;
            eauto with lia sorted typeclass_instances. }
      }
      (* Case: the loop has finished normally. *)
      { assert (j = dstofs) by tauto. subst j.
        wp_set.
        intro_isortto_inv.
        (* The destination segment contains a permitted permutation. *)
        { unfold transported in *.
          use_known_permutation. recognize_named_lookups.
          list. eauto. }
        (* The destination segment is sorted. *)
        { unfold above in *. recognize_named_lookups. assumption. }
      }
    }
  }
Qed.

End InsertionSort.
