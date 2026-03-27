From stdpp Require Import numbers list well_founded.
From Stdlib Require Import Uint63.
From Stdlib Require Import Array.PArray.
From Stdlib Require Import Sorting.Permutation Sorting.Sorted.
From Corelib Require Import Classes.RelationClasses.
From marble Require Import equations.
From marble Require Import tactics list_extra list_tactics.
From marble Require Import iteration int wp wp_tactics array.
From marble Require Import orders sorting compare.
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

(* Local hints. *)

Local Hint Resolve
  Sorted_singleton
  Sorted_app_inv_l
  Sorted_app_inv_r
  sorted_seg_variance
  seg_pairwise_seg_variance
: lia.

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

Local Lemma exploit_seg_pairwise_seg i1 j1 xs1 i2 j2 xs2 x1 k1 x2 k2 :
  seg i1 j1 xs1 `precede` seg i2 j2 xs2 →
  x1 = xs1 !!! k1 →
  x2 = xs2 !!! k2 →
  i1 ≤ k1 < j1 `min` len xs1 →
  i2 ≤ k2 < j2 `min` len xs2 →
  x1 `precedes` x2.
Proof.
  intros. eapply exploit_seg_pairwise_seg; eauto.
Qed.

Local Hint Resolve exploit_seg_pairwise_seg : lia.

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

(* [lex x y] implies [x ≤ y]. *)

Lemma lex_elim x y : lex x y → x ≤ y.
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
Implicit Types srcofs dstofs n : nat.

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
     lex z0 z1 →
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
  lex y0 y1 →
  [x0] `precede` [y0; y1] →
  (∀ z0 z1 z2,
     lex z0 z1 → lex z1 z2 →
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
  lex y0 y1 → lex y1 y2 →
  [x0] `precede` [y0; y1; y2] →
  (∀ z0 z1 z2 z3,
     lex z0 z1 → lex z1 z2 → lex z2 z3 →
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
  lex x0 x1 →
  [x0; x1] `precede` [y0] →
  (∀ z0 z1 z2,
     lex z0 z1 → lex z1 z2 →
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
  lex x0 x1 → lex y0 y1 →
  [x0; x1] `precede` [y0; y1] →
  (∀ z0 z1 z2 z3,
     lex z0 z1 → lex z1 z2 → lex z2 z3 →
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
     lex z0 z1 → lex z1 z2 →
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
     lex z0 z1 → lex z1 z2 → lex z2 z3 →
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

Definition naive_sort_segment_2 a _i _k :=
  do x0 ← get a _i ;
  do x1 ← get a (_i + 1) ;
  sort2 x0 x1 @@ λ x0 x1,
  do a ← set a _k x0 ;
  do a ← set a (_k + 1) x1 ;
  a.

Definition naive_sort_segment_3 a _i _k :=
  do x0 ← get a _i ;
  do x1 ← get a (_i + 1) ;
  do x2 ← get a (_i + 2) ;
  sort3 x0 x1 x2 @@ λ x0 x1 x2,
  do a ← set a _k x0 ;
  do a ← set a (_k + 1) x1 ;
  do a ← set a (_k + 2) x2 ;
  a.

Definition naive_sort_segment_4 a _i _k :=
  do x0 ← get a _i ;
  do x1 ← get a (_i + 1) ;
  do x2 ← get a (_i + 2) ;
  do x3 ← get a (_i + 3) ;
  sort4 x0 x1 x2 x3 @@ λ x0 x1 x2 x3,
  do a ← set a _k x0 ;
  do a ← set a (_k + 1) x1 ;
  do a ← set a (_k + 2) x2 ;
  do a ← set a (_k + 3) x3 ;
  a.

End S.

(* The optimized versions. *)

Definition sort_segment_2 :=
  Eval compute -[bind leb] in naive_sort_segment_2.

Definition sort_segment_3 :=
  Eval compute -[bind leb] in naive_sort_segment_3.

Definition sort_segment_4 :=
  Eval compute -[bind leb] in naive_sort_segment_4.

(* Disable Notation "t .[ i ]" := (get t i). *)
(* Disable Notation "t .[ i <- a ]" := (set t i a). *)
(* Print sort_segment_2. *)
(* Print sort_segment_3. *)
(* Print sort_segment_4. *)

(* The specification of the [sort_segment] functions. *)

(* The array is unmodified outside of the segment [k, k+n). Within this
   segment, a sorted copy of the data that initially existed in the
   segment [i, i+n) is written. This is a stable sort. *)

Definition wp_sort_segment_spec sort_segment n :=
  ∀ a xs _i i _k k,
  isArray a xs →
  isInt _i i →
  isInt _k k →
  valid_seg i (i + n) xs →
  valid_seg k (k + n) xs →
  Sorted R' (seg i (i + n) xs) →
  wp (sort_segment a _i _k) (λ a, ∃ xs',
    isArray a xs' ∧
    len xs = len xs' ∧
    unmodified_outside_seg xs xs' k (k + n) ∧
    seg k (k + n) xs' ≃ seg i (i + n) xs ∧
    sorted (seg k (k + n) xs')
  ).

(* Each of these functions is correct. *)

Lemma wp_sort_segment_2 :
  wp_sort_segment_spec sort_segment_2 2.
Proof.
  unfold wp_sort_segment_spec. intros.
  change sort_segment_2 with naive_sort_segment_2.
  unfold naive_sort_segment_2.
  wp_get x0. wp_get x1.
  eapply wp_sort2.
  { pairwise. repeat split; eauto.
    subst. eapply exploit_sorted_seg; eauto with lia. }
  intros. wp_last Hpermut.
  repeat wp_set. wp_ret. eexists. pack.
  + eauto.
  + list. eauto.
  + list. eauto.
  + list. rewrite <- Hpermut. eapply identity_permutation.
    (* OK, let's use a big hammer: *)
    listx_total o. assert (o = 0 ∨ o = 1) as [|] by lia;
    subst o; simpl; list; assumption.
  + list.
    repeat (eapply sorted_app_boundary; eauto using Sorted_singleton).
Qed.

Lemma wp_sort_segment_3 :
  wp_sort_segment_spec sort_segment_3 3.
Proof.
  unfold wp_sort_segment_spec. intros.
  change sort_segment_3 with naive_sort_segment_3.
  unfold naive_sort_segment_3.
  wp_get x0. wp_get x1. wp_get x2.
  eapply wp_sort3;
    try solve [ subst; eapply exploit_sorted_seg; eauto with lia ].
  intros. wp_last Hpermut.
  repeat wp_set. wp_ret. eexists. pack.
  + eauto.
  + list. eauto.
  + list. eauto.
  + list. rewrite <- Hpermut. eapply identity_permutation.
    listx_total o.
    assert (o = 0 ∨ o = 1 ∨ o = 2) as [|[|]] by lia;
    subst o; simpl; list; assumption.
  + list.
    repeat (eapply sorted_app_boundary; eauto using Sorted_singleton).
Qed.

Lemma wp_sort_segment_4 :
  wp_sort_segment_spec sort_segment_4 4.
Proof.
  unfold wp_sort_segment_spec. intros.
  change sort_segment_4 with naive_sort_segment_4.
  unfold naive_sort_segment_4.
  wp_get x0. wp_get x1. wp_get x2. wp_get x3.
  eapply wp_sort4;
    try solve [ subst; eapply exploit_sorted_seg; eauto with lia ].
  intros. wp_last Hpermut.
  repeat wp_set. wp_ret. eexists. pack.
  + eauto.
  + list. eauto.
  + list. eauto.
  + list. rewrite <- Hpermut. eapply identity_permutation.
    listx_total o.
    assert (o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3) as [|[|[|]]] by lia;
    subst o; simpl; list; assumption.
  + list.
    repeat (eapply sorted_app_boundary; eauto using Sorted_singleton).
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
  split; [| split ]; cbv zeta.

Local Ltac elim_dst_inv :=
  match goal with h: dst_inv _ _ _ _ _ _ |- _ =>
    unfold dst_inv in h;
    destruct h as (Hpermut & Hsortedx & Habove);
    list in Hpermut; nat in Hsortedx
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
  Sorted R' (seg srcofs (srcofs + n) src) →
  wp (isortto _src _srcofs _dst _dstofs _n)
     (isortto_inv src srcofs dst dstofs n).
Proof.
  intros. unfold isortto.
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
      int.wp_xiter_down (inner_inv src srcofs dst dstofs i).
      (* Initialization of the inner loop. *)
      { intro_inner_inv. intro_dst_inv; list.
        + rewrite Hdata. list. reflexivity.
        + assumption.
        + recognize. pairwise. tauto. }
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
      { wp_break. intro_inner_inv.
        + recognize. eapply le_le_lex. assumption.
          (* Proving [xj `precedes` xi] is the slightly tricky part.
             The argument is that [xj] comes from the extended source
             segment, whose rightmost element is [xi]. This is the only
             point where stability creates an extra proof obligation. *)
          elim_dst_inv.
          assert (Hseg: xj ∈ seg srcofs (srcofs + i + 1) src).
          { rewrite <- Hpermut. subst xj. eauto with elem_of_app lia. }
          rewrite lookup_total_elem_seg in Hseg by lia.
          destruct Hseg as (j' & Hj' & Hxj). nat in Hj'.
          rewrite Hxj. subst xi.
          eapply exploit_sorted_seg; eauto with lia. }
      (* Case [xi < xj]. *)
      { elim_dst_inv.
        wp_set. wp_continue.
        intro_inner_inv. intro_dst_inv; list.
        (* Permutation. *)
        { rewrite <- Hpermut. clarify.
          rewrite (split_seg j dst'' dstofs (j + 1)) by lia. clarify.
          recognize. eapply Permutation_app_comm. }
        (* Sortedness except at [j]. *)
        { subst xj. list. rewrite app_assoc. list. (* UGLY *) assumption. }
        (* Ordering above [xi]. *)
        { recognize. pairwise. eauto. }}}
    (* Epilogue of the inner loop. *)
    { clear dependent _dst. intros [ _dst out ].
      intros (j&Hj). nat in Hj. unpack in Hj.
      (* Perform a case analysis on [out], so as to separately analyze
         the case where the loop has been stopped early and the case
         where it has finished normally. *)
      destruct out as [ _j' |]; elim_inner_inv dst''; elim_dst_inv.
      (* Case: we have broken out. *)
      { wp_set.
        intro_isortto_inv;
        rewrite insert_seg by (list; lia); nat.
        (* Permutation. *)
        { rewrite <- Hpermut. recognize. reflexivity. }
        (* Sortedness. *)
        { recognize.
          eapply Sorted_app_app; eauto.
          eapply boundary_test; tc3; intros _ _; list.
          assumption. }}
      (* Case: the loop has finished normally. *)
      { assert (j = dstofs) by tauto. subst j.
        wp_set.
        intro_isortto_inv.
        (* Permutation. *)
        { rewrite <- Hpermut. recognize. list. reflexivity. }
        (* Sortedness. *)
        { recognize. eapply Sorted_app; tc. }}}}
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

Lemma wp_isortto' a xs _srcofs srcofs _dstofs dstofs _n n :
  isArray a xs →
  isInt _srcofs srcofs →
  isInt _dstofs dstofs →
  isInt _n n →
  valid_seg srcofs (srcofs + n) xs →
  valid_seg dstofs (dstofs + n) xs →
  (srcofs + n ≤ dstofs ∨ dstofs ≤ srcofs)%nat → (* disjoint or overlap *)
  Sorted R' (seg srcofs (srcofs + n) xs) →
  wp (isortto' a _srcofs _dstofs _n)
     (isortto_inv xs srcofs xs dstofs n).
Proof.
  intros. unfold isortto'.
  (* The outer loop. *)
  wp_iter_up (isortto_inv xs srcofs xs dstofs).
  (* Initialization of the outer loop. *)
  { intro_isortto_inv. }
  (* The body of the outer loop. *)
  { clear dependent a. wp_up_intros i a. intros _i ?.
    elim_isortto_inv xs'.
    (* [xs'] is the content of the array
       upon entry into the body of the outer loop. *)
    wp_get xi.
    (* [xi] is the same value that would have been read out of the initial
       unmodified array. This is the key reason why the proof goes through
       with almost no change. *)
    assert (KEY: xs' !!! (srcofs + i) = xs !!! (srcofs + i)).
    { eapply equal_lookups_to_equal_segs; eauto with lia. }
    eapply wp_bind.
    { (* The inner loop. *)
      int.wp_xiter_down (inner_inv xs srcofs xs dstofs i).
      (* Initialization of the inner loop. *)
      { intro_inner_inv. intro_dst_inv; list.
        + rewrite Hdata. list. reflexivity.
        + assumption.
        + recognize. pairwise. tauto. }
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
      { wp_break. intro_inner_inv.
        + recognize. eapply le_le_lex. assumption.
          (* Proving [xj `precedes` xi] is the slightly tricky part.
             The argument is that [xj] comes from the extended source
             segment, whose rightmost element is [xi]. This is the only
             point where stability creates an extra proof obligation. *)
          elim_dst_inv.
          assert (Hseg: xj ∈ seg srcofs (srcofs + i + 1) xs).
          { rewrite <- Hpermut. subst xj. eauto with elem_of_app lia. }
          rewrite lookup_total_elem_seg in Hseg by lia.
          destruct Hseg as (j' & Hj' & Hxj). nat in Hj'.
          rewrite Hxj. rewrite KEY.
          eapply exploit_sorted_seg; eauto with lia. }
      (* Case [xi < xj]. *)
      { elim_dst_inv.
        wp_set. wp_continue.
        intro_inner_inv. intro_dst_inv; list.
        (* Permutation. *)
        { rewrite <- Hpermut. clarify.
          rewrite (split_seg j xs'' dstofs (j + 1)) by lia. clarify.
          recognize. eapply Permutation_app_comm. }
        (* Sortededness except at [j]. *)
        { subst xj. list. rewrite app_assoc. list. (* UGLY *) assumption. }
        (* Ordering above [xi]. KEY is used here. *)
        { recognize. pairwise. eauto. }}}
    (* Epilogue of the inner loop. *)
    { clear dependent a. intros [ a out ].
      intros (j&Hj). nat in Hj. unpack in Hj.
      (* Perform a case analysis on [out], so as to separately analyze
         the case where the loop has been stopped early and the case
         where it has finished normally. *)
      destruct out as [ _j' |]; elim_inner_inv dst''; elim_dst_inv.
      (* Case: we have broken out. *)
      { wp_set.
        intro_isortto_inv;
        rewrite insert_seg by (list; lia); nat.
        (* Permutation. *)
        { rewrite <- Hpermut. recognize. reflexivity. }
        (* Sortedness. [KEY] is used here. *)
        { recognize.
          eapply Sorted_app_app; eauto.
          eapply boundary_test; tc3; intros _ _; list.
          assumption. }}
      (* Case: the loop has finished normally. *)
      { assert (j = dstofs) by tauto. subst j.
        wp_set.
        intro_isortto_inv.
        (* The destination segment contains a permitted permutation. *)
        { rewrite <- Hpermut. recognize. list. reflexivity. }
        (* Sortedness. [KEY] is used here. *)
        { recognize. eapply Sorted_app; tc. }}}}
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
  split; [ eauto 2 | split; [ list; lia | pack ] ].

Local Ltac intro_merge_aux_post_list :=
  intro_merge_aux_post; list; recognize_empty_segments; list.

Local Ltac elim_merge_aux_post dst' :=
  match goal with h: merge_aux_post _ _ _ _ _ _ _ _ _ |- _ =>
    unfold merge_aux_post in h;
    destruct h as (dst' & h);
    list in h; unpack in h
  end.

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
  (i1 < j1)%nat →
  ∀ x1,
  x1 = src1 !!! i1 →
  ∀ i2, isInt _i2 i2 →
  ∀ j2, isInt _j2 j2 →
  valid_seg i2 j2 src2 →
  (i2 < j2)%nat →
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

Local Ltac tc ::=
  eauto 7 with typeclass_instances lia.

Lemma wp_merge_aux _j1 _j2 _i1 _i2 :
  merge_aux_spec _j1 _j2 (_i1, _i2).
Proof.
  simple eapply (well_founded_ind (Wf_order _j1 _j2)). clear _i1 _i2.
  intros (_i1, _i2) IH.
  unfold merge_aux_spec. intros.
  (* Now examine the code. *)
  autorewrite with merge_aux.
  wp_if.
  (* Case [x1 ≤ x2]. *)
  { wp_set.
    wp_if.
    (* Subcase [i1 + 1 < j1]. *)
    { wp_get x'1.
      (* We are now looking at the recursive call. *)
      eapply wp_conseq.
      { eapply (IH (_i1 + 1, _i2)%uint63); tc3; list; tc. }
      clear dependent _dst. intros _dst Hpost.
      elim_merge_aux_post dst'.
      intro_merge_aux_post.
      (* Unmodified. *)
      { rewrite Hpost1 by lia. list. reflexivity. }
      (* Permutation. *)
      { split_seg (k + 1) dst'. rewrite Hpost1 by lia. list.
        split_seg (i1 + 1) src1. rewrite Hpost2. clarify.
        recognize. reflexivity. }
      (* Sortedness. *)
      { split_seg (k + 1) dst'. rewrite Hpost1 by lia. list.
        eapply Sorted_app; eauto with lia.
        rewrite Hpost2.
        (* {[x1]} ≼ seg (i1 + 1) j1 src1 ++ seg i2 j2 src2 *)
        pairwise. split.
        + apply boundary_test; eauto 2 with lia.
          - eapply sorted_seg_variance; eauto 2 with lia.
          - intros _ _; list. subst x1.
            eapply exploit_sorted_seg; eauto with lia.
        + apply boundary_test; eauto 2 with lia.
          intros _ _; list. recognize. eauto with lia. }}
    (* Subcase [i1 + 1 = j1]. *)
    { assert (j1 = i1 + 1) by lia. subst j1.
      wp_blit.
      intro_merge_aux_post_list.
      + unmodified_outside_seg.
      + reflexivity.
      + recognize.
        eapply sorted_app_boundary; eauto 2 with lia.
        (* The fact that [x1] precedes [x2] is used here. *)
        intros _ _. list. recognize. eauto with lia. }}
  (* Case [x2 < x1]. *)
  { wp_set.
    wp_if.
    (* Subcase [i2 + 1 < j2]. *)
    { wp_get x'2.
      (* We are now looking at the recursive call. *)
      eapply wp_conseq.
      { eapply (IH (_i1, _i2 + 1)%uint63); tc3; list; tc. }
      clear dependent _dst. intros _dst Hpost.
      elim_merge_aux_post dst'.
      intro_merge_aux_post.
      (* Unmodified. *)
      { rewrite Hpost1 by lia. list. reflexivity. }
      (* Permutation. *)
      { split_seg (k + 1) dst'. rewrite Hpost1 by lia. list.
        split_seg (i2 + 1) src2. rewrite Hpost2. clarify.
        recognize. eapply Permutation_app_comm. }
      (* Sortedness. *)
      { split_seg (k + 1) dst'. rewrite Hpost1 by lia. list.
        eapply Sorted_app; eauto with lia.
        rewrite Hpost2.
        (* {[x2]} ≼ seg i1 j1 src1 ++ seg (i2 + 1) j2 src2 *)
        pairwise. split.
        + apply boundary_test; eauto 2 with lia.
          intros _ _; list. recognize. eauto.
        + apply boundary_test; eauto 2 with lia.
          - eapply sorted_seg_variance; eauto 2 with lia.
          - intros _ _; list. subst x2.
            eapply exploit_sorted_seg; eauto with lia. }}
    (* Subcase [i2 + 1 = j2]. *)
    { assert (j2 = i2 + 1) by lia. subst j2.
      wp_blit.
      intro_merge_aux_post_list.
      + unmodified_outside_seg.
      + eapply Permutation_app_comm.
      + recognize.
        eapply sorted_app_boundary; eauto 2 with lia.
        intros _ _. list. recognize. eauto. }}
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
  (i1 < j1)%nat →
  ∀ x1,
  x1 = src1 !!! i1 →
  ∀ i2, isInt _i2 i2 →
  ∀ j2, isInt _j2 j2 →
  valid_seg i2 j2 src2 →
  (i2 < j2)%nat →
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

Lemma wp_merge_aux_1 _j1 _j2 _i1 _i2 :
  merge_aux_1_spec _j1 _j2 (_i1, _i2).
Proof.
  simple eapply (well_founded_ind (Wf_order _j1 _j2)). clear _i1 _i2.
  intros (_i1, _i2) IH.
  unfold merge_aux_1_spec. intros.
  assert (Hi1: i1 = k + (j2 - i2)) by lia.
  autorewrite with merge_aux_1.
  arrays.
  wp_if.
  (* Case [x1 ≤ x2]. *)
  { wp_set.
    wp_if.
    (* Subcase [i1 + 1 < j1]. *)
    { wp_get x'1.
      match goal with h: x'1 = _ |- _ => rewrite <- Hi1 in h end.
      (* We are now looking at the recursive call. *)
      eapply wp_conseq.
      { eapply (IH (_i1 + 1, _i2)%uint63); tc3; list; tc3; tc. }
      clear dependent _src1. intros _src1 Hpost.
      elim_merge_aux_post dst'.
      intro_merge_aux_post.
      (* Unmodified. *)
      { rewrite Hpost1 by lia. list. reflexivity. }
      (* Permutation. *)
      { split_seg (k + 1) dst'. rewrite Hpost1 by lia. list.
        split_seg (i1 + 1) src1. rewrite Hpost2. clarify.
        recognize. eauto. }
      (* Sortedness. *)
      { split_seg (k + 1) dst'. rewrite Hpost1 by lia. list.
        eapply Sorted_app; eauto with lia.
        rewrite Hpost2.
        (* {[x1]} ≼ seg (i1 + 1) j1 src1 ++ seg i2 j2 src2 *)
        pairwise. split.
        + apply boundary_test; eauto 2 with lia.
          - eapply sorted_seg_variance; eauto 2 with lia.
          - intros _ _. list. subst x1.
            eapply exploit_sorted_seg; eauto with lia.
        + apply boundary_test; eauto 2 with lia.
          (* The fact that [x1] precedes [x2] is used here. *)
          intros _ _. list. recognize. eauto with lia. }}
    (* Subcase [i1 + 1 = j1]. *)
    { assert (j1 = i1 + 1) by lia. subst j1. nat in *.
      (* i1 = k + (j2 - i2) *) subst i1.
      wp_blit.
      intro_merge_aux_post_list.
      + unmodified_outside_seg.
      + reflexivity.
      + recognize.
        eapply sorted_app_boundary; eauto 2 with lia.
        (* The fact that [x1] precedes [x2] is used here. *)
        intros _ _. list. recognize. eauto with lia. }}
  (* Case [x2 < x1]. *)
  { wp_set.
    wp_if.
    (* Subcase [i2 + 1 < j2]. *)
    { wp_get x'2.
      (* We are now looking at the recursive call. *)
      eapply wp_conseq.
      { eapply (IH (_i1, _i2 + 1)%uint63); tc3; list; tc. }
      clear dependent _src1. intros _src1 Hpost.
      elim_merge_aux_post dst'.
      intro_merge_aux_post.
      (* Unmodified. *)
      { rewrite Hpost1 by lia. list. reflexivity. }
      (* Permutation. *)
      { split_seg (k + 1) dst'. rewrite Hpost1 by lia. list.
        split_seg (i2 + 1) src2. rewrite Hpost2. clarify.
        recognize. eapply Permutation_app_comm. }
      (* Sortedness. *)
      { split_seg (k + 1) dst'. rewrite Hpost1 by lia. list.
        eapply Sorted_app; eauto with lia.
        rewrite Hpost2.
        (* {[x2]} ≼ seg i1 j1 src1 ++ seg (i2 + 1) j2 src2 *)
        pairwise. split.
        + apply boundary_test; eauto 2 with lia.
          intros _ _; list. recognize. eauto.
        + apply boundary_test; eauto 2 with lia.
          - eapply sorted_seg_variance; eauto 2 with lia.
          - intros _ _; list. subst x2.
            eapply exploit_sorted_seg; eauto with lia. }}
    (* Subcase [i2 + 1 = j2]. *)
    { assert (j2 = i2 + 1) by lia. subst j2. nat in *.
      (* i1 = k + 1 *) subst i1.
      wp_ret.
      intro_merge_aux_post_list.
      + reflexivity.
      + recognize. eapply Permutation_app_comm.
      + eapply sorted_app_boundary; eauto 2 with lia.
        intros _ _. list. recognize. eauto. }}
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
  (i1 < j1)%nat →
  ∀ x1,
  x1 = src1 !!! i1 →
  ∀ i2, isInt _i2 i2 →
  ∀ j2, isInt _j2 j2 →
  valid_seg i2 j2 src2 →
  (i2 < j2)%nat →
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
  unfold merge_aux_2_spec. intros.
  assert (Hi2: i2 = k + (j1 - i1)) by lia.
  autorewrite with merge_aux_2.
  arrays.
  wp_if.
  (* Case [x1 ≤ x2]. *)
  { wp_set.
    wp_if.
    (* Subcase [i1 + 1 < j1]. *)
    { wp_get x'1.
      (* We are now looking at the recursive call. *)
      eapply wp_conseq.
      { eapply (IH (_i1 + 1, _i2)%uint63); tc3; list; tc3; tc. }
      clear dependent _src2. intros _src2 Hpost.
      elim_merge_aux_post dst'.
      intro_merge_aux_post.
      (* Unmodified. *)
      { rewrite Hpost1 by lia. list. reflexivity. }
      (* Permutation. *)
      { split_seg (k + 1) dst'. rewrite Hpost1 by lia. list.
        split_seg (i1 + 1) src1. rewrite Hpost2. clarify.
        recognize. eauto. }
      (* Sortedness. *)
      { split_seg (k + 1) dst'. rewrite Hpost1 by lia. list.
        eapply Sorted_app; eauto with lia.
        rewrite Hpost2.
        (* {[x1]} ≼ seg (i1 + 1) j1 src1 ++ seg i2 j2 src2 *)
        pairwise. split.
        + apply boundary_test; eauto 2 with lia.
          - eapply sorted_seg_variance; eauto 2 with lia.
          - intros _ _. list. subst x1.
            eapply exploit_sorted_seg; eauto with lia.
        + apply boundary_test; eauto 2 with lia.
          (* The fact that [x1] precedes [x2] is used here. *)
          intros _ _. list. recognize. eauto with lia. }}
    (* Subcase [i1 + 1 = j1]. *)
    { assert (j1 = i1 + 1) by lia. subst j1. nat in *.
      (* i2 = k + 1 *) subst i2.
      wp_ret.
      intro_merge_aux_post_list.
      + reflexivity.
      + recognize. reflexivity.
      + eapply sorted_app_boundary; eauto 2 with lia.
        (* The fact that [x1] precedes [x2] is used here. *)
        intros _ _. list. recognize. eauto with lia. }}
  (* Case [x2 < x1]. *)
  { wp_set.
    wp_if.
    (* Subcase [i2 + 1 < j2]. *)
    { wp_get x'2.
      match goal with h: x'2 = _ |- _ => rewrite <- Hi2 in h end.
      (* We are now looking at the recursive call. *)
      eapply wp_conseq.
      { eapply (IH (_i1, _i2 + 1)%uint63); tc3; list; tc3; tc. }
      clear dependent _src2. intros _src2 Hpost.
      elim_merge_aux_post dst'.
      intro_merge_aux_post.
      (* Unmodified. *)
      { rewrite Hpost1 by lia. list. reflexivity. }
      (* Permutation. *)
      { split_seg (k + 1) dst'. rewrite Hpost1 by lia. list.
        split_seg (i2 + 1) src2. rewrite Hpost2. clarify.
        recognize. eapply Permutation_app_comm. }
      (* Sortedness. *)
      { split_seg (k + 1) dst'. rewrite Hpost1 by lia. list.
        eapply Sorted_app; eauto with lia.
        rewrite Hpost2.
        (* {[x2]} ≼ seg i1 j1 src1 ++ seg (i2 + 1) j2 src2 *)
        pairwise. split.
        + apply boundary_test; eauto 2 with lia.
          intros _ _. list. recognize. eauto.
        + apply boundary_test; eauto 2 with lia.
          - eapply sorted_seg_variance; eauto 2 with lia.
          - intros _ _. list. subst x2.
            eapply exploit_sorted_seg; eauto with lia. }}
    (* Subcase [i2 + 1 = j2]. *)
    { assert (j2 = i2 + 1) by lia. subst j2. nat in *.
      wp_blit.
      intro_merge_aux_post_list.
      + unmodified_outside_seg.
      + rewrite <- Hi2. eapply Permutation_app_comm.
      + rewrite <- Hi2. recognize.
        eapply sorted_app_boundary; eauto 2 with lia.
        intros _ _. list. recognize. eauto. }}
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
  (i1 < j1)%nat →
  ∀ x1,
  x1 = dst !!! i1 →
  ∀ i2, isInt _i2 i2 →
  ∀ j2, isInt _j2 j2 →
  valid_seg i2 j2 dst →
  (i2 < j2)%nat →
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
  (j1 ≤ k ∨ limit ≤ i1)%nat →
  valid_seg k limit dst →
  wp (merge_aux_12 _j1 _j2 _i1 x1 _i2 x2 _dst _k)
     (merge_aux_post dst dst i1 j1 i2 j2 dst k).

Lemma wp_merge_aux_12 _j1 _j2 _i1 _i2 :
  merge_aux_12_spec _j1 _j2 (_i1, _i2).
Proof.
  simple eapply (well_founded_ind (Wf_order _j1 _j2)). clear _i1 _i2.
  intros (_i1, _i2) IH.
  unfold merge_aux_12_spec. intros.
  assert (Hi2: i2 = k + (j1 - i1)) by lia.
  autorewrite with merge_aux_12.
  arrays.
  wp_if.
  (* Case [x1 ≤ x2]. *)
  { wp_set.
    wp_if.
    (* Subcase [i1 + 1 < j1]. *)
    { wp_get x'1.
      (* We are now looking at the recursive call. *)
      eapply wp_conseq.
      { eapply (IH (_i1 + 1, _i2)%uint63); tc3; list; tc3; tc. }
      clear dependent _dst. intros _dst Hpost.
      elim_merge_aux_post dst'.
      intro_merge_aux_post.
      (* Unmodified. *)
      { rewrite Hpost1 by lia. list. reflexivity. }
      (* Prove that we have a permutation. *)
      { split_seg (k + 1) dst'. rewrite Hpost1 by lia. list.
        split_seg (i1 + 1) dst. rewrite Hpost2. clarify.
        recognize. eauto. }
      (* Sortedness. *)
      { split_seg (k + 1) dst'. rewrite Hpost1 by lia. list.
        eapply Sorted_app; eauto with lia.
        rewrite Hpost2.
        (* {[x1]} ≼ seg (i1 + 1) j1 dst ++ seg i2 j2 dst *)
        pairwise. split.
        + apply boundary_test; eauto 2 with lia.
          - eapply (sorted_seg_variance i1 j1); eauto 2 with lia.
          - intros _ _. list. subst x1.
            eapply (exploit_sorted_seg i1 j1); eauto 2 with lia.
        + apply boundary_test; eauto 2 with lia.
          (* The fact that [x1] precedes [x2] is used here. *)
          intros _ _. list. recognize. eauto with lia. }}
    (* Subcase [i1 + 1 = j1]. *)
    { assert (j1 = i1 + 1) by lia. subst j1. nat in *.
      (* i2 = k + 1 *) subst i2.
      wp_ret.
      intro_merge_aux_post_list.
      + reflexivity.
      + recognize. reflexivity.
      + eapply sorted_app_boundary; eauto 2 with lia.
        (* The fact that [x1] precedes [x2] is used here. *)
        intros _ _. list. recognize. eauto with lia. }}
  (* Case [x2 < x1]. *)
  { wp_set.
    wp_if.
    (* Subcase [i2 + 1 < j2]. *)
    { wp_get x'2.
      match goal with h: x'2 = _ |- _ => rewrite <- Hi2 in h end.
      (* We are now looking at the recursive call. *)
      eapply wp_conseq.
      { eapply (IH (_i1, _i2 + 1)%uint63); tc3; list; tc3; tc. }
      clear dependent _dst. intros _dst Hpost.
      elim_merge_aux_post dst'.
      intro_merge_aux_post.
      (* Unmodified. *)
      { rewrite Hpost1 by lia. list. reflexivity. }
      (* Permutation. *)
      { split_seg (k + 1) dst'. rewrite Hpost1 by lia. list.
        rewrite (split_seg (i2 + 1) dst i2 j2) by lia. rewrite Hpost2. clarify.
        rewrite Permutation_app_comm.
        clarify. recognize. eauto. }
      (* Sortedness. *)
      { split_seg (k + 1) dst'. rewrite Hpost1 by lia. list.
        eapply Sorted_app; eauto with lia.
        rewrite Hpost2.
        (* {[x2]} ≼ seg i1 j1 src1 ++ seg (i2 + 1) j2 src2 *)
        pairwise. split.
        + apply boundary_test; eauto 2 with lia.
          intros _ _. list. recognize. eauto.
        + apply boundary_test; eauto 2 with lia.
          - eapply sorted_seg_variance; eauto 2 with lia.
          - intros _ _. list. subst x2.
            eapply exploit_sorted_seg; eauto with lia. }}
    (* Subcase [i2 + 1 = j2]. *)
    { assert (j2 = i2 + 1) by lia. subst j2. nat in *.
      wp_blit.
      intro_merge_aux_post_list.
      + unmodified_outside_seg.
      + rewrite <- Hi2. eapply Permutation_app_comm.
      + rewrite <- Hi2.
        eapply sorted_app_boundary; eauto 2 with lia.
        intros _ _. list. recognize. eauto. }}
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
  (i1 < j1)%nat →
  ∀ i2, isInt _i2 i2 →
  ∀ j2, isInt _j2 j2 →
  valid_seg i2 j2 src2 →
  (i2 < j2)%nat →
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

Lemma wp_optimistic_merge _j1 _j2 _i1 _i2 :
  optimistic_merge_spec _j1 _j2 (_i1, _i2).
Proof.
  unfold optimistic_merge_spec. intros.
  unfold optimistic_merge.
  wp_get x1.
  wp_get x2.
  wp_if.
  (* Case [x1 ≤ x2]. *)
  { (* This remark is the key reason with this case works. *)
    assert (seg i1 j1 src1 ≼ seg i2 j2 src2).
    { apply boundary_test; eauto 2. intros _ _. list.
      recognize. eauto with lia. }
    wp_blit.
    wp_blit.
    wp_ret.
    (* UGLY *)
    match goal with h: isArray _ _ |- _ =>
      rewrite* @seg_none' in h by lia; list in h end.
    reckon (j2 - i2) in *. (* optional *)
    reckon (len dst) in *. (* optional *)
    (* Conclude. *)
    intro_merge_aux_post_list.
    + unmodified_outside_seg.
    + clarify. reflexivity.
    + reckon i2. reckon j2. eapply Sorted_app; eauto. }
  (* Case [x2 < x1]. *)
  { clear dependent x1.
    wp_get x1.
    wp_op wp_merge_aux _dst'.
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
  (i1 < j1)%nat →
  ∀ i2, isInt _i2 i2 →
  ∀ j2, isInt _j2 j2 →
  valid_seg i2 j2 src2 →
  (i2 < j2)%nat →
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
  { (* This remark is the key reason with this case works. *)
    assert (seg i1 j1 src1 ≼ seg i2 j2 src2).
    { apply boundary_test; eauto 2. intros _ _. list.
      recognize. eauto with lia. }
    wp_blit.
    wp_blit.
    (* UGLY *)
    match goal with h: isArray _ _ |- _ =>
      repeat rewrite* @seg_none' in h by lia; list in h end.
    reckon (len src1) in *.
    wp_ret.
    intro_merge_aux_post_list.
    + unmodified_outside_seg.
    + clarify. reflexivity.
    + reckon i2. reckon j2. eapply Sorted_app; eauto. }
  (* Case [x2 < x1]. *)
  { clear dependent x1.
    wp_get x1.
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
  (i1 < j1)%nat →
  ∀ i2, isInt _i2 i2 →
  ∀ j2, isInt _j2 j2 →
  valid_seg i2 j2 src2 →
  (i2 < j2)%nat →
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
  { (* This remark is the key reason with this case works. *)
    assert (seg i1 j1 src1 ≼ seg i2 j2 src2).
    { apply boundary_test; eauto 2. intros _ _. list.
      recognize. eauto with lia. }
    wp_blit.
    wp_ret.
    intro_merge_aux_post_list.
    + unmodified_outside_seg.
    + clarify. reflexivity.
    + reckon i2. reckon j2. eapply Sorted_app; eauto. }
  (* Case [x2 < x1]. *)
  { clear dependent x1.
    wp_get x1.
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
  (i1 < j1)%nat →
  ∀ i2, isInt _i2 i2 →
  ∀ j2, isInt _j2 j2 →
  valid_seg i2 j2 dst →
  (i2 < j2)%nat →
  sorted (seg i1 j1 dst) →
  sorted (seg i2 j2 dst) →
  seg i1 j1 dst `precede` seg i2 j2 dst →
  ∀Int _k k,
  (* The second source segment must be a suffix of the destination segment. *)
  let limit := k + (j1 - i1) + (j2 - i2) in
  limit = j2 →
  (* The first source segment and the destination segment must be disjoint. *)
  (j1 ≤ k ∨ limit ≤ i1)%nat →
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
  { (* This remark is the key reason with this case works. *)
    assert (seg i1 j1 dst ≼ seg i2 j2 dst).
    { apply boundary_test; eauto 2. intros _ _. list.
      recognize. eauto with lia. }
    wp_blit.
    wp_ret.
    intro_merge_aux_post_list.
    + unmodified_outside_seg.
    + clarify. reflexivity.
    + reckon i2. reckon j2. eapply Sorted_app; eauto. }
  (* Case [x2 < x1]. *)
  { clear dependent x1.
    wp_get x1.
    wp_op wp_merge_aux_12 _dst'.
    assumption. }
Qed.

(* -------------------------------------------------------------------------- *)

(* [sortto' _i _dst _k _n] sorts the source array segment described by the
   array [_dst], the start index [_i], and the length [_n]. The sorted data
   is written into the array segment described by [_dst], [_k], and [_n].
   The source and destination segments must be disjoint. This is a merge
   sort, with an insertion sort at the leaves. It is a stable sort. *)

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
    (a ≤ b ≤ len dst)%nat →
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
  unfold sortto'_post; pack; list; tc3; list; tc3.

Local Ltac elim_sortto'_post dst' :=
  match goal with h: sortto'_post _ _ _ _ _ |- _ =>
    destruct h as (dst' & h); unpack in h
  end.

(* I am not sure why, but this helps; otherwise [tc] can get stuck. *)

Local Hint Extern 1 (Sorted _ (seg _ _ _)) =>
  eapply sorted_seg_variance; eauto 2 with lia
: lia.

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
  unfold sortto'_spec. intros.
  autorewrite with sortto'.
  assert (isInt 5 5) by eauto using introIsInt. (* UGLY *)
  wp_if.
  (* Case [n ≤ cutoff]. *)
  { wp_op wp_isortto' _dst'. (* TODO wp_op_overwrite? *)
    clear dependent _dst. rename _dst' into _dst.
    elim_isortto_inv dst'. intro_sortto'_post. }
  (* Case [cutoff < n]. We actually need only [2 ≤ n]. *)
  { set (_n1 := (_n / 2)%uint63). set (n1 := (n / 2)).
    assert (isInt _n1 n1) by tc.
    set (_n2 := (_n - _n1)%uint63). set (n2 := (n - n1)).
    assert (isInt _n2 n2) by tc.
    (* The first recursive call. *)
    wp_op_overwrite IH _dst. wp_last HpostA.
    elim_sortto'_post dst'.
    (* This call has not affected the first half of the source segment. *)
    assert (frameA: seg i (i + n1) dst' = seg i (i + n1) dst)
      by eauto with lia.
    assert (Sorted R' (seg i (i + n1) dst'))
      by (rewrite frameA; eauto with lia).
    (* The second recursive call. *)
    wp_op_overwrite IH _dst. wp_last HpostB.
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
      eapply split_sorted_seg; eauto 2 with lia. }
    (* The third call: merging the sorted halves. *)
    wp_op_overwrite wp_optimistic_merge_12 _dst. wp_last HpostC.
    elim_merge_aux_post dst'''.
    (* Conclude. *)
    wp_ret. intro_sortto'_post.
    (* Nothing has been modified outside of the two segments. *)
    { rewrite HpostC1, HpostB1, HpostA1 by lia. reflexivity. }
    (* Permutation. *)
    { replace n with (n1 + n2) by lia. nat.
      rewrite HpostC2.
      rewrite HpostB2, frameB.
      rewrite frameA, HpostA2.
      list. reflexivity. }}
Qed.

(* -------------------------------------------------------------------------- *)

(* [sortto _src _i _dst _k _n] sorts the source array segment described by
   the array [_src], the start index [_i], and the length [_n]. The sorted
   data is written into the array segment described by [_dst], [_k], and
   [_n]. The arrays [_src] and [_dst] must be distinct. This is a merge
   sort, with an insertion sort at the leaves. It is a stable sort. *)

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
  unfold sortto_post; pack; list; tc3; list; tc3.

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
  unfold sortto_spec. intros.
  autorewrite with sortto.
  assert (isInt 5 5) by eauto using introIsInt. (* UGLY *)
  wp_if.
  (* Case [n ≤ cutoff]. *)
  { wp_op wp_isortto _dst'. (* TODO wp_op_overwrite? *)
    clear dependent _dst. rename _dst' into _dst.
    elim_isortto_inv dst'.
    wp_ret. intro_sortto_post. }
  (* Case [cutoff < n]. We actually need only [2 ≤ n]. *)
  { set (_n1 := (_n / 2)%uint63). set (n1 := (n / 2)).
    assert (isInt _n1 n1) by tc.
    set (_n2 := (_n - _n1)%uint63). set (n2 := (n - n1)).
    assert (isInt _n2 n2) by tc.
    (* The first recursive call. *)
    wp_op_overwrite_pair IH _src _dst. wp_last HpostA.
    elim_sortto_post src' dst'.
    (* This call has not affected the first half of the source segment. *)
    assert (frameA: seg i (i + n1) src' = seg i (i + n1) src)
      by eauto with lia.
    assert (Sorted R' (seg i (i + n1) src'))
      by (rewrite frameA; eauto with lia).
    (* The second call: a call to [sortto']. *)
    wp_op_overwrite wp_sortto' _src. wp_last HpostB.
    elim_sortto'_post src''.
    assert (seg (i + n2) (i + n2 + n1) src'' `precede`
            seg (k + n1) (k + n1 + n2) dst').
    { rewrite HpostB2. rewrite HpostA5. rewrite frameA.
      eapply split_sorted_seg; eauto 2 with lia. }
    (* The third call: merging the sorted halves. *)
    wp_op_overwrite wp_optimistic_merge_2 _dst. wp_last HpostC.
    elim_merge_aux_post dst'''.
    (* Conclude. *)
    wp_ret. intro_sortto_post.
    (* Nothing has been modified outside of the two segments. *)
    { rewrite HpostB1, HpostA3 by lia. reflexivity. }
    { rewrite HpostC1, HpostA4 by lia. reflexivity. }
    (* Permutation. *)
    { replace n with (n1 + n2) by lia. nat.
      rewrite HpostC2.
      rewrite HpostB2.
      rewrite frameA, HpostA5.
      list. reflexivity. }}
Qed.

(* -------------------------------------------------------------------------- *)

(* [sort_seg a _i _n] sorts the array segment described by the array [a],
   the start index [_i], and the length [_n]. The data is sorted in place.
   This is a merge sort, with an insertion sort at the leaves. It is a
   stable sort. *)

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
  unfold sort_seg_post; pack; list; tc3; list; tc3.

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
  intros. unfold sort_seg.
  assert (isInt 5 5) by eauto using introIsInt. (* UGLY *)
  wp_if.
  (* Case [n ≤ cutoff]. *)
  { wp_op_overwrite wp_isortto' a.
    elim_isortto_inv xs'.
    intro_sort_seg_post. }
  (* Case [cutoff < n]. We actually need only [2 ≤ n]. *)
  { set (_n1 := (_n / 2)%uint63). set (n1 := (n / 2)).
    assert (isInt _n1 n1) by tc.
    set (_n2 := (_n - _n1)%uint63). set (n2 := (n - n1)).
    assert (isInt _n2 n2) by tc.
    (* Allocation of an array. *)
    wp_make t.
    (* The first call. *)
    wp_op_overwrite_pair wp_sortto a t. wp_last HpostA.
    elim_sortto_post xs' dst'. list in *.
    (* This call has not affected the first half of [a]. *)
    assert (frameA: seg i (i + n1) xs' = seg i (i + n1) xs)
      by eauto with lia.
    assert (Sorted R' (seg i (i + n1) xs'))
      by (rewrite frameA; eauto with lia).
    (* The second call. *)
    wp_op_overwrite wp_sortto' a. wp_last HpostB.
    elim_sortto'_post xs''.
    replace (i + n2 + n1) with (i + n1 + n2) in * by lia.
    assert (seg (i + n2) (i + n1 + n2) xs'' `precede`
            seg 0 n2 dst').
    { rewrite HpostB2. rewrite HpostA5. rewrite frameA.
      eapply split_sorted_seg; eauto 2 with lia. }
    (* The third call: merging the sorted halves. *)
    wp_op_overwrite wp_optimistic_merge_1 a. wp_last HpostC.
    elim_merge_aux_post xs'''.
    (* Conclude. *)
    wp_ret. intro_sort_seg_post.
    (* Nothing has been modified outside of this segment. *)
    { rewrite HpostC1, HpostB1, HpostA3 by lia. reflexivity. }
    (* Permutation. *)
    { replace n with (n1 + n2) in * by lia. nat in *.
      rewrite HpostC2.
      rewrite HpostB2.
      rewrite frameA, HpostA5.
      list. reflexivity. }}
Qed.

(* -------------------------------------------------------------------------- *)

(* [sort a] sorts the array [a] in place. This is a merge sort, with an
   insertion sort at the leaves. It is a stable sort. *)

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
  unfold sort_post; pack; list; tc3; list; tc3.

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
  intros. unfold sort.
  wp_length _n.
  assert (Sorted R' (initial_seg (0 + len xs) xs))
    by (list; assumption).
  wp_op_overwrite wp_sort_seg a. wp_last Hpost.
  elim_sort_seg_post xs'. list in *.
  intro_sort_post.
Qed.

End Sort.

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

(* -------------------------------------------------------------------------- *)

(* A simplified specification of [sort_seg], without stability. *)

Lemma wp_sort_seg' `{Inhabited A, PreOrder A R, LebSpec A R} a xs _i i _n n :
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
  (* As we does not care about stability, we let [R'] be the relation
     that is everywhere true. This is a preorder, and the array [xs]
     is (trivially) sorted with respect to this relation. *)
  set (R' := λ x y : A, True).
  assert (PreOrder R').
  { unfold R'. constructor; eauto. }
  assert (Sorted R' (seg i (i + n) xs)).
  { unfold R'. eapply Sorted_top; eauto. }
  (* Therefore we are allowed to sort with respect to [R]. *)
  wp_op_overwrite (@wp_sort_seg A _ R _ _ _ R' _) a.
  elim_sort_seg_post xs'.
  (* The segment is now sorted with respect to the lexicographic ordering
     of [R] and [R'], which is the same thing as [R]. *)
  specialize (@lex_elim A R R'); intro.
  eauto 7 using Sorted_covariant.
Qed.

Global Ltac wp_sort_seg a :=
  wp_op_overwrite @wp_sort_seg' a.

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
  (* As we does not care about stability, we let [R'] be the relation
     that is everywhere true. This is a preorder, and the array [xs]
     is (trivially) sorted with respect to this relation. *)
  set (R' := λ x y : A, True).
  assert (PreOrder R').
  { unfold R'. constructor; eauto. }
  assert (Sorted R' xs).
  { unfold R'. eapply Sorted_top; eauto. }
  (* Therefore we are allowed to sort with respect to [R]. *)
  wp_op_overwrite (@wp_sort A _ R _ _ _ R' _) a.
  elim_sort_post xs'.
  (* The array is now sorted with respect to the lexicographic ordering
     of [R] and [R'], which is the same thing as [R]. *)
  specialize (@lex_elim A R R'); intro.
  eauto 6 using Sorted_covariant.
Qed.

Global Ltac wp_sort a :=
  wp_op_overwrite @wp_sort' a.

(* -------------------------------------------------------------------------- *)
