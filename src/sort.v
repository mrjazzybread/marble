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
        intro_dst_inv; list; recognize; smt_reasoning.
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
          split_seg_singleton_r dst''.
          recognize. simplify_list_permutation_goal.
          (* Argue that swapping [xi] and [xj] is permitted. *)
          eapply Permutation_app_comm. }
      }
      (* Case [xj ≤ xi]. *)
      { wp_break. intro_inner_inv.
        + recognize. eapply le_le_lex. assumption.
          (* Proving [xj `precedes` xi] is the slightly tricky part.
             The argument is that [xj] comes from the extended source
             segment, whose rightmost element is [xi]. This is the only
             point where stability creates an extra proof obligation. *)
          elim_dst_inv.
          assert (Hseg: xj ∈ seg srcofs (srcofs + i + 1) src).
          { use_known_permutation. subst xj. eauto with elem_of_app lia. }
          rewrite lookup_total_elem_seg in Hseg by lia.
          destruct Hseg as (j' & Hj' & ?). list in Hj'.
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
        { use_known_permutation. recognize.
          rewrite insert_seg by (list; lia); nat.
          reflexivity. }
        (* The destination segment is sorted. *)
        { eapply smt_sorted_seg_fill; eauto 2; intros; list; subst xi.
          + assumption.
          + eapply Habove. lia. }
      }
      (* Case: the loop has finished normally. *)
      { assert (j = dstofs) by tauto. subst j.
        wp_set.
        intro_isortto_inv; try solve [ smt_reasoning ].
        (* The destination segment contains a permitted permutation. *)
        { use_known_permutation. recognize. list. reflexivity. }
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
   disjoint or to possibly overlap in a configuration where the destination
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
        intro_dst_inv; list; recognize; smt_reasoning.
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
          split_seg_singleton_r xs''.
          recognize. simplify_list_permutation_goal.
          (* Argue that swapping [xi] and [xj] is permitted. *)
          eapply Permutation_app_comm. }
        (* The destination segment is sorted. [KEY] is exploited here. *)
        { smt_reasoning. recognize. eauto. }
      }
      (* Case [xj ≤ xi]. *)
      { wp_break. intro_inner_inv.
        + recognize. eapply le_le_lex. assumption.
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
        { use_known_permutation. recognize.
          rewrite insert_seg by (list; lia); nat.
          reflexivity. }
        (* The destination segment is sorted. [KEY] is used here. *)
        { eapply smt_sorted_seg_fill; eauto 2; intros; list; subst xi;
          rewrite KEY.
          + assumption.
          + eapply Habove. lia. }
      }
      (* Case: the loop has finished normally. *)
      { assert (j = dstofs) by tauto. subst j.
        wp_set.
        intro_isortto_inv; try solve [ smt_reasoning ].
        (* The destination segment contains a permitted permutation. *)
        { use_known_permutation. recognize. list. reflexivity. }
        (* The destination segment is sorted. [KEY] is used here. *)
        { smt_reasoning. rewrite KEY. smt_reasoning. }
      }
    }
  }
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
  initial_seg k dst = initial_seg k dst' ∧
  final_seg limit dst = final_seg limit dst' ∧
  (* Inside the destination segment, we find a permutation
     of the data contained in the two source segments, *)
  seg i1 j1 src1 ++ seg i2 j2 src2 ≃ seg k limit dst' ∧
  (* and the destination segment is sorted. *)
  sorted (seg k limit dst').

Local Ltac intro_merge_aux_post :=
  unfold merge_aux_post; pack.

Local Ltac elim_merge_aux_post :=
  let dst' := fresh "dst'" in
  match goal with h: merge_aux_post _ _ _ _ _ _ _ _ _ |- _ =>
    unfold merge_aux_post in h;
    destruct h as (dst' & h);
    list in h; unpack in h;
    repeat decompose_segment
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

Local Hint Resolve
  Sorted_singleton
  sorted_seg_variance
  seg_pairwise_seg_variance
: lia.

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
  wp_compare.
  (* Case [x2 < x1]. *)
  { wp_set.
    wp_if.
    (* Subcase [i2 + 1 < j2]. *)
    { wp_get x'2.
      (* We are now looking at the recursive call. *)
      eapply wp_conseq.
      { eapply (IH (_i1, _i2 + 1)%uint63); tc3; list; tc. }
      clear dependent _dst. intros _dst Hpost.
      elim_merge_aux_post.
      intro_merge_aux_post; eauto 2.
      (* Prove that we have a permutation. *)
      { split_seg (i2 + 1) src2.
        split_seg (k + 1) dst'.
        rewrite <- Hpost3. rewrite <- Hpost5.
        simplify_list_permutation_goal.
        rewrite Permutation_app_comm.
        simplify_list_permutation_goal. recognize. eauto. }
      (* Prove that the destination segment is sorted. *)
      { split_seg (k + 1) dst'.
        rewrite <- Hpost5.
        eapply Sorted_app; eauto with lia.
        rewrite <- Hpost3.
        (* {[x2]} ≼ seg i1 j1 src1 ++ seg (i2 + 1) j2 src2 *)
        rewrite pairwise_app_right_iff; split.
        + apply boundary_test; eauto 2 with lia.
          intros _ _. list. recognize. eauto.
        + apply boundary_test; eauto 2 with lia.
          - eapply sorted_seg_variance; eauto 2 with lia.
          - intros _ _. list. subst x2.
            eapply exploit_sorted_seg; eauto with lia.
      }
    }
    (* Subcase [i2 + 1 = j2]. *)
    { assert (j2 = i2 + 1) by lia. subst j2.
      wp_blit.
      intro_merge_aux_post; eauto 2; nat in *; list;
      (* UGLY [list] misses this rewriting step: *)
      try (erewrite (seg_none' _ _ dst) by lia; list);
      eauto 2 with lia.
      + simplify_list_equality_goal. reflexivity.
      + eapply Permutation_app_comm.
      + recognize.
        eapply sorted_app_boundary; eauto 2 with lia.
        intros _ _. list. recognize. eauto.
    }
  }
  (* Case [x1 ≤ x2]. *)
  { wp_set.
    wp_if.
    (* Subcase [i1 + 1 < j1]. *)
    { wp_get x'1.
      (* We are now looking at the recursive call. *)
      eapply wp_conseq.
      { eapply (IH (_i1 + 1, _i2)%uint63); tc3; list; tc. }
      clear dependent _dst. intros _dst Hpost.
      elim_merge_aux_post.
      intro_merge_aux_post; eauto 2.
      (* Prove that we have a permutation. *)
      { split_seg (i1 + 1) src1.
        split_seg (k + 1) dst'.
        rewrite <- Hpost3. rewrite <- Hpost5.
        simplify_list_permutation_goal. recognize. eauto. }
      (* Prove that the destination segment is sorted. *)
      { split_seg (k + 1) dst'.
        rewrite <- Hpost5.
        eapply Sorted_app; eauto with lia.
        rewrite <- Hpost3.
        (* {[x1]} ≼ seg (i1 + 1) j1 src1 ++ seg i2 j2 src2 *)
        rewrite pairwise_app_right_iff; split.
        + apply boundary_test; eauto 2 with lia.
          - eapply sorted_seg_variance; eauto 2 with lia.
          - intros _ _. list. subst x1.
            eapply exploit_sorted_seg; eauto with lia.
        + apply boundary_test; eauto 2 with lia.
          (* The fact that [x1] precedes [x2] is used here. *)
          intros _ _. list. recognize. eauto with lia.
      }
    }
    (* Subcase [i1 + 1 = j1]. *)
    { assert (j1 = i1 + 1) by lia. subst j1.
      wp_blit.
      intro_merge_aux_post; eauto 2; nat in *; list;
      (* UGLY [list] misses this rewriting step: *)
      try (erewrite (seg_none' _ _ dst) by lia; list);
      eauto 2 with lia.
      + simplify_list_equality_goal. reflexivity.
      + recognize.
        eapply sorted_app_boundary; eauto 2 with lia.
        (* The fact that [x1] precedes [x2] is used here. *)
        intros _ _. list. recognize. eauto with lia.
    }
  }
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
  match compare x1 x2 with
  | Lt | Eq =>
      do _dst ← set _dst _k x1 ;
      let _i1 := _i1 + 1 in
      let _k := _k + 1 in
      IF (_i1 <? _j1) THEN
        do x1 ← get _dst _i1 ;
        merge_aux_1 _i1 x1 _i2 x2 _dst _k
      ELSE
        blit _src2 _i2 _dst _k (_j2 - _i2)
  | Gt =>
      do _dst ← set _dst _k x2 ;
      let _i2 := _i2 + 1 in
      let _k := _k + 1 in
      IF (_i2 <? _j2) THEN
        do x2 ← get _src2 _i2 ;
        merge_aux_1 _i1 x1 _i2 x2 _dst _k
      ELSE
        (* There is nothing to do in this case. *)
        _dst
  end.

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
  wp_compare.
  (* Case [x2 < x1]. *)
  { wp_set.
    wp_if.
    (* Subcase [i2 + 1 < j2]. *)
    { wp_get x'2.
      (* We are now looking at the recursive call. *)
      eapply wp_conseq.
      { eapply (IH (_i1, _i2 + 1)%uint63); tc3; list; tc. }
      clear dependent _src1. intros _src1 Hpost.
      elim_merge_aux_post.
      intro_merge_aux_post; eauto 2.
      (* Prove that we have a permutation. *)
      { split_seg (i2 + 1) src2.
        split_seg (k + 1) dst'.
        rewrite <- Hpost3. rewrite <- Hpost5.
        simplify_list_permutation_goal.
        rewrite Permutation_app_comm.
        simplify_list_permutation_goal. recognize. eauto. }
      (* Prove that the destination segment is sorted. *)
      { split_seg (k + 1) dst'.
        rewrite <- Hpost5.
        eapply Sorted_app; eauto with lia.
        rewrite <- Hpost3.
        (* {[x2]} ≼ seg i1 j1 src1 ++ seg (i2 + 1) j2 src2 *)
        rewrite pairwise_app_right_iff; split.
        + apply boundary_test; eauto 2 with lia.
          intros _ _. list. recognize. eauto.
        + apply boundary_test; eauto 2 with lia.
          - eapply sorted_seg_variance; eauto 2 with lia.
          - intros _ _. list. subst x2.
            eapply exploit_sorted_seg; eauto with lia.
      }
    }
    (* Subcase [i2 + 1 = j2]. *)
    { assert (j2 = i2 + 1) by lia. subst j2.
      (* i1 = k + 1 *) subst i1.
      wp_ret.
      intro_merge_aux_post; eauto 2; nat in *; list; eauto 2 with lia.
      + recognize. eapply Permutation_app_comm.
      + eapply sorted_app_boundary; eauto 2 with lia.
        intros _ _. list. recognize. eauto.
    }
  }
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
      elim_merge_aux_post.
      intro_merge_aux_post; eauto 2.
      (* Prove that we have a permutation. *)
      { split_seg (i1 + 1) src1.
        split_seg (k + 1) dst'.
        rewrite <- Hpost3. rewrite <- Hpost5.
        simplify_list_permutation_goal. recognize. eauto. }
      (* Prove that the destination segment is sorted. *)
      { split_seg (k + 1) dst'.
        rewrite <- Hpost5.
        eapply Sorted_app; eauto with lia.
        rewrite <- Hpost3.
        (* {[x1]} ≼ seg (i1 + 1) j1 src1 ++ seg i2 j2 src2 *)
        rewrite pairwise_app_right_iff; split.
        + apply boundary_test; eauto 2 with lia.
          - eapply sorted_seg_variance; eauto 2 with lia.
          - intros _ _. list. subst x1.
            eapply exploit_sorted_seg; eauto with lia.
        + apply boundary_test; eauto 2 with lia.
          (* The fact that [x1] precedes [x2] is used here. *)
          intros _ _. list. recognize. eauto with lia.
      }
    }
    (* Subcase [i1 + 1 = j1]. *)
    { assert (j1 = i1 + 1) by lia. subst j1.
      (* i1 = k + (j2 - i2) *) subst i1.
      wp_blit.
      intro_merge_aux_post; eauto 2; nat in *; list; eauto 2 with lia.
      + simplify_list_equality_goal. reflexivity.
      + simplify_list_permutation_goal.
        erewrite (seg_none' _ _ src1) by lia; list. (* UGLY *)
        reflexivity.
      + recognize.
        erewrite (seg_none' _ _ src1) by lia; list. (* UGLY *)
        eapply sorted_app_boundary; eauto 2 with lia.
        (* The fact that [x1] precedes [x2] is used here. *)
        intros _ _. list. recognize. eauto with lia.
    }
  }
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
  match compare x1 x2 with
  | Lt | Eq =>
      do _dst ← set _dst _k x1 ;
      let _i1 := _i1 + 1 in
      let _k := _k + 1 in
      IF (_i1 <? _j1) THEN
        do x1 ← get _src1 _i1 ;
        merge_aux_2 _i1 x1 _i2 x2 _dst _k
      ELSE
        (* There is nothing to do in this case. *)
        _dst
  | Gt =>
      do _dst ← set _dst _k x2 ;
      let _i2 := _i2 + 1 in
      let _k := _k + 1 in
      IF (_i2 <? _j2) THEN
        do x2 ← get _dst _i2 ;
        merge_aux_2 _i1 x1 _i2 x2 _dst _k
      ELSE
        blit _src1 _i1 _dst _k (_j1 - _i1)
  end.

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
  wp_compare.
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
      elim_merge_aux_post.
      intro_merge_aux_post; eauto 2.
      (* Prove that we have a permutation. *)
      { split_seg (i2 + 1) src2.
        split_seg (k + 1) dst'.
        rewrite <- Hpost3. rewrite <- Hpost5.
        simplify_list_permutation_goal.
        rewrite Permutation_app_comm.
        simplify_list_permutation_goal. recognize. eauto. }
      (* Prove that the destination segment is sorted. *)
      { split_seg (k + 1) dst'.
        rewrite <- Hpost5.
        eapply Sorted_app; eauto with lia.
        rewrite <- Hpost3.
        (* {[x2]} ≼ seg i1 j1 src1 ++ seg (i2 + 1) j2 src2 *)
        rewrite pairwise_app_right_iff; split.
        + apply boundary_test; eauto 2 with lia.
          intros _ _. list. recognize. eauto.
        + apply boundary_test; eauto 2 with lia.
          - eapply sorted_seg_variance; eauto 2 with lia.
          - intros _ _. list. subst x2.
            eapply exploit_sorted_seg; eauto with lia.
      }
    }
    (* Subcase [i2 + 1 = j2]. *)
    { assert (j2 = i2 + 1) by lia. subst j2.
      wp_blit.
      intro_merge_aux_post; eauto 2; nat in *; list;
      (* UGLY [list] misses this rewriting step: *)
      try (erewrite (seg_none' _ _ src2) by lia; list);
      eauto 2 with lia;
      rewrite <- Hi2.
      + simplify_list_equality_goal. reflexivity.
      + recognize.
        erewrite (seg_none' _ _ src2) by lia. list. (* UGLY *)
        eapply Permutation_app_comm.
      + recognize.
        erewrite (seg_none' _ _ src2) by lia. list. (* UGLY *)
        eapply sorted_app_boundary; eauto 2 with lia.
        intros _ _. list. recognize. eauto.
    }
  }
  (* Case [x1 ≤ x2]. *)
  { wp_set.
    wp_if.
    (* Subcase [i1 + 1 < j1]. *)
    { wp_get x'1.
      (* We are now looking at the recursive call. *)
      eapply wp_conseq.
      { eapply (IH (_i1 + 1, _i2)%uint63); tc3; list; tc3; tc. }
      clear dependent _src2. intros _src2 Hpost.
      elim_merge_aux_post.
      intro_merge_aux_post; eauto 2.
      (* Prove that we have a permutation. *)
      { split_seg (i1 + 1) src1.
        split_seg (k + 1) dst'.
        rewrite <- Hpost3. rewrite <- Hpost5.
        simplify_list_permutation_goal. recognize. eauto. }
      (* Prove that the destination segment is sorted. *)
      { split_seg (k + 1) dst'.
        rewrite <- Hpost5.
        eapply Sorted_app; eauto with lia.
        rewrite <- Hpost3.
        (* {[x1]} ≼ seg (i1 + 1) j1 src1 ++ seg i2 j2 src2 *)
        rewrite pairwise_app_right_iff; split.
        + apply boundary_test; eauto 2 with lia.
          - eapply sorted_seg_variance; eauto 2 with lia.
          - intros _ _. list. subst x1.
            eapply exploit_sorted_seg; eauto with lia.
        + apply boundary_test; eauto 2 with lia.
          (* The fact that [x1] precedes [x2] is used here. *)
          intros _ _. list. recognize. eauto with lia.
      }
    }
    (* Subcase [i1 + 1 = j1]. *)
    { assert (j1 = i1 + 1) by lia. subst j1.
      (* i2 = k + 1 *) subst i2.
      wp_ret.
      intro_merge_aux_post; eauto 2; nat in *; list; eauto 2 with lia.
      + recognize. reflexivity.
      + eapply sorted_app_boundary; eauto 2 with lia.
        (* The fact that [x1] precedes [x2] is used here. *)
        intros _ _. list. recognize. eauto with lia.
    }
  }
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
  match compare x1 x2 with
  | Lt | Eq =>
      do _dst ← set _dst _k x1 ;
      let _i1 := _i1 + 1 in
      let _k := _k + 1 in
      IF (_i1 <? _j1) THEN
        do x1 ← get _dst _i1 ;
        merge_aux_12 _i1 x1 _i2 x2 _dst _k
      ELSE
        _dst
  | Gt =>
      do _dst ← set _dst _k x2 ;
      let _i2 := _i2 + 1 in
      let _k := _k + 1 in
      IF (_i2 <? _j2) THEN
        do x2 ← get _dst _i2 ;
        merge_aux_12 _i1 x1 _i2 x2 _dst _k
      ELSE
        blit' _dst _i1 _k (_j1 - _i1)
  end.

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
  wp_compare.
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
      elim_merge_aux_post.
      intro_merge_aux_post; eauto 2.
      (* Prove that we have a permutation. *)
      { rewrite (split_seg (i2 + 1) dst i2 j2) by lia.
        split_seg (k + 1) dst'.
        rewrite <- Hpost3. rewrite <- Hpost5.
        simplify_list_permutation_goal.
        rewrite Permutation_app_comm.
        simplify_list_permutation_goal. recognize. eauto. }
      (* Prove that the destination segment is sorted. *)
      { split_seg (k + 1) dst'.
        rewrite <- Hpost5.
        eapply Sorted_app; eauto with lia.
        rewrite <- Hpost3.
        (* {[x2]} ≼ seg i1 j1 src1 ++ seg (i2 + 1) j2 src2 *)
        rewrite pairwise_app_right_iff; split.
        + apply boundary_test; eauto 2 with lia.
          intros _ _. list. recognize. eauto.
        + apply boundary_test; eauto 2 with lia.
          - eapply sorted_seg_variance; eauto 2 with lia.
          - intros _ _. list. subst x2.
            eapply exploit_sorted_seg; eauto with lia.
      }
    }
    (* Subcase [i2 + 1 = j2]. *)
    { assert (j2 = i2 + 1) by lia. subst j2.
      wp_blit.
      intro_merge_aux_post; eauto 2; nat in *; list;
      (* UGLY [list] misses this rewriting step: *)
      try (erewrite (seg_none' _ _ dst) by lia; list);
      eauto 2 with lia;
      rewrite <- Hi2.
      + simplify_list_equality_goal. reflexivity.
      + recognize.
        rewrite* @seg_none' by lia. list. (* UGLY *)
        eapply Permutation_app_comm.
      + recognize.
        rewrite* sub_diag' by lia. nat. (* UGLY *)
        rewrite seg_none. list. (* UGLY *)
        eapply sorted_app_boundary; eauto 2 with lia.
        intros _ _. list. recognize. eauto.
    }
  }
  (* Case [x1 ≤ x2]. *)
  { wp_set.
    wp_if.
    (* Subcase [i1 + 1 < j1]. *)
    { wp_get x'1.
      (* We are now looking at the recursive call. *)
      eapply wp_conseq.
      { eapply (IH (_i1 + 1, _i2)%uint63); tc3; list; tc3; tc. }
      clear dependent _dst. intros _dst Hpost.
      elim_merge_aux_post.
      intro_merge_aux_post; eauto 2.
      (* Prove that we have a permutation. *)
      { split_seg (i1 + 1) dst.
        split_seg (k + 1) dst'.
        rewrite <- Hpost3. rewrite <- Hpost5.
        simplify_list_permutation_goal. recognize. eauto. }
      (* Prove that the destination segment is sorted. *)
      { split_seg (k + 1) dst'.
        rewrite <- Hpost5.
        eapply Sorted_app; eauto with lia.
        rewrite <- Hpost3.
        (* {[x1]} ≼ seg (i1 + 1) j1 dst ++ seg i2 j2 dst *)
        rewrite pairwise_app_right_iff; split.
        + apply boundary_test; eauto 2 with lia.
          - eapply (sorted_seg_variance i1 j1); eauto 2 with lia.
          - intros _ _. list. subst x1.
            eapply (exploit_sorted_seg i1 j1); eauto 2 with lia.
        + apply boundary_test; eauto 2 with lia.
          (* The fact that [x1] precedes [x2] is used here. *)
          intros _ _. list. recognize. eauto with lia.
      }
    }
    (* Subcase [i1 + 1 = j1]. *)
    { assert (j1 = i1 + 1) by lia. subst j1.
      (* i2 = k + 1 *) subst i2.
      wp_ret.
      intro_merge_aux_post; eauto 2; nat in *; list; eauto 2 with lia.
      + recognize. reflexivity.
      + eapply sorted_app_boundary; eauto 2 with lia.
        (* The fact that [x1] precedes [x2] is used here. *)
        intros _ _. list. recognize. eauto with lia.
    }
  }
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
  match compare x1 x2 with
  | Lt | Eq =>
      (* If they are suitably ordered then two blits suffice. *)
      let _n1 := _j1 - _i1 in
      do _dst ← blit _src1 _i1 _dst _k _n1 ;
      let _n2 := _j2 - _i2 in
      do _dst ← blit _src2 _i2 _dst (_k + _n1) _n2 ;
      _dst
  | Gt =>
      do x1 ← get _src1 _i1 ;
      merge_aux _src1 _src2 _j1 _j2 _i1 x1 _i2 x2 _dst _k
  end.

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
  wp_compare.
  (* Case [x2 < x1]. *)
  { clear dependent x1.
    wp_get x1.
    wp_op wp_merge_aux _dst'.
    assumption. }
  (* Case [x1 ≤ x2]. *)
  {
    (* This remark is the key reason with this case works. *)
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
    intro_merge_aux_post; eauto 2; list.
    + lia.
    + reflexivity.
    + simplify_list_equality_goal. reflexivity.
    + rewrite* @seg_none' by lia. list. reckon i2. reckon j2.
      reflexivity.
    + rewrite* @seg_none' by lia. list. reckon i2. reckon j2.
      eapply Sorted_app; eauto.
  }
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
  match compare x1 x2 with
  | Lt | Eq =>
      (* If they are suitably ordered then one blit suffices. *)
      let _n1 := _j1 - _i1 in
      do _dst ← blit _src1 _i1 _dst _k _n1 ;
      _dst
  | Gt =>
      do x1 ← get _src1 _i1 ;
      merge_aux_2 _src1 _j1 _j2 _i1 x1 _i2 x2 _dst _k
  end.

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
  wp_compare.
  (* Case [x2 < x1]. *)
  { clear dependent x1.
    wp_get x1.
    wp_op wp_merge_aux_2 _dst'.
    assumption. }
  (* Case [x1 ≤ x2]. *)
  {
    (* This remark is the key reason with this case works. *)
    assert (seg i1 j1 src1 ≼ seg i2 j2 src2).
    { apply boundary_test; eauto 2. intros _ _. list.
      recognize. eauto with lia. }
    wp_blit.
    wp_ret.
    intro_merge_aux_post; eauto 2; list.
    + lia.
    + reflexivity.
    + simplify_list_equality_goal. reflexivity.
    + reckon i2. reckon j2. reflexivity.
    + reckon i2. reckon j2. eapply Sorted_app; eauto.
  }
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
  match compare x1 x2 with
  | Lt | Eq =>
      let _n1 := _j1 - _i1 in
      do _dst ← blit' _dst _i1 _k _n1 ;
      _dst
  | Gt =>
      do x1 ← get _dst _i1 ;
      merge_aux_12 _j1 _j2 _i1 x1 _i2 x2 _dst _k
  end.

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
  wp_compare.
  (* Case [x2 < x1]. *)
  { clear dependent x1.
    wp_get x1.
    wp_op wp_merge_aux_12 _dst'.
    assumption. }
  (* Case [x1 ≤ x2]. *)
  {
    (* This remark is the key reason with this case works. *)
    assert (seg i1 j1 dst ≼ seg i2 j2 dst).
    { apply boundary_test; eauto 2. intros _ _. list.
      recognize. eauto with lia. }
    wp_blit.
    wp_ret.
    intro_merge_aux_post; eauto 2; list.
    + lia.
    + reflexivity.
    + simplify_list_equality_goal. reflexivity.
    + reckon i2. reckon j2. reflexivity.
    + reckon i2. reckon j2. eapply Sorted_app; eauto.
  }
Qed.

End Sorting.
