From stdpp Require Import numbers list.
From Stdlib Require Import Uint63.
From Stdlib Require Import Array.PArray.
From Stdlib Require Import Sorting.Permutation.
From Corelib Require Import Classes.RelationClasses.
From marble Require Import tactics list_extra bool iteration int wp wp_tactics array.
Implicit Types _i _j _k : int.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

Open Scope nat_scope.

(* Documentation:
   https://rocq-prover.org/doc/V9.1.0/corelib/Corelib.Classes.RelationClasses.html
 *)

(* TODO *)
Lemma list_insert_id'' `{Inhabited A} (xs : list A) (i : nat) (x : A) :
  valid i xs →
  xs !!! i = x →
  <[i:=x]>xs = xs.
Proof.
  rewrite <- lookup_lt_is_Some.
  intros Hvalid Hlookup.
  apply list_lookup_lookup_total in Hvalid.
  rewrite list_insert_id by congruence.
  eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Three-way comparisons. *)

(* This type exists in the standard library:
Inductive comparison := Eq | Lt | Gt.
 *)

(* A [compare] function performs a three-way comparison. *)

(* [Compare A] means that the type [A] has a [compare] function. *)

Class Compare (A : Type) :=
  { compare : A → A → comparison }.

(* A preorder is a reflexive and transitive relation. *)

(* Its kernel is an equivalence relation. *)

Section Kernel.

Context {A} (R : A → A → Prop).

Definition kernel x y :=
  R x y ∧ R y x.

Context `{@PreOrder A R}.

Global Instance : Reflexive kernel.
Proof. unfold kernel. repeat intro. split; reflexivity. Qed.

Global Instance : Symmetric kernel.
Proof. unfold kernel. repeat intro. tauto. Qed.

Global Instance : Transitive kernel.
Proof.
  unfold kernel. intros x y z (?&?) (?&?).
  split; transitivity y; eauto.
Qed.

End Kernel.

(* [Comparable A] means that the [compare] function at type [A]
   is correct with respect to the default preorder on this type. *)

Declare Scope element_scope.
Delimit Scope element_scope with element.

Section Comparable.

Open Scope element_scope.

Context (A : Type).

Context `{PreOrder A R}.

Infix "≤" := R
  (at level 70, no associativity) : element_scope.
Infix "<" := (strict R)
  (at level 70, no associativity) : element_scope.
Notation "y ≥ x" := (x ≤ y)%element
  (only parsing, at level 70, no associativity) : element_scope.
Notation "y > x" := (x < y)%element
  (only parsing, at level 70, no associativity) : element_scope.
Infix "≡" := (kernel R)
  (at level 70, no associativity) : element_scope.

Context `{Compare A}.

Class Comparable := {
  compare_spec :
    ∀ x y : A, CompareSpec (x ≡ y) (x < y) (x > y) (compare x y)
}.

End Comparable.

(* TODO find a way of reasoning about 2-way comparisons *)

(* -------------------------------------------------------------------------- *)

(* Insertion sort: [isortto]. *)


Section Sort.

Context `{Inhabited A} `{Comparable A}.

Implicit Types _src _dst : array A.
Implicit Types src dst : list A.
Implicit Types _srcofs _dstofs _n : int.
Implicit Types srcofs dstofs n : nat.

Local Definition empty_slot _dstofs (out : outcome int) : int :=
  match out with
  | Break _j => _j + 1
  | Continue => _dstofs
  end.

(* [isortto src _srcofs dst _dstofs _n] sorts the array segment described
   by [src], [_srcofs], [_n]. The resulting data is written into the array
   segment described by [dst], [_dstofs], [_n]. The source and destination
   arrays must be distinct. This is an insertion sort. *)

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
    set dst (empty_slot _dstofs out) xi.

Infix "≤" := R
  (at level 70, no associativity) : element_scope.
Infix "<" := (strict R)
  (at level 70, no associativity) : element_scope.
Notation "y ≥ x" := (x ≤ y)%element
  (only parsing, at level 70, no associativity) : element_scope.
Notation "y > x" := (x < y)%element
  (only parsing, at level 70, no associativity) : element_scope.
Infix "≡" := (kernel R)
  (at level 70, no associativity) : element_scope.

Open Scope element_scope.

Infix "π" := (@Permutation A) (* TODO find better symbol *)
  (at level 70, no associativity).

(* This is the invariant of the main loop. *)

(* Here,
   [src] is the content of the source array;
   [dst] is the initial content of the destination array;
   [dst']  is the final content of the destination array.
 *)

Local Definition isortto_inv src srcofs dst dstofs := λ i _dst,
  ∃ dst',
  isArray _dst dst' ∧
  len dst' = len dst ∧
  (* Outside of the destination segment,
     the destination array is unmodified. *)
  initial_seg dstofs dst = initial_seg dstofs dst' ∧
  final_seg (dstofs + i) dst = final_seg (dstofs + i) dst' ∧
  (* Inside the destination segment,
     we find a permutation of the data in the source segment. *)
  seg srcofs (srcofs + i) src π seg dstofs (dstofs + i) dst'
.

Local Ltac intro_isortto_inv :=
  unfold isortto_inv; pack; list; tc3; list; tc3.

Local Ltac elim_isortto_inv dst' :=
  match goal with h: isortto_inv _ _ _ _ _ _ |- _ =>
    destruct h as (dst' & h); unpack in h
  end.

Local Definition transported_pending_last_write src srcofs i dst dstofs j :=
  let xi := src !!! (srcofs + i) in
  seg srcofs (srcofs + (i + 1)) src
    π
  seg dstofs j dst ++ {[xi]} ++ seg (j + 1) (dstofs + (i + 1)) dst.

Local Definition inner_inv src srcofs dst dstofs i := λ j _dst out,
  ∃ dst',
  isArray _dst dst' ∧
  len dst' = len dst ∧
  (* Outside of the destination segment,
     extended by one slot up to index [i+1],
     the destination array is unmodified. *)
  initial_seg dstofs dst = initial_seg dstofs dst' ∧
  final_seg (dstofs + (i + 1)) dst = final_seg (dstofs + (i + 1)) dst' ∧
  (* Inside this extended destination segment,
     provided the element at offset [j] is replaced with [xi],
     we find a permutation of the data
     in the corresponding extended source segment. *)
  match out with
  | Continue =>
      transported_pending_last_write src srcofs i dst' dstofs j
  | Break _j =>
      isInt _j j ∧ dstofs ≤ j < dstofs + i ∧
      dst' !!! j ≤ src !!! (srcofs + i) ∧
      transported_pending_last_write src srcofs i dst' dstofs (j + 1)
  end.

Local Ltac intro_inner_inv :=
  unfold inner_inv; pack; list; tc3; list; tc3.

Local Ltac elim_inner_inv dst' :=
  match goal with h: inner_inv _ _ _ _ _ _ _ _ |- _ =>
    destruct h as (dst' & h); cbv zeta in h; unpack in h
  end.

Lemma equiv_le x y :  x ≡ y → x ≤ y.
Proof. unfold kernel. tauto. Qed.
Lemma lt_le x y :  x < y → x ≤ y.
Proof. unfold strict. tauto. Qed.
Lemma equiv_ge x y :  x ≡ y → x ≥ y.
Proof. unfold kernel. tauto. Qed.
Lemma gt_ge x y :  x > y → x ≥ y.
Proof. eauto using lt_le. Qed.

Lemma wp_compare_Gt_Le {B} (x y : A) (e1 e2 : B) (Q : B → Prop) :
  (x > y → wp e1 Q) →
  (x ≤ y → wp e2 Q) →
  wp (match compare x y with Gt => e1 | _ => e2 end) Q.
Proof.
  intros. destruct (compare_spec _ x y).
  + eauto using equiv_le.
  + eauto using lt_le.
  + eauto.
Qed.

Ltac wp_compare :=
  first [
    simple eapply wp_compare_Gt_Le
  ];
  intro.

(* TODO *)
Lemma a_bp1_m1 a b : a + (b + 1) - 1 = a + b.
Proof. lia. Qed.
Hint Rewrite a_bp1_m1 : list nat.

Ltac simplify_list_permutation_goal :=
  (* TODO cannot use [list] because it joins segments *)
  autorewrite with nat;
  repeat rewrite app_assoc;
  repeat eapply Permutation_app_tail;
  repeat rewrite <- app_assoc;
  repeat eapply Permutation_app_head.

Ltac split_seg_singleton_r xs :=
  erewrite (split_seg_singleton_r xs) by lia;
  autorewrite with nat.

Ltac recognize_named_lookups :=
  repeat match goal with h: ?x = ?xs !!! ?i |- context[?xs !!! ?i] =>
    rewrite <- !h
  end.

Ltac use_known_permutations :=
  repeat match goal with h: ?xs π ?ys |- context[?xs] =>
    rewrite h
  end.

Lemma seg_equality_implication i1 j1 i2 j2 i'1 j'1 i'2 j'2 (xs1 xs2 : list A) :
  seg i1 j1 xs1 = seg i2 j2 xs2 →
  valid_seg i1 j1 xs1 →
  valid_seg i2 j2 xs2 →
  i1 ≤ i'1 ≤ j'1 ≤ j1 →
  i2 ≤ i'2 ≤ j'2 ≤ j2 →
  i'2 - i2 = i'1 - i1 →
  j'2 - i2 = j'1 - i1 →
  seg i'1 j'1 xs1 = seg i'2 j'2 xs2.
Proof.
  intros.
  replace (seg i'1 j'1 xs1) with
          (seg (i'1 - i1) (j'1 - i1) (seg i1 j1 xs1))
  by (list; eauto).
  replace (seg i'2 j'2 xs2) with
          (seg (i'2 - i2) (j'2 - i2) (seg i2 j2 xs2))
  by (list; eauto).
  congruence.
Qed.

Local Hint Resolve seg_equality_implication : seg.

Lemma wp_issortto _src src _srcofs srcofs _dst dst _dstofs dstofs _n n :
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
      { intro_inner_inv.
        { eauto with seg lia. }
        { unfold transported_pending_last_write.
          split_seg_singleton_r src. use_known_permutations. list. eauto. }
      }
      (* The body of the inner loop. *)
      clear dependent _dst. wp_loop_intros _j j _dst.
      elim_inner_inv dst''.
      (* [dst''s] is the content of the destination array upon entry into
         the body of the inner loop. *)
      wp_get xj.
      wp_compare.
      (* Case [xi < xj]. *)
      { wp_set. wp_continue. intro_inner_inv.
        (* Justify the content of the destination segment. *)
        { unfold transported_pending_last_write in *. list.
          use_known_permutations.
          erewrite (seg_is_singleton src (srcofs + i)) by lia.
          split_seg_singleton_r dst''.
          simplify_list_permutation_goal. recognize_named_lookups.
          (* Argue that swapping [xi] and [xj] is permitted. *)
          eapply Permutation_app_comm. }
      }
      (* Case [xj ≤ xi]. *)
      { wp_break. intro_inner_inv.
        { subst. assumption. }
      }
    }
    (* Conclusion of the inner loop. *)
    { clear dependent _dst. intros [ _dst out ].
      intros (j&Hj). list in Hj. unpack in Hj.
      (* Perform a case analysis on [out], so as to separately analyze
         the case where the loop has been stopped early and the case
         where it has finished normally. *)
      destruct out as [ _j |]; simpl empty_slot; elim_inner_inv dst''.
      (* Case: we have broken out. *)
      { wp_set.
        intro_isortto_inv.
        (* Justify the content of the destination segment. *)
        { unfold transported_pending_last_write in *.
          use_known_permutations.
          recognize_named_lookups.
          rewrite insert_seg by (list; lia); autorewrite with nat.
          eauto. }
      }
      (* Case: the loop has finished normally. *)
      { assert (j = dstofs) by tauto. subst j.
        wp_set.
        intro_isortto_inv.
        (* Justify the content of the destination segment. *)
        { unfold transported_pending_last_write in *.
          use_known_permutations.
          recognize_named_lookups.
          list. eauto. }
      }
    }
  }
Qed.

End Sort.
