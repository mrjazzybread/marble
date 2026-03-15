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

Implicit Types src dst : array A.
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

Definition isortto src _srcofs dst _dstofs _n :=
  (* Let [i] scan the source segment upwards. *)
  int.iter_up 0 _n dst @@ λ _i dst ,
    (* Extract [xi] at offset [i] in the source segment. *)
    do xi ← get src (_srcofs + _i)%uint63 ;
    do (dst, out) ← (
      (* Let [j] scan the sorted part of the destination segment, downwards. *)
      int.xiter_down (_dstofs + _i)%uint63 _dstofs dst @@
      λ _ _j dst continue break ,
        (* Read an element [xj] at offset [j] in the destination segment.
           If [xj ≥ xi] holds then move [xj] upwards by one position and
           continue. Otherwise stop. *)
        do xj ← get dst _j ;
        match compare xj xi with
        | Gt      => do dst ← set dst (_j + 1) xj; continue dst
        | Lt | Eq => break dst _j
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

Implicit Types xs ys zs : list A.

Infix "π" := (@Permutation A) (* TODO find better symbol *)
  (at level 70, no associativity).

Notation isortto_inv xs srcofs ys dstofs i dst := (
  ∃ zs,
  isArray dst zs ∧
  len zs = len ys ∧
  initial_seg dstofs ys = initial_seg dstofs zs ∧
  final_seg (dstofs + i) ys = final_seg (dstofs + i) zs ∧
  seg srcofs (srcofs + i) xs π seg dstofs (dstofs + i) zs
).

Notation isortto_inner_inv xs srcofs ys dstofs i j dst out := (
  ∃ zs,
  isArray dst zs ∧
  len zs = len ys ∧
  initial_seg dstofs ys = initial_seg dstofs zs ∧
  final_seg (dstofs + (i + 1)) ys = final_seg (dstofs + (i + 1)) zs ∧
  seg srcofs (srcofs + (i + 1)) xs π
    <[j - dstofs := xs !!! (srcofs + i)]>(seg dstofs (dstofs + (i + 1)) zs)
  ∧
  match out with
  | Continue => True
  | Break _j =>
      isInt _j j ∧ dstofs ≤ j < dstofs + i ∧
      zs !!! j ≤ xs !!! (srcofs + i)
  end
).

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

Lemma wp_issortto src xs _srcofs srcofs dst ys _dstofs dstofs _n n :
  isArray src xs →
  isInt _srcofs srcofs →
  isArray dst ys →
  isInt _dstofs dstofs →
  isInt _n n →
  valid_seg srcofs (srcofs + n) xs →
  valid_seg dstofs (dstofs + n) ys →
  wp (isortto src _srcofs dst _dstofs _n) (λ dst,
    isortto_inv xs srcofs ys dstofs n dst
  ).
Proof.
  intros. unfold isortto.
  wp_iter_up (λ i dst, isortto_inv xs srcofs ys dstofs i dst).
  (* The loop body. *)
  { (* TODO avoid manual renamings. *)
    (* TODO [wp_loop] should probably NOT use [pack] *)
    subst j0 j1. clear dependent dst.
    rename o into _i, j into i, s into dst.
    wp_get xi.
    eapply wp_bind.
    { int.wp_xiter_down (λ j dst out,
        isortto_inner_inv xs srcofs ys dstofs i j dst out
      ).
      { admit. }
      { replace (dstofs + (i + 1) - 1) with (dstofs + i) by lia. (* TODO rewrite hint *)
        (* TODO set up rewriting modulo π *)
        admit. }
      (* TODO avoid manual renamings. *)
      subst j0 j1. clear dependent dst.
      rename o into _j, s into dst.
      wp_get xj.
      wp_compare.
      (* Case [xi < xj]. *)
      { wp_set. wp_continue; pack; list; tc3; list; tc3.
        + admit.
      }
      (* Case [xj ≤ xi]. *)
      { wp_break; pack; list; tc3; list; tc3.
        + admit.
        + subst. assumption.
      }
    }
    (* Conclusion of the inner loop. *)
    { clear dependent dst. intros [ dst out ].
      intros (j&?). unpack. list in *.
      assert (dstofs ≤ to_nat (empty_slot _dstofs out) ≤ dstofs + i). (* TODO *)
      { destruct out; simpl empty_slot.
        - replace (to_nat (i0 + 1)) with (j + 1) by admit.
          lia.
        - rewrite H5. int.
          replace (proj dstofs) with dstofs.
          2: symmetry.
          2: rewrite <- representable_iff_proj.
          2: tc.
          lia. }
      wp_set.
      { eapply introIsInt. }
      { eauto with lia. }
      pack; list; tc3; list; tc3.
      + admit.
    }
  }
  (* Conclusion of the outer loop. *)
  { eauto 6. }
Admitted.

End Sort.
