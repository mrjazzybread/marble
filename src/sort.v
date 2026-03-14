From stdpp Require Import numbers list.
From Stdlib Require Import Uint63.
From Stdlib Require Import Array.PArray.
From Corelib Require Import Classes.RelationClasses.
From marble Require Import tactics list_extra bool iteration int wp wp_tactics array.
Implicit Types _i _j _k _n : int.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

Open Scope nat_scope.

(* Documentation:
   https://rocq-prover.org/doc/V9.1.0/corelib/Corelib.Classes.RelationClasses.html
 *)

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

Section Comparable.

Open Scope element_scope.

Context (A : Type).

Context `{PreOrder A R}.

Infix "≤" := R
  (at level 70, no associativity) : element_scope.
Infix "<" := (strict R)
  (at level 70, no associativity) : element_scope.
Notation "y ≥ x" := (x ≤ y)
  (only parsing, at level 70, no associativity) : element_scope.
Notation "y > x" := (x < y)
  (only parsing, at level 70, no associativity) : element_scope.
Infix "≡" := (kernel R)
  (at level 70, no associativity) : element_scope.

Context `{Compare A}.

Class Comparable := {
  compare_spec :
    ∀ x y : A, CompareSpec (x ≡ y) (x < y) (x > y) (compare x y)
}.

End Comparable.

(* -------------------------------------------------------------------------- *)

(* Insertion sort: [isortto]. *)

Section Sort.

Context `{Inhabited A} `{Comparable A}.

(* [isortto src srcofs dst dstofs n] sorts the array segment described
   by [src], [srcofs], [n]. The resulting data is written into the array
   segment described by [dst], [dstofs], [n]. The source and destination
   arrays must be distinct. This is an insertion sort. *)

Definition isortto src srcofs dst dstofs n :=
  (* Let [i] scan the source segment upwards. *)
  int.iter_up 0 n dst @@ λ _i dst ,
    (* Extract [x] at offset [i] in the source segment. *)
    do x ← get src (srcofs + _i)%uint63 ;
    do (dst, out) ← (
      (* Let [j] scan the sorted part of the destination segment, downwards. *)
      int.xiter_down (dstofs + _i)%uint63 dstofs dst @@
      λ _ _j dst continue break ,
        (* Read an element [xj] at offset [j] in the destination segment.
           If [xj ≥ x] holds then move [xj] upwards by one position and
           continue. Otherwise write [x] into position [j] and stop. *)
        do xj ← get dst _j ;
        match compare xj x with
        | Gt      => do dst ← set dst (_j + 1) xj; continue dst
        | Lt | Eq => do dst ← set dst (_j + 1)  x; break dst ()
        end
    );
    dst.

End Sort.
