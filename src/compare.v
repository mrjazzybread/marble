From Stdlib Require Import ZArith Lia.
From Stdlib Require Import Uint63 ZifyUint63.
  (* [ZifyUint63] magically makes [lia] more powerful *)
From stdpp Require Import base numbers.
From marble Require Import tactics orders bool int.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

(* -------------------------------------------------------------------------- *)

(* Two-way comparison functions. *)

(* A [leb] function performs a two-way comparison. *)

(* [leb] stands for "Less than or Equal, Boolean". *)

(* [Leb A] means that the type [A] has a [leb] function. *)

Class Leb (A : Type) :=
  { leb : A → A → bool }.

(* Three-way comparison functions. *)

(* This type exists in the standard library:
Inductive comparison := Eq | Lt | Gt.
 *)

(* A [compare] function performs a three-way comparison. *)

(* [Compare A] means that the type [A] has a [compare] function. *)

Class Compare (A : Type) :=
  { compare : A → A → comparison }.

(* -------------------------------------------------------------------------- *)

(* Specifications for comparison functions. *)

Section Specs.

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

(* [LebSpec A] means that the [leb] function at type [A] is correct
   with respect to the default preorder on this type. *)

Section LebSpec.

Context `{Leb A}.

Class LebSpec := {
  leb_spec :
    ∀ x y : A, isBool (leb x y) (x ≤ y) (x > y)
}.

(* We make [leb_spec] an instance, so [wp_if] works out of the box. *)

Global Existing Instance leb_spec.

(* This is an example:

Local Lemma example `{LebSpec} {B} (x y : A) (e1 e2 : B) (Q : B → Prop) :
  (x ≤ y → wp e1 Q) →
  (x > y → wp e2 Q) →
  wp (if leb x y then e1 else e2) Q.
Proof.
  intros. wp_if.
  + eauto.
  + eauto.
Qed.
 *)

End LebSpec.

(* [Comparable A] means that the [compare] function at type [A]
   is correct with respect to the default preorder on this type. *)

(* The assertion [CompareSpec] is defined in the standard library. *)

Section Comparable.

Context `{Compare A}.

Class Comparable := {
  compare_spec :
    ∀ x y : A, CompareSpec (x ≡ y) (x < y) (x > y) (compare x y)
}.

End Comparable.

End Specs.

(* -------------------------------------------------------------------------- *)

(* Instances. *)

Open Scope Z_scope.

(* A two-way comparison on binary integers (Z). *)

Instance Leb_Z : Leb Z := { leb := Z.leb }.

Lemma strict_Zle x y : strict Z.le x y ↔ (x < y).
Proof. unfold strict. lia. Qed.

Instance LebSpec_Z : LebSpec Z Z.le.
Proof.
  constructor; intros.
  eapply BoolSpec_isBool.
  rewrite strict_Zle.
  eapply Z.leb_spec.
Qed.

(* A two-way comparison on machine integers (int). *)

Instance Leb_int : Leb int := { leb := Uint63.leb }.

Instance LebSpec_int : LebSpec int (λ _i _j : int, to_Z _i ≤ to_Z _j).
Proof.
  constructor; intros _i _j. simpl. unfold strict.
  (* I am suffering more than I should. Probably there is a simpler way. *)
  assert (H:
    isBool1 (_i ≤? _j)%uint63
            (proj (to_nat _i) ≤ proj (to_nat _j))%nat
  ).
  { eapply isBool_leb_proj; eapply introIsInt. }
  destruct (_i ≤? _j)%uint63; simpl in *;
    rewrite <- !to_nat_of_nat, !of_nat_to_nat in *; lia.
Qed.
