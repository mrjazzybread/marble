From stdpp Require Import numbers list.
Local Notation len := List.length.
From Stdlib Require Import Uint63.
From Stdlib Require Import Array.PArray.
From array Require Import tactics list_extra bool int wp array.
Implicit Types _i _j _k _n : int.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

Open Scope nat_scope.

(* -------------------------------------------------------------------------- *)

(* A vector is a pair of a logical length [_n] and an array [a]. *)

Definition vectorInv `{Inhabited A} _n a (xs : list A) :=
  ∃ unoccupied,
  isInt _n (len xs) ∧
  isArray a (xs ++ unoccupied).

Definition vector (A : Type) :=
  (int * array A)%type.

Definition isVector `{Inhabited A} (v : vector A) (xs : list A) :=
  let (_n, a) := v in
  vectorInv _n a xs.

(* These tactics and lemmas help work with [isVector]. *)

Local Ltac introIsVector :=
  unfold isVector; unfold vectorInv; eexists; split.

Local Ltac introIsVectorWithWitness u :=
  unfold isVector; unfold vectorInv; exists u; split.

Local Ltac destructIsVector _n a :=
  match goal with h: isVector ?v _ |- _ =>
    destruct v as [ _n a ];
    unfold isVector in h;
    let u := fresh "unoccupied" in
    destruct h as (u&?&?)
  end.

(* -------------------------------------------------------------------------- *)

Section Operations.
Context `{Inhabited A}.
Implicit Types v : vector A.
Implicit Types xs : list A.

(* -------------------------------------------------------------------------- *)

(* Creating an empty vector: [create]. *)

(* A new vector has logical length 0 and physical capacity 0. *)

Definition create (_ : unit) : vector A :=
  let _n := 0%uint63 in
  do a ← make _n inhabitant ;
  (_n, a).

Lemma wp_create :
  wp (create ()) (λ v, isVector v []).
Proof.
  unfold create. wp_make a. wp_ret. introIsVector; eauto with int.
Qed.

(* -------------------------------------------------------------------------- *)

(* Popping an element off the right end of a nonempty vector: [pop]. *)

(* The newly emptied slot is not overwritten with a default value. *)

Definition pop v : A * vector A :=
  let (_n, a) := v in
  let _i := (_n - 1)%uint63 in
  do x ← get a _i ;
  (x, (_i, a)).

Lemma wp_pop v xs :
  isVector v xs →
  0 < len xs →
  wp (pop v) (λ '(x, v),
    let i := len xs - 1 in
    x = xs !!! i ∧
    isVector v (initial_seg i xs)
  ).
Proof.
  intros. unfold pop. destructIsVector _n a.
  wp_get x.
  wp_ret. split; [ eauto |].
  introIsVectorWithWitness ({[x]} ++ unoccupied).
  + list. eauto with int.
  + subst x. isArray.
Qed.

(* -------------------------------------------------------------------------- *)

End Operations.
