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
  unfold isVector; unfold vectorInv; eexists; list; split.

Local Ltac introIsVectorWithWitness u :=
  unfold isVector; unfold vectorInv; exists u; list; split.

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

(* Random access: [get] and [set]. *)

Definition get v _i : A :=
  let (_n, a) := v in
  a.[_i].

Lemma wp_get v xs _i i :
  isInt _i i →
  isVector v xs →
  valid i xs →
  wp (get v _i) (λ x, x = xs !!! i).
Proof.
  intros. unfold get. destructIsVector _n a. wp_get x. eauto.
Qed.

Definition set v _i x : vector A :=
  let (_n, a) := v in
  do a ← a.[_i <- x] ;
  (_n, a).

Lemma wp_set v xs _i i x :
  isInt _i i →
  isVector v xs →
  valid i xs →
  wp (set v _i x) (λ v', isVector v' (<[i := x]>xs)).
Proof.
  intros. unfold set. destructIsVector _n a.
  wp_set. wp_ret. introIsVector; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Popping an element off the end of a nonempty vector: [pop]. *)

(* The newly emptied slot is not overwritten with a default value. *)

Definition pop v : A * vector A :=
  let (_n, a) := v in
  let _i := (_n - 1)%uint63 in
  do x ← a.[_i] ;
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
  wp_get x. wp_ret. split; [ eauto |].
  introIsVectorWithWitness ({[x]} ++ unoccupied).
  + eauto with int.
  + subst x. isArray.
Qed.

(* -------------------------------------------------------------------------- *)

(* TODO *)
Variable really_ensure_capacity : vector A → int → array A.

Lemma wp_really_ensure_capacity v xs _n' n' :
  isInt _n' n' →
  representable n' →
  n' ≤ max_array_length →
  wp (really_ensure_capacity v _n') (λ a ,
    ∃ unoccupied,
    isArray a (xs ++ unoccupied) ∧
    n' ≤ len xs + len unoccupied
  ).
Proof.
Admitted.

(* -------------------------------------------------------------------------- *)

(* Pushing an element onto the end of a vector: [push]. *)

Definition push v x : vector A :=
  let (_n, a) := v in
  (* Ensure that sufficient space exists. *)
  let _n' := (_n + 1)%uint63 in
  do capacity ← length a ;
  do a ← (
    if (_n' ≤? capacity)%uint63 then a
    else really_ensure_capacity v _n'
  ) ;
  (* A free slot now exists. *)
  do a ← a.[_n <- x] ;
  (_n', a).

Lemma wp_push v xs x :
  isVector v xs →
  len xs + 1 ≤ max_array_length →
  wp (push v x) (λ v, isVector v (xs ++ {[x]})).
Proof.
  intros. cbv delta [ push ]. destructIsVector _n a.
  wp_length capacity.
  (* We are looking at the [if] construct. At the join point,
     at least one free slot exists in the array. *)
  eapply wp_bind with (P := λ a,
    ∃ unoccupied',
    isArray a (xs ++ unoccupied') ∧
    len xs + 1 ≤ len xs + len unoccupied'
      (* equivalent to: 0 < len unoccupied' *)
  ).
  { wp_if.
    (* Case: there is still room. *)
    + wp_ret. eauto with lia.
    (* Case: the array must be grown. *)
    + eauto using wp_really_ensure_capacity with int representable. }
  clear dependent a unoccupied. intros a (unoccupied & ? & ?).
  (* Write; return. *)
  wp_set. wp_ret.
  introIsVectorWithWitness (final_seg 1 unoccupied).
  + eauto with int.
  + isArray.
    rewrite (seg_intro unoccupied) at 1. list. eauto.
Qed.

(* -------------------------------------------------------------------------- *)

End Operations.
