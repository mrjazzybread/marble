(******************************************************************************)
(*                                                                            *)
(*                                  Marble                                    *)
(*                                                                            *)
(*                       François Pottier, Inria Paris                        *)
(*                                                                            *)
(*       Copyright 2026--2026 Inria. All rights reserved. This file is        *)
(*       distributed under the terms of the GNU Library General Public        *)
(*       License, with an exception, as described in the file LICENSE.        *)
(*                                                                            *)
(******************************************************************************)

From stdpp Require Import numbers list.
From listz Require Import listz.
Notation len := length.
From Stdlib Require Import Uint63.
From Stdlib Require Import Array.PArray.
From marble Require Import tactics bool int array wp.
Implicit Types _i _j _k _n : int.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

(* -------------------------------------------------------------------------- *)

(* A value of type [darray A d] is an array of type [array A] packaged with
   a proof of the equation [default a = d], which means that the default
   value of this array is [d]. *)

Definition darray A d :=
  { a : array A | default a = d }.

Section D.

Context {A : Type}.

Implicit Type d : A.

(* The five basic operations on this type are [make], [length], [get], [set],
   and [init]. *)

Definition make _n d : darray A d :=
  exist (make _n d) (default_make A d _n).

Definition length {d} (a : darray A d) : int :=
  length (`a).

Definition get {d} (a : darray A d) _i : A :=
  get (`a) _i.

Lemma set_obligation {d} (a : darray A d) _i x :
  default (set (`a) _i x) = d.
Proof.
  destruct a as [ a pf ]. simpl.
  transitivity (default a).
  + simple eapply default_set.
  + exact pf.
Qed.

Definition set {d} (a : darray A d) _i x : darray A d :=
  exist (set (`a) _i x) (set_obligation a _i x).

Implicit Type f : int → A.

Context `{Inhabited A}.

Definition init _n (f : int → A) : darray A inhabitant :=
  exist (init _n f) (default_init _n f).

(* -------------------------------------------------------------------------- *)

(* Reasoning rules. *)

Implicit Type xs : list A.

Definition isDArray {d} (a : darray A d) xs :=
  isArray (`a) xs.

Lemma wp_make d :
  ∀Int _n n,
  0 ≤ n ≤ max_array_length →
  wp (make _n d) (λ a, isDArray a (replicate n d)).
Proof.
  unfold make, isDArray. intros.
  eapply wp_exist. simpl.
  wp_make a. intro. assumption.
Qed.

Lemma wp_length {d} (a : darray A d) xs :
  isDArray a xs →
  wp (length a) (λ _n, isInt _n (len xs)).
Proof.
  unfold length, isDArray. intros.
  wp_length _n. assumption.
Qed.

Lemma wp_get {d} _i i (a : darray A d) xs :
  isInt _i i →
  isDArray a xs →
  valid i xs →
  wp (get a _i) (λ x, x = xs !!! i).
Proof.
  unfold get, isDArray. intros.
  destruct a as [ a pf ]. simpl.
  wp_get x. assumption.
Qed.

Lemma wp_set {d} _i i (a : darray A d) xs x :
  isInt _i i →
  isDArray a xs →
  valid i xs →
  wp (set a _i x) (λ a', isDArray a' (<[i := x]>xs)).
Proof.
  unfold set, isDArray. intros.
  eapply wp_exist. simpl.
  destruct a as [ a pf ]. simpl.
  wp_set. intros _. assumption.
Qed.

Lemma wp_init (ψ : Z → A) _n n f :
  isInt _n n →
  0 ≤ n ≤ max_array_length →
  (∀Int _i i, 0 ≤ i < n → wp (f _i) (eq (ψ i))) →
  wp (init _n f) (λ a, isDArray a (listz.init n ψ)).
Proof.
  unfold init, isDArray. intros.
  eapply wp_exist. simpl.
  wp_op wp_init introducing: a.
  intros _. assumption.
Qed.

End D.
