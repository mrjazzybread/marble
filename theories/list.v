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

From stdpp Require Import list.
From listz Require Import listz.
From marble Require Import tactics bool int iteration wp.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

(* This file offers specifications of some operations on lists. *)

(* -------------------------------------------------------------------------- *)

(* Assuming that [R _x x] means that the runtime value [_x] represents
   the mathematical value [x], the assertion [isList R _xs xs] means
   that the runtime list [_xs] represents the mathematical sequence
   [xs]. *)

Notation isList := Forall2.

(* -------------------------------------------------------------------------- *)

(* Lemmas and hints about [Forall2]. *)

Lemma Forall2_nil' {_A A} (R : _A → A → Prop) :
  Forall2 R [] [].
Proof. eauto. Qed.

Lemma Forall2_singleton {_A A} (R : _A → A → Prop) _x x :
  R _x x → Forall2 R {[_x]} {[x]}.
Proof. unfold singleton, stdpp_buffer.singleton_list. eauto. Qed.

Hint Resolve
  Forall2_nil'
  Forall2_singleton
  Forall2_insert
  Forall2_app
  Forall2_seg
  Forall2_replicate
  Forall2_reverse
: marble.

(* -------------------------------------------------------------------------- *)

Section Fold.
Variable A : Type.
Implicit Type xs : list A.
Variable S : Type.
Variable body : S → A → S.

(* A specification of [fold_left], in the special case where an element
   represents itself. *)

Lemma wp_fold_left_aux xs :
  ∀ future history,
  xs = history ++ future →
  ITER_LIST
    history xs
    (λ x s Q, wp (body s x) Q)
    (λ   s Q, wp (fold_left body future s) Q).
Proof.
  induction future as [| x future ]; simpl;
  intro history; list; intro; subst xs; ITER.
  { wp_ret. }
  { change (fold_left body future (body s x))
      with (do s ← body s x ; fold_left body future s).
    wp_op Hbody shadowing: s.
    wp_op IHfuture shadowing: s.
    eauto. }
Qed.

Lemma wp_fold_left xs :
  ITER_LIST
    [] xs
    (λ x s Q, wp (body s x) Q)
    (λ   s Q, wp (fold_left body xs s) Q).
Proof.
  eapply wp_fold_left_aux. eauto.
Qed.

End Fold.

Section Fold.
Variable _A A : Type.
Variable R : _A → A → Prop.
Implicit Type _xs : list _A.
Implicit Type xs : list A.
Variable S : Type.
Variable body : S → _A → S.

(* A more general specification of [fold_left], in the general case
   where a relation [R] on elements is provided. *)

(* We provide direct proofs, but it should also be possible to provide
   an indirect proof that reuses the lemma [wp_fold_left]. *)

Lemma wp_fold_left_aux' xs :
  ∀ _future future history,
  isList R _future future →
  xs = history ++ future →
  ITER_LIST
    history xs
    (λ x s Q, ∀ _x, R _x x → wp (body s _x) Q)
    (λ   s Q, wp (fold_left body _future s) Q).
Proof.
  induction _future as [| _x _future ]; simpl;
  intros future history; list; intros HisList ->;
  inversion HisList; subst;
  ITER; list in *.
  { wp_ret. }
  { change (fold_left body _future (body s _x))
      with (do s ← body s _x ; fold_left body _future s).
    wp_op Hbody shadowing: s.
    wp_op IH_future shadowing: s.
    eauto. }
Qed.

Lemma wp_fold_left' _xs xs :
  isList R _xs xs →
  ITER_LIST
    [] xs
    (λ x s Q, ∀ _x, R _x x → wp (body s _x) Q)
    (λ   s Q, wp (fold_left body _xs s) Q).
Proof.
  intros. eapply wp_fold_left_aux'; eauto.
Qed.

End Fold.
