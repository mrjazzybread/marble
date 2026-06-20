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

Notation isListIntU := (isList (λ _v v, isIntU _v v)).

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

(* Iteration on a list, from left to right: [fold_left]. *)

(* [fold_left] is defined in Rocq's standard library. *)

Section Fold.
Variable A : Type.
Implicit Type xs : list A.
Variable S : Type.
Variable body : S → A → S.

(* A specification of [fold_left],
   in the special case where an element represents itself. *)

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

(* -------------------------------------------------------------------------- *)

(* Iteration on a list, from left to right, in CPS style. *)

(* Because iteration on a list is tail-recursive, the parameter [k] in
   [fold_left_cps] is invariant: it is the same in every loop iteration.
   Therefore we hoist it out of the fixed point. *)

Section FoldCPS.

Context {R A S : Type}.
Variable body : S → A → (S → R) → R.
Implicit Type xs : list A.
Implicit Type s : S.
Variable k : S → R.

Fixpoint fold_left_cps_aux xs s :=
  match xs with
  | [] =>
      k s
  | x :: xs =>
      body s x @@ λ s,
      fold_left_cps_aux xs s
  end.

Implicit Type ψ : R → Prop.

End FoldCPS.

(* Re-order the parameters so that [k] comes last. *)

Definition fold_left_cps {R A S} (body : S → A → (S → R) → R) xs s k :=
  fold_left_cps_aux body k xs s.

(* A specification of [fold_left_cps],
   in the special case where an element represents itself. *)

(* It is exactly the same as the specification of [fold_left],
   except [wp] is replaced with [wp_cps _ ψ]. *)

Lemma wp_fold_left_cps_aux {R A S} (body : S → A → (S → R) → R) xs ψ :
  ∀ future history,
  xs = history ++ future →
  ITER_LIST
    history xs
    (λ x s Q, wp_cps (body s x) Q ψ)
    (λ   s Q, wp_cps (λ k, fold_left_cps_aux body k future s) Q ψ).
Proof.
  induction future as [| x future ]; simpl;
  intro history; list; intro; subst xs; ITER.
  { eapply wp_cps_ret. eauto. }
  { eapply wp_cps_bind.
    { eapply Hbody; tc. }
    cbv beta. clear dependent s. intros s ?.
    eapply IHfuture; tc; list; tc. }
Qed.

Lemma wp_fold_left_cps {R A S} (body : S → A → (S → R) → R) xs ψ :
  ITER_LIST
    [] xs
    (λ x s Q, wp_cps (body s x) Q ψ)
    (λ   s Q, wp_cps (fold_left_cps body xs s) Q ψ).
Proof.
  eauto using wp_fold_left_cps_aux.
Qed.

(* -------------------------------------------------------------------------- *)
