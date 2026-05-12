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

Section List.
Variable A : Type.
Implicit Type xs : list A.

Section Fold.
Variable S : Type.
Variable body : S → A → S.

Local Lemma prefix_refl xs : xs `prefix_of` xs.
Proof. eauto. Qed.
Local Hint Resolve prefix_refl prefix_app_l : marble.

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
End List.
