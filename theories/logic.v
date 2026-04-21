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

From stdpp Require Import numbers.
Open Scope Z_scope.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

(* -------------------------------------------------------------------------- *)

(* [on_seg i k P] means that [P j] is true of every index [j]
   in the semi-open interval [i, k). *)

Definition on_seg i k (P : Z → Prop) :=
  ∀ j, i ≤ j < k → P j.

Lemma on_seg_init i k P : k ≤ i → on_seg i k P.
Proof. unfold on_seg. lia. Qed.

Lemma on_seg_step_up i k P : on_seg i k P → P k → on_seg i (k+1) P.
Proof.
  unfold on_seg. intros.
  case (decide (j = k)); intros; try subst; eauto with lia.
Qed.

Lemma on_seg_step_down i k P : on_seg (i+1) k P → P i → on_seg i k P.
Proof.
  unfold on_seg. intros.
  case (decide (j = i)); intros; try subst; eauto with lia.
Qed.

Global Hint Unfold on_seg : on_seg.

Global Hint Resolve
  on_seg_init
  on_seg_step_up
  on_seg_step_down
: on_seg.
