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
From marble Require Import tactics bool int iteration wp list.
From Corelib Require Derive.

(* -------------------------------------------------------------------------- *)

(* [sum xs] is the sum of the elements of a list [xs : list Z]. *)

(* The function [sum] is used in the specification of [partial_sum],
   later on. *)

Definition sum xs :=
  fold_left (λ s x, s + x) xs 0.

Lemma sum_singleton x :
  sum {[x]} = x.
Proof.
  reflexivity.
Qed.

Lemma sum_app xs ys :
  sum (xs ++ ys) = sum xs + sum ys.
Proof.
  unfold sum.
  generalize 0 at 1 2.
  revert xs ys.
  induction xs as [| x xs ]; intros; simpl.
  { revert ys z.
    induction ys as [| y ys ]; intros; simpl.
    { lia. }
    { rewrite (IHys (z + y)).
      rewrite (IHys (0 + y)).
      lia. }
  }
  { rewrite IHxs. eauto. }
Qed.

(* -------------------------------------------------------------------------- *)

(* This instance is needed by [wp_if] below. *)

Local Instance isBool_Z_leb (i j : Z) :
  isBool1 (i <=? j)%Z (i ≤ j).
Proof.
  unfold isBool. destruct (i <=? j) eqn:?; lia.
Qed.

(* [partial_sum] is an example of using [fold_left_cps] to set up an
   exitable loop. This function computes the sum of the elements of
   a list, but stops if the running sum exceeds [limit]. *)

Section PartialSum.

Variable limit        : Z.
Variable limit_nonneg : 0 ≤ limit.

Definition partial_sum_cps xs s k :=
  let body s x k :=
    let s := s + x in
    if Z.leb s limit then k s else s
  in
  fold_left_cps body xs s k.

Definition partial_sum xs :=
  partial_sum_cps xs 0 (λ s, s).

(* [partial_sum_inv] is the invariant that is satisfied as long as
   the loop continues normally. *)

Definition partial_sum_inv xs s :=
  s = sum xs ∧ s ≤ limit.

(* [partial_sum_exit] is the property that is satisfied if the loop
   exits early. *)

Definition partial_sum_exit xs s :=
  ∃ xs',
  s = sum xs' ∧
  xs' `prefix_of` xs ∧
  limit < s.

(* The postcondition of [partial_sum] is the disjunction of these
   properties. *)

Definition partial_sum_post xs s :=
  partial_sum_inv xs s   ∨
  partial_sum_exit xs s.

(* [partial_sum] is correct. *)

(* The proof does not require induction. Induction has been used already
   to establish the lemma [wp_fold_left_cps]; now this lemma provides us
   with a Hoare-style reasoning rule. *)

Lemma wp_partial_sum xs :
  wp (partial_sum xs) (partial_sum_post xs).
Proof.
  unfold partial_sum.
  eapply wp_cps_id.
  unfold partial_sum_cps.
  eapply wp_cps_eta.
  eapply wp_cps_conseq.
  { eapply wp_fold_left_cps
    with (past := []) (inv := partial_sum_inv) (ψ := partial_sum_exit xs).
    { prove_Proper. }
    (* Initialization. *)
    { unfold partial_sum_inv, sum; simpl. eauto. }
    (* Preservation. *)
    { intros history ? s Hinv x _ <- Hpermitted.
      unfold partial_sum_inv in *.
      assert (s + x = sum (history ++ {[x]})).
      { rewrite sum_app, sum_singleton. lia. }
      wp_cps_intro.
      wp_if; [ clear Habort | clear Hk ].
      (* Case: the loop continues. *)
      { eapply Hk; clear Hk. eauto. }
      (* Case: the loop is interrupted. *)
      { eapply Habort; clear Habort.
        unfold permitted_sequence in *.
        unfold partial_sum_exit.
        eauto with lia. }}}
  (* Completion (normal exit). *)
  { cbv beta. unfold complete_sequence. intros s (? & Hinv & ->).
    unfold partial_sum_post. eauto. }
  (* Completion (exceptional exit). *)
  { unfold partial_sum_post. eauto. }
Qed.

End PartialSum.

(* Now, optimize the code. *)

(* We obtain the direct-style code that one would write by hand,
   without going through a higher-order iteration function. *)

Derive partial_sum'
  in (∀ limit xs, partial_sum' limit xs = partial_sum limit xs)
  as partial_sum_eq.
Proof.
  intros.
  unfold partial_sum, partial_sum_cps.
  unfold fold_left_cps, fold_left_cps_aux.
  unfold partial_sum'. reflexivity.
Qed.
