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
From stdpp Require Import sets propset.
From listz Require Import listz.
From marble.logic Require Import sets.
Notation len := length.
From marble Require Import tactics bool int wp iteration.

(* We prove that the specifications [ITER_SET] and [ITER_SET'] are
   equivalent. *)

Section Equivalence.

Context {S A : Type} `{SemiSet A C}.

Variable (body : A → S → WP S).
Variable (loop : S → WP S).

(* We must assume that [body] and [loop] are covariant; that is,
   they support the consequence rule. These assumptions mean that
   this equivalence proof may be a little inconvenient to use in
   practice. *)

Variable body_covariant :
  ∀ x s Q Q',
  body x s Q →
  (∀ s, Q s → Q' s) →
  body x s Q'.

Variable loop_covariant :
  ∀ s Q Q',
  loop s Q →
  (∀ s, Q s → Q' s) →
  loop s Q'.

Lemma direction1 (init xs : C) (init' : list A) :
  ITER_SET init xs body loop →
  list_to_set init' ≡ init →
  ITER_SET' init' xs body loop.
Proof.
  intros Hspec Hseed. ITER.
  eapply loop_covariant.
  { eapply Hspec with (inv :=
      λ xs s, ∃ history,
        inv history s ∧
        init' `prefix_of` history ∧
        list_to_set history ≡ xs
    ); clear Hspec.
    (* Compatibility. *)
    { clear dependent s.
      intros xs1 xs2 Hequiv. intros s ? <-.
      split; intros; unpack; pack; eauto.
      + rewrite <- Hequiv. eauto.
      + rewrite Hequiv. eauto. }
    (* Initialization. *)
    { pack; eauto. }
    (* Preservation. *)
    { clear dependent s.
      intros j0 j1 s (history0 & ? & ? & ?).
      intros x ???.
      eapply body_covariant.
      { eauto with set_solver. }
      cbv beta. pack; eauto using prefix_app_r. set_solver. }
    }
  cbv beta. clear Hspec Hbody. clear dependent s.
  intros s (xs' & Hpost).
  destruct Hpost as ((history & ? & ? & ?) & ?).
  pack; eauto. set_solver.
Qed.

Lemma list_to_set_prefix_of (xs ys : list A) :
  xs `prefix_of` ys →
  list_to_set xs ⊆ (list_to_set ys : C).
Proof.
  intros. intro x. set_unfold. eauto using elem_of_prefix.
Qed.

Lemma direction2 (init xs : C) (init' : list A) :
  ITER_SET' init' xs body loop →
  list_to_set init' ≡ init →
  ITER_SET init xs body loop.
Proof.
  intros Hspec Hseed. ITER.
  eapply loop_covariant.
  { eapply Hspec with (inv := λ history s, inv (list_to_set history) s);
    clear Hspec.
    (* Compatibility. *)
    { clear Hbody. clear dependent s.
      intros history1 history2 Hequiv.
      unfold equiv in Hequiv. subst history2.
      intros s ? <-.
      split; intros; unpack; pack; eauto. }
    (* Initialization. *)
    { set_solver. }
    (* Preservation. *)
    { clear dependent s.
      intros j0 j1 s ?. intros x ???.
      eapply body_covariant.
      { eapply Hbody; eauto.
        + rewrite <- Hseed.
          eauto using list_to_set_prefix_of.
        + set_solver. }
      cbv beta. subst j1. pack.
      rewrite list_to_set_app, list_to_set_singleton. assumption. }
  }
  cbv beta. clear Hspec Hbody. clear dependent s.
  intros s (history & Hpost).
  destruct Hpost.
  pack; eauto with set_solver.
Qed.

End Equivalence.
