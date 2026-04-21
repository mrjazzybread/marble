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

From stdpp Require Import base well_founded.

(** The statement of [Acc_dep_ind] is this: *)

Goal
  ∀ {A} (R : A → A → Prop) (P : ∀ x : A, Acc R x → Prop)
  (obligation : ∀ x : A,
    ∀ Achild : (∀ y : A, R y x → Acc R y),
    ∀ IH : (∀ y : A, ∀ r : R y x, P y (Achild y r)),
    P x (Acc_intro x Achild)
  ),
  ∀ (x : A) (Ax : Acc R x), P x Ax.
Proof.
  exact Acc_dep_ind.
Qed.

(** In the previous statement, [obligation] represents the proof
    obligation that a user of the lemma receives. The user is given
    a proof [Achild] that every child [y] of [x] is accessible and
    the induction hypothesis [IH], which states that [P y Ay] holds
    at every child [y], FOR SOME proof of accessibility [Ay],
    which happens to be [Achild y r].

    This statement can be too weak. It would be more pleasant if
    the induction hypothesis would guarantee that [P y Ay] holds
    at every child [y] and FOR EVERY proof of accessibility [Ay]
    of this child.

    Fortunately, this stronger statement can be obtained
    as a consequence of the weaker statement, as follows. *)

Lemma Acc_dep_ind_strong
  {A} (R : A → A → Prop) (P : ∀ x : A, Acc R x → Prop)
  (obligation : ∀ x : A,
    ∀ Achild : (∀ y : A, R y x → Acc R y),
    ∀ IH : (∀ y : A, ∀ Ay : Acc R y, R y x → P y Ay),
    P x (Acc_intro x Achild)
  )
: ∀ (x : A) (Ax : Acc R x), P x Ax.
Proof.
  intros.
  (* The trick is to apply the weaker statement, not to [P],
     but to the property [λ x Ax, ∀ Ax, P x Ax]. *)
  eapply (Acc_dep_ind A R (λ x Ax, ∀ Ax, P x Ax)); [| exact Ax ].
  clear x Ax. intros x Ay IH Ax.
  destruct Ax. eauto.
Qed.

(** The recommended way of applying the above lemma is to write:

      pattern x, Ax; eapply Acc_dep_ind_strong; clear x Ax

    where x and Ax are the names that appear in your goal. *)
