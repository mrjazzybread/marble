From stdpp Require Import list.
From listz Require Import listz.
From marble Require Import tactics.

(* -------------------------------------------------------------------------- *)

(* [simplify_list_permutation_goal] simplifies a goal of the form [xs ≃ ys],
   that is, an obligation to prove that the lists [xs] and [ys] are equal up
   to a permutation of their elements. *)

Local Infix "≃" := (Permutation)
  (at level 70, no associativity).

Lemma identity_permutation {A} (xs ys : list A) :
  xs = ys → xs ≃ ys.
Proof. intros. subst. eauto. Qed.

Ltac simplify_list_permutation_goal :=
  list;
  repeat rewrite app_assoc;
  repeat eapply Permutation_app_tail;
  repeat rewrite <- app_assoc;
  repeat eapply Permutation_app_head;
  try solve [ eapply identity_permutation; chop_list_equality_goal ].

(* -------------------------------------------------------------------------- *)

(* [clarify] is a short-hand for the union of
   [simplify_list_equality_goal] and [simplify_list_permutation_goal]. *)

Ltac clarify :=
  lazymatch goal with
  | |- _ = _ =>
      simplify_list_equality_goal
  | |- _ ≃ _ =>
      simplify_list_permutation_goal
  | _ =>
      idtac
  end.

(* -------------------------------------------------------------------------- *)

(* The tactic [unmodified_outside_seg] can (sometimes) prove a goal of
   the form [unmodified_outside_seg xs xs' i j]. It destructs the most
   recent hypothesis of the form [disjoint_seg _ _ _ _], if it can
   find one; then it uses [clarify] to reduce the goal to a trivial
   equality. It is quite ad hoc. *)

Ltac unmodified_outside_seg :=
  try match goal with h: disjoint_seg _ _ _ _ |- _ => destruct h end;
  clarify; eauto.

(* -------------------------------------------------------------------------- *)

(* The tactic [recognize_named_lookups] detects hypotheses of the form
   [x = xs !!! i] and uses them to replace [xs !!! i] with [x] both in
   the goal and in all hypotheses. *)

Ltac recognize_named_lookups :=
  repeat match goal with h: ?x = ?xs !!! ?i |- _ =>
    try rewrite <- !h in *;
    revert h
  end;
  intros.

(* -------------------------------------------------------------------------- *)

(* The tactic [recognize] is a short-hand for the composition of the
   above two tactics. *)

Ltac recognize :=
  recognize_singleton_segments; recognize_named_lookups.
