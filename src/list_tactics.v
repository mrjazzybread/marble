From stdpp Require Import list.
From marble Require Import tactics list_extra.

(* -------------------------------------------------------------------------- *)

(* [simplify_list_equality_goal] simplifies a goal of the form [xs = ys].
   To compensate for the lack of rewriting modulo associativity, we first
   identify and eliminate identical terms on the left-hand side and on the
   right-hand side; then we attempt to fuse adjacent list segments. *)

(* This tactic cannot fail, and does not solve the goal. *)

(* The goal should be rigid. If it contains metavariables at either end
   then they may be instantiated in incorrect ways. *)

Lemma simplify_app_l {A} (xs ys zs : list A) :
  ys = zs → xs ++ ys = xs ++ zs.
Proof. congruence. Qed.

Lemma simplify_app_r {A} (xs ys zs : list A) :
  ys = zs → ys ++ xs = zs ++ xs.
Proof. congruence. Qed.

Lemma simplify_app_l_seg {A} i1 j1 i2 j2 (xs ys zs : list A) :
  i1 = i2 → j1 = j2 → ys = zs → seg i1 j1 xs ++ ys = seg i2 j2 xs ++ zs.
Proof. congruence. Qed.

Lemma simplify_app_r_seg {A} i1 j1 i2 j2 (xs ys zs : list A) :
  i1 = i2 → j1 = j2 → ys = zs → ys ++ seg i1 j1 xs = zs ++ seg i2 j2 xs.
Proof. congruence. Qed.

Lemma simplify_seg_equality {A} i1 j1 i2 j2 (xs ys : list A) :
  i1 = i2 → j1 = j2 → xs = ys → seg i1 j1 xs = seg i2 j2 ys.
Proof. congruence. Qed.

Global Ltac simplify_seg_equality :=
  simple eapply simplify_seg_equality; [ (list; lia) | (list; lia) |].

Global Ltac simplify_list_equality_goal_left :=
  first [
    eapply simplify_app_l
  | eapply simplify_app_l_seg; [ (list; lia) | (list; lia) |]
  ].

Global Ltac simplify_list_equality_goal_right :=
  first [
    eapply simplify_app_r
  | eapply simplify_app_r_seg; [ (list; lia) | (list; lia) |]
  ].

Global Ltac simplify_list_equality_goal :=
  list;
  repeat rewrite app_assoc;
  repeat simplify_list_equality_goal_right;
  repeat rewrite <- app_assoc;
  repeat simplify_list_equality_goal_left;
  list;
  (* In case a single equality between segments remains,
     try to simplify it. *)
  try simplify_seg_equality.

(* -------------------------------------------------------------------------- *)

(* [simplify_list_permutation_goal] simplifies a goal of the form [xs ≃ ys],
   that is, an obligation to prove that the lists [xs] and [ys] are equal up
   to a permutation of their elements. *)

(* We do not use the tactic [list] because it fuses adjacent segments,
   which, in a permutation goal, can be counter-productive. *)

Local Infix "≃" := (Permutation)
  (at level 70, no associativity).

Lemma identity_permutation {A} (xs ys : list A) :
  xs = ys → xs ≃ ys.
Proof. intros. subst. eauto. Qed.

Lemma simplify_seg_permutation {A} i1 j1 i2 j2 (xs ys : list A) :
  i1 = i2 → j1 = j2 → xs = ys → seg i1 j1 xs ≃ seg i2 j2 ys.
Proof. eauto using identity_permutation, simplify_seg_equality. Qed.

Global Ltac simplify_seg_permutation :=
  simple eapply simplify_seg_permutation; [ (list; lia) | (list; lia) |].

Ltac simplify_list_permutation_goal :=
  nat;
  repeat rewrite app_assoc;
  repeat eapply Permutation_app_tail;
  repeat rewrite <- app_assoc;
  repeat eapply Permutation_app_head;
  try simplify_seg_permutation.

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

(* The tactic [recognize_empty_segments] recognizes empty segments and
   replaces them with an empty list. In principle, it should not be
   needed; however, currently, [list] misses rewriting opportunities.
   UGLY *)

Ltac recognize_empty_segments :=
  repeat rewrite* @seg_none' by lia.

(* -------------------------------------------------------------------------- *)

(* The tactic [unmodified_outside_seg] can (sometimes) prove a goal
   of the form [unmodified_outside_seg xs xs' i j]. It destructs the
   most recent hypothesis of the form [disjoint_seg _ _ _ _], if it
   can find one; then it recognizes empty segments and uses [clarify]
   to reduce the goal to a trivial equality. It is quite ad hoc. *)

Ltac unmodified_outside_seg :=
  try match goal with h: disjoint_seg _ _ _ _ |- _ => destruct h end;
  recognize_empty_segments; clarify; eauto.

(* -------------------------------------------------------------------------- *)

(* The tactic [recognize_singleton_segments] detects a segment of the form
   [seg i j xs] in the goal, where [i + 1 = j] can be proved, and replaces
   this segment with a singleton {[xs !!! i]}. *)

Ltac recognize_singleton_segments :=
  repeat match goal with |- context[seg ?i ?j ?xs] =>
    erewrite (seg_is_singleton xs) by lia
  end.

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

(* -------------------------------------------------------------------------- *)

(* The tactic [decompose_segment] detects a hypothesis of the form
   [seg i j xs ++ {[x]} = seg i (j + 1) ys]. It deduces the two
   equations [seg i j xs = seg i j ys] and [{[x]} = seg j (j + 1) ys]. *)

Ltac decompose_segment :=
  match goal with
  h: seg ?i ?j ?xs ++ {[?x]} = seg ?i (?j + 1) ?ys |- _ =>
    rewrite (split_seg j ys) in h by lia;
    eapply app_inj_1 in h; [| list; lia ];
    unpack in h
  end.
