From stdpp Require Import list.
From marble Require Import tactics list_extra.

(* The tactic [recognize_singleton_segments] detects a segment of the form
   [seg i j xs] in the goal, where [i + 1 = j] can be proved, and replaces
   this segment with a singleton {[xs !!! i]}. *)

Ltac recognize_singleton_segments :=
  repeat match goal with |- context[seg ?i ?j ?xs] =>
    erewrite (seg_is_singleton xs) by lia
  end.

(* The tactic [recognize_named_lookups] detects hypotheses of the form
   [x = xs !!! i] and uses them to replace [xs !!! i] with [x] both in
   the goal and in all hypotheses. *)

Ltac recognize_named_lookups :=
  repeat match goal with h: ?x = ?xs !!! ?i |- _ =>
    try rewrite <- !h in *;
    revert h
  end;
  intros.

(* The tactic [recognize] is a short-hand for the composition of the
   above two tactics. *)

Ltac recognize :=
  recognize_singleton_segments; recognize_named_lookups.

(* The tactic [use_known_permutation] detects a hypothesis of the form
   [xs ≃ ys], where [xs] occurs in the goal, and uses it to replace [xs]
   with [ys] in the goal. (Of course this requires the surrounding context
   to be compatible with such a rewriting step.) *)

Ltac use_known_permutation :=
  match goal with h: Permutation ?xs ?ys |- context[?xs] =>
    rewrite h
  end.

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
