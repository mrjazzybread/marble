(* The tactic [really replace i with e] replaces [i] with [e] in
   the goal, and fails if this replacement is trivial, that is,
   if [i] and [e] are identical. This can be a good thing, as it
   can cause backtracking higher up. *)

Tactic Notation "really" "replace" constr(i) "with" constr(e) :=
  let eq := fresh in
  assert (eq: i = e) by eauto with lia;
  rewrite eq; (* [rewrite eq] fails if [eq] is trivial *)
  clear eq.

Tactic Notation "really" "replace" constr(i) "with" constr(e) "in" hyp(h) :=
  let eq := fresh in
  assert (eq: i = e) by eauto with lia;
  rewrite eq in h;
  clear eq.

Tactic Notation "really" "replace" constr(i) "with" constr(e) "in" "*" :=
  let eq := fresh in
  assert (eq: i = e) by eauto with lia;
  rewrite eq in *;
  clear eq.

(* The tactic [reckon e], where [e] has type [nat], searches for
   a subexpression [e'] in the goal that is provably equal to [e]
   and replaces it with [e]. *)

(* The tactics [reckon e in h] and [reckon e in *] are similar,
   but act inside the hypothesis [h] or inside all hypotheses. *)

(* This offers a poor man's way of simplifying arithmetic expressions.
   As long as you are able to spell out the result of the desired
   simplification step, simplification will succeed. *)

Tactic Notation "reckon" constr(e) :=
  match goal with |- context[?i] =>
  match type of i with nat =>
    really replace i with e
  end end.

Tactic Notation "reckon" constr(e) "in" hyp(h) :=
  match type of h with context[?i] =>
  match type of i with nat =>
    really replace i with e in h
  end end.

Tactic Notation "reckon" constr(e) "in" "*" :=
  match goal with h: context[?i] |- _ =>
  match type of i with nat =>
    really replace i with e in *
  end end.
