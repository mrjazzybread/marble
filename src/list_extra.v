From stdpp Require Import list.

(* A variant of the lemma [drop_S]. *)

Lemma drop_S' `{Inhabited A} (xs : list A) (x : A) (i : nat) :
  i < List.length xs →
  x = xs !!! i →
  x :: drop (i + 1) xs = drop i xs.
Proof.
  intros. subst.
  replace (i + 1) with (S i) by lia.
  rewrite <- drop_S by eauto using list_lookup_lookup_total_lt with lia.
  eauto.
Qed.

Lemma replicate_is_repeat {A} n (x : list A) :
  replicate n x = List.repeat x n.
Proof.
  revert n. induction n as [| n]; simpl; congruence.
Qed.

Lemma replicate_0 {A} (x : A) :
  replicate 0 x = [].
Proof. eauto. Qed.

Lemma expand_replicate {A} n (x : A) :
  0 < n →
  replicate n x = x :: replicate (n-1) x.
Proof.
  intros. destruct n as [| n]; [ lia |].
  rewrite replicate_S. do 2 f_equal. lia.
Qed.

Lemma insert_replicate_0 {A} n (x y : A) :
  0 < n →
  <[0:=y]>(replicate n x) = [y] ++ replicate (n-1) x.
Proof.
  intros. rewrite insert_replicate_lt by eauto.
  rewrite app_nil_l. eauto.
Qed.

Lemma sub_succ (n h : nat) :
  n - (h + 1) = n - h - 1.
Proof. lia. Qed.

Lemma sub_diag' (x y : nat) :
  x ≤ y → x - y = 0.
Proof. lia. Qed.

Global Hint Rewrite
  Nat.sub_0_l Nat.sub_0_r Nat.sub_diag sub_succ
  @app_nil_l @app_nil_r
  @replicate_0
  @length_nil
  @length_cons
  @length_app
  @length_insert
  @length_replicate
: list.

Global Hint Rewrite
  <- @app_assoc
: list.

Global Ltac list :=
  autorewrite with list.

Global Tactic Notation "list" "in" hyp(h) :=
  autorewrite with list in h.

Global Hint Rewrite
  sub_diag'
  using (list; lia)
: list.

Global Hint Extern 1 (_ < List.length _) => (list; lia) : lia.

Global Hint Rewrite
  @insert_app_l
  @insert_app_r_alt
  @insert_replicate_0
  using (list; lia)
: list.

(* The tactic [apply_prefix_length] searches for a hypothesis of the form
   [xs `prefix_of` ys] and introduces a new fact [length xs ≤ length ys].
   This new fact is then simplified using the tactic [list]. *)

Global Ltac apply_prefix_length :=
  match goal with h: _ `prefix_of` _ |- _ =>
    generalize h;
    let h' := fresh h in
    intro h'; apply prefix_length in h';
    list in h'
  end.
