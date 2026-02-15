From stdpp Require Import list.

Lemma replicate_is_repeat {A} n (x : list A) :
  replicate n x = List.repeat x n.
Proof.
  revert n. induction n as [| n]; simpl; congruence.
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

Lemma replicate_0 {A} (x : A) :
  replicate 0 x = [].
Proof. eauto. Qed.

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
  Nat.sub_diag
  @insert_app_l
  @insert_app_r_alt
  @insert_replicate_0
  using (list; lia)
: insert.

Global Ltac insert :=
  autorewrite with insert.

Global Tactic Notation "insert" "in" hyp(h) :=
  autorewrite with insert in h.
