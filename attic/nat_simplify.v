From Stdlib Require Import ZArithRing.
From stdpp Require Import numbers.

(* [seed t] traverses the term [t], an arithmetic expression of type
   [nat]. At each leaf [a], it rewrites [a] into [Z.to_nat (Z.of_nat a)].
   This is a global rewrite, which affects the goal (not the term [t]
   itself), so if a variable or subterm occurs several times in [t],
   several identical rewrites take place. This is unfortunate but seems
   tolerable. *)

Local Ltac seed t :=
  match t with
  | (Nat.add ?a ?b) =>
      seed a; seed b
  | (Nat.sub ?a ?b) =>
      seed a; seed b
  | ?a =>
      (* replace [a] with [Z.to_nat (Z.of_nat a)] *)
      rewrite <- (Nat2Z.id a)
  end.

(* [autorewrite with forward] hoists [Z.to_nat] up
   through an arithmetic expression of type [nat]. *)

(* <- Z2Nat.inj_add *)
Goal ∀ a b,
  (0 ≤ b ∧ 0 ≤ a)%Z →
  Z.to_nat a + Z.to_nat b = Z.to_nat (a + b).
Proof. lia. Qed.

(* <- Z2Nat.inj_sub *)
Goal ∀ a b,
  (0 ≤ b ≤ a)%Z →
  Z.to_nat a - Z.to_nat b = Z.to_nat (a - b).
Proof. lia. Qed.

Hint Rewrite <-
  Z2Nat.inj_add
  Z2Nat.inj_sub
  using lia
: forward.

(* [autorewrite with backward] hoists [Z.of_nat] up
   through an arithmetic expression of type [Z]. *)

(* <- Nat2Z.inj_add *)
Goal ∀ a b,
  (Z.of_nat a + Z.of_nat b = Z.of_nat (a + b))%Z.
Proof. lia. Qed.

(* <- Nat2Z.inj_sub *)
Goal ∀ a b,
  b ≤ a →
  (Z.of_nat a - Z.of_nat b = Z.of_nat (a - b))%Z.
Proof. lia. Qed.

Hint Rewrite <-
  Nat2Z.inj_add
  Nat2Z.inj_sub
  using lia
: backward.

(* [eapply z_to_nat_congruent] eliminates [Z.to_nat] on both sides
   at the root of an equation. *)

Local Lemma z_to_nat_congruent (a b : Z) :
  a = b → Z.to_nat a = Z.to_nat b.
Proof. congruence. Qed.

(* [nat_simplify t] simplifies the arithmetic expression [t]
   in the goal. *)

Ltac nat_simplify t :=
  let z := fresh in
  evar (z : Z);
  let fact := fresh in
  assert (fact: t = Z.to_nat z); [
      (* Prove this assertion. *)
      (* Wrap each leaf [a] as [Z.to_nat (Z.of_nat a)]. *)
      seed t;
      (* Hoist [Z.to_nat] up to the root. *)
      autorewrite with forward;
      (* Cancel out [Z.to_nat] at the root. *)
      eapply z_to_nat_congruent;
      (* We are now looking at an equality between two expressions of
         type [Z]. The right-hand side is just [z]. Use [ring_simplify]
         to simplify the left-hand side. *)
      ring_simplify;
      (* Hoist [Z.of_nat] up to the root. *)
      autorewrite with backward;
      (* Solve this goal, by instantiating the metavariable [z]. *)
      unfold z; reflexivity
  |
      (* Exploit this assertion: *)
      subst z;
      (* Cancel out [Z.to_nat (Z.of_nat _)] at the root. *)
      rewrite Nat2Z.id in fact;
      (* Done. *)
      rewrite fact;
      clear fact
  ].

(* Assuming that the goal is an equation between two expressions of
   type [nat], [nat_simplify_lhs] simplifies its left-hand side. *)

Ltac nat_simplify_lhs :=
  match goal with |- ?lhs = ?rhs => nat_simplify lhs end.

(* Examples. *)

Local Lemma ab_minus_cb a b c :
  b + c ≤ a + b →
  a + b - c - b = a - c.
Proof. intros. nat_simplify_lhs. reflexivity. Qed.

Local Lemma ab_plus_cmb a b c :
  b ≤ c →
  a + b + (c - b) = a + c.
Proof. intros. nat_simplify_lhs. reflexivity. Qed.

Lemma ab_plus_cma a b c :
  a ≤ c →
  a + b + (c - a) = b + c.
Proof. intros. nat_simplify_lhs. reflexivity. Qed.

Lemma abc_plus_dma a b c d :
  a ≤ d →
  a + b + c + (d - a) = b + c + d.
Proof. intros. nat_simplify_lhs. reflexivity. Qed.

Lemma abc_plus_dmb a b c d :
  b ≤ d →
  a + b + c + (d - b) = a + c + d.
Proof. intros. nat_simplify_lhs. reflexivity. Qed.

Lemma abc_plus_dmc a b c d :
  c ≤ d →
  a + b + c + (d - c) = a + b + d.
Proof. intros. nat_simplify_lhs. reflexivity. Qed.

Lemma a_bmac a b c :
  a + c ≤ b →
  a + (b - a - c) = b - c.
Proof. intros. nat_simplify_lhs. reflexivity. Qed.
