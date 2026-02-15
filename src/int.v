From stdpp Require Import numbers.
From Stdlib Require Import Uint63.
(* TODO why is [of_to_Z] an axiom? *)

(* Documentation:
   https://rocq-prover.org/doc/V9.0.1/corelib/Corelib.Numbers.Cyclic.Int63.Uint63Axioms.html
   https://rocq-prover.org/doc/v9.2/stdlib/Stdlib.Numbers.Cyclic.Int63.Uint63.html
 *)

Open Scope Z_scope.
Implicit Types _i : int.
Implicit Types  i : nat.
Implicit Types  z : Z.

(* -------------------------------------------------------------------------- *)

(* [unsigned z] means that [z] lies in the interval of the unsigned
   machine integers. *)

Notation unsigned z :=
  (0 ≤ z < wB).

(* -------------------------------------------------------------------------- *)

(* [φ : int → Z] is an injection. *)
(* [π : Z → int] is a projection. *)

Global Notation "'φ'" := (to_Z).
Global Notation "'π'" := (of_Z).

Global Hint Rewrite
  to_Z_0
  to_Z_1
: int.

(* Round-trip properties. *)

Goal ∀ _i, π (φ _i) = _i.
Proof. apply of_to_Z. Qed.

Lemma to_of_Z z :
  unsigned z →
  φ (π z) = z.
Proof.
  rewrite of_Z_spec. intros. eauto using Z.mod_small.
Qed.
(* This is a reformulation of [is_int]. *)

Goal ∀ z,
  φ (π z) = z `mod` wB.
Proof.
  apply of_Z_spec.
Qed.

Global Hint Rewrite
  of_to_Z
  to_of_Z
  using lia
: int.

Global Ltac int :=
  autorewrite with int.

Global Tactic Notation "int" "in" hyp(h) :=
  autorewrite with int in h.

(* φ is injective. *)

Goal ∀ _i1 _i2, φ _i1 = φ _i2 → _i1 = _i2.
Proof. eapply to_Z_inj. Qed.

(* π, restricted to the interval of the unsigned machine integers,
   is injective. *)

Lemma of_Z_inj z1 z2 :
  unsigned z1 →
  unsigned z2 →
  π z1 = π z2 →
  z1 = z2.
Proof.
  intros.
  rewrite <- (to_of_Z z1) by eauto.
  rewrite <- (to_of_Z z2) by eauto.
  congruence.
Qed.

Lemma of_Z_inj' z1 z2 :
  unsigned z1 →
  unsigned z2 →
  z1 ≠ z2 →
  π z1 ≠ π z2.
Proof.
  intros ? ? Hzz ?. apply Hzz. eauto using of_Z_inj.
Qed.

(* The image of φ is the interval of the unsigned machine integers. *)

Lemma to_Z_ge_0 _i :
  0 ≤ φ _i.
Proof.
  apply (to_Z_bounded _i).
Qed.

Lemma to_Z_lt_wB _i :
  φ _i < wB.
Proof.
  apply (to_Z_bounded _i).
Qed.

Global Hint Resolve
  to_Z_ge_0 to_Z_lt_wB
: lia.

(* -------------------------------------------------------------------------- *)

(* Addition commutes with projection. *)

Lemma add_spec' z1 z2 :
  (π z1 + π z2)%uint63 = π (z1 + z2).
Proof.
  eapply to_Z_inj.
  (* Rewrite on the left. *)
  rewrite add_spec.
  (* Rewrite three occurrences of [φ . π]. *)
  rewrite !of_Z_spec.
  (* A property of modulus. *)
  rewrite <- Z.add_mod by eauto. eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* A relational view of the connection between [int] and [nat]. *)

Definition isInt (_i : int) (i : nat) :=
  _i = of_nat i.

Ltac introIsInt :=
  unfold isInt.

Ltac destructIsInt :=
  match goal with h: isInt ?_i _ |- _ =>
    unfold isInt in h; try subst _i
  end.

Lemma introIsInt _i i :
  _i = of_nat i →
  isInt _i i.
Proof.
  intros. introIsInt. eauto.
Qed.

Global Hint Resolve
  introIsInt
: lia.

Global Hint Rewrite
  Z2Nat.id
  using (eauto with lia)
: int.

(* Addition. *)

Lemma succ_spec _i i :
  isInt _i i →
  isInt (_i+1) (i+1)%nat.
Proof.
  intros. introIsInt. destructIsInt.
  change 1%uint63 with (π 1%Z).
  rewrite add_spec'. f_equal. lia.
Qed.

Lemma add_spec _i i _j j :
  isInt _i i →
  isInt _j j →
  isInt (_i+_j) (i+j)%nat.
Proof.
  intros. introIsInt. repeat destructIsInt.
  rewrite add_spec'. f_equal. lia.
Qed.
