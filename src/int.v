From stdpp Require Import numbers.
From Stdlib Require Import Uint63.
(* TODO why is [of_to_Z] an axiom? *)

(* Documentation:
   https://rocq-prover.org/doc/V9.0.1/corelib/Corelib.Numbers.Cyclic.Int63.Uint63Axioms.html
   https://rocq-prover.org/doc/v9.2/stdlib/Stdlib.Numbers.Cyclic.Int63.Uint63.html
 *)

Open Scope Z_scope.
Implicit Types i : int.
Implicit Types z : Z.

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

(* Round-trip properties. *)

Goal ∀ i, π (φ i) = i.
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

(* φ is injective. *)

Goal ∀ i1 i2, φ i1 = φ i2 → i1 = i2.
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

Lemma to_Z_ge_0 i :
  0 ≤ φ i.
Proof.
  apply (to_Z_bounded i).
Qed.

Lemma to_Z_lt_wB i :
  φ i < wB.
Proof.
  apply (to_Z_bounded i).
Qed.

Global Hint Resolve
  to_Z_ge_0 to_Z_lt_wB
: int.

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
