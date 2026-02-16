From stdpp Require Import numbers.
From Stdlib Require Import Uint63.
(* TODO why is [of_to_Z] an axiom? *)
From Stdlib Require Import Wellfounded.Wellfounded.
From Equations Require Import Equations.
From array Require Import bool.

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

Lemma to_Z_inj' _i1 _i2 :
  _i1 ≠ _i2 →
  φ _i1 ≠ φ _i2.
Proof.
  intuition eauto using to_Z_inj.
Qed.

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
  intuition eauto using of_Z_inj.
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

(* [to_nat] is injective. *)

Lemma to_nat_inj _i1 _i2 :
  to_nat _i1 = to_nat _i2 →
  _i1 = _i2.
Proof.
  eauto using to_Z_inj, Z2Nat.inj with lia.
Qed.

Global Hint Resolve
  to_nat_inj
: lia.

(* -------------------------------------------------------------------------- *)

(* Addition in Z commutes with projection. *)

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

(* Subtraction in Z commutes with projection. *)

Lemma sub_spec' z1 z2 :
  (π z1 - π z2)%uint63 = π (z1 - z2).
Proof.
  eapply to_Z_inj. rewrite sub_spec, !of_Z_spec.
  rewrite <- Zminus_mod by eauto. eauto.
Qed.

(* Multiplication in Z commutes with projection. *)

Lemma mul_spec' z1 z2 :
  (π z1 * π z2)%uint63 = π (z1 * z2).
Proof.
  eapply to_Z_inj. rewrite mul_spec, !of_Z_spec.
  rewrite <- Z.mul_mod by eauto. eauto.
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

Global Hint Rewrite
  Z2Nat.id
  Nat2Z.id
  using (eauto with lia)
: int.

Lemma introIsInt' _i :
  isInt _i (to_nat _i).
Proof.
  introIsInt. int. eauto.
Qed.

Global Hint Resolve
  introIsInt
: int.

(* Addition. *)

Lemma succ_compat _i i :
  isInt _i i →
  isInt (_i+1) (i+1)%nat.
Proof.
  intros. introIsInt. destructIsInt.
  change 1%uint63 with (π 1%Z).
  rewrite add_spec'. f_equal. lia.
Qed.

Lemma add_compat _i i _j j :
  isInt _i i →
  isInt _j j →
  isInt (_i+_j) (i+j)%nat.
Proof.
  intros. introIsInt. repeat destructIsInt.
  rewrite add_spec'. f_equal. lia.
Qed.

(* Subtraction. *)

Lemma sub_compat _i i _j j :
  isInt _i i →
  isInt _j j →
  (j < i)%nat →
  isInt (_i-_j) (i-j)%nat.
Proof.
  intros. introIsInt. repeat destructIsInt.
  rewrite sub_spec'. f_equal. lia.
Qed.

(* Multiplication. *)

Lemma mul_compat _i i _j j :
  isInt _i i →
  isInt _j j →
  isInt (_i*_j) (i*j)%nat.
Proof.
  intros. introIsInt. repeat destructIsInt.
  rewrite mul_spec'. f_equal. lia.
Qed.

Global Hint Resolve
  succ_compat
  add_compat
  sub_compat
  mul_compat
: int.

(* The representable natural integers. *)

Definition wBN : nat :=
  Z.to_nat wB.

Local Notation representable i :=
  (i < wBN)%nat.

Lemma representable_def i :
  representable i ↔ unsigned (Z.of_nat i).
Proof.
  unfold wBN. lia.
Qed.

Local Notation proj i :=
  (i `mod` wBN)%nat.

(* The lemmas that relate [Nat.modulo] and [Z.modulo] are
   [Nat2Z.inj_mod] and [Z2Nat.inj_mod]. *)

Lemma proj_def i :
  proj i = to_nat (π (Z.of_nat i)).
Proof.
  generalize wB_pos; intro HwB.
  rewrite of_Z_spec. unfold wBN.
  rewrite Znat.Z2Nat.inj_mod by lia.
  int. eauto.
Qed.

Lemma representable_proj i :
  representable i →
  proj i = i.
Proof.
  eauto using Nat.mod_small.
Qed.

Global Hint Resolve
  representable_proj
: lia.

(* Equality. *)

Lemma eqb_spec_negated _i _j :
  (_i =? _j)%uint63 = false ↔ (_j ≠ _i).
Proof.
  generalize (eqb_spec _i _j); intro.
  destruct ((_i =? _j)%uint63).
  (* I believe [lia] should work here, but it doesn't. *)
  + assert (_i = _j) by tauto. subst. split; congruence.
  + assert (_i ≠ _j).
    { intro. assert (false = true) by tauto. congruence. }
    split; congruence.
Qed.

Lemma eq_compat _i i _j j :
  isInt _i i →
  isInt _j j →
  isBool (eqb _i _j) (proj i = proj j).
Proof.
  intros. unfold isBool. repeat destructIsInt.
  rewrite !proj_def.
  rewrite eqb_spec.
  split; [ congruence | eauto using to_nat_inj ].
Qed.

Lemma eq_compat' _i i _j j :
  isInt _i i →
  isInt _j j →
  representable i →
  representable j →
  isBool (eqb _i _j) (i = j).
Proof.
  intros. eapply isBool_conseq; [ eapply eq_compat; eauto |].
  rewrite !representable_proj by eauto. tauto.
Qed.

(* Comparison. *)

Global Hint Resolve
  Z.mod_pos
: lia.

Lemma ltb_spec_negated _i _j :
  (_i <? _j)%uint63 = false ↔ (φ _j ≤ φ _i)%Z.
Proof.
  generalize (ltb_spec _i _j); intro.
  destruct ((_i <? _j)%uint63); lia.
Qed.

Lemma ltb_compat _i i _j j :
  isInt _i i →
  isInt _j j →
  isBool (ltb _i _j) (proj i < proj j)%nat.
Proof.
  generalize wB_pos; intro HwB.
  intros. unfold isBool. repeat destructIsInt.
  rewrite ltb_spec.
  rewrite !of_Z_spec. unfold wBN.
  rewrite <- (Nat2Z.id i) at 2.
  rewrite <- (Nat2Z.id j) at 2.
  rewrite <- !Z2Nat.inj_mod by eauto with lia.
  apply Z2Nat.inj_lt; eauto with lia.
Qed.

Lemma ltb_compat' _i i _j j :
  isInt _i i →
  isInt _j j →
  representable i →
  representable j →
  isBool (ltb _i _j) (i < j)%nat.
Proof.
  intros. eapply isBool_conseq; [ eapply ltb_compat; eauto |].
  rewrite !representable_proj by eauto. tauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Well-foundedness of an ordering on machine integers. *)

Definition ilt _i _j :=
  φ _i < φ _j.

Lemma ltb_spec' _i _j :
  ltb _i _j = true ↔ ilt _i _j.
Proof.
  unfold ilt. rewrite ltb_spec. tauto.
Qed.

Lemma ilt_alt_def _i _j :
  ilt _i _j ↔ 0 ≤ φ _i < φ _j.
Proof.
  unfold ilt. split; eauto with lia.
Qed.

Lemma ilt_wf : well_founded ilt.
Proof.
  eapply wf_incl; [| eapply Z.lt_wf_projected with (f := φ) ].
  intros _i _j. rewrite ilt_alt_def. eauto.
Qed.

Global Instance Wf_ilt : WellFounded ilt := ilt_wf.
