From stdpp Require Import numbers well_founded.
From Stdlib Require Import Uint63.
(* TODO why is [of_to_Z] an axiom? *)
From Stdlib Require Import Wellfounded.Wellfounded.
From Equations Require Import Equations.
From Equations.Prop Require Import Logic. (* [inspect] *)
Notation inspected x := (exist _ x _).
From array Require Import tactics bool wp wp_tactics iteration.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

(* This file provides support for working with unsigned primitive integers. *)

(* The type of 63-bit unsigned primitive integers is named [int]. *)

(* Documentation:
   https://rocq-prover.org/doc/V9.0.1/corelib/Corelib.Numbers.Cyclic.Int63.Uint63Axioms.html
   https://rocq-prover.org/doc/v9.2/stdlib/Stdlib.Numbers.Cyclic.Int63.Uint63.html
 *)

Open Scope Z_scope.
Implicit Types _i _j _k : int.
Implicit Types  i : nat.
Implicit Types  z : Z.

(* -------------------------------------------------------------------------- *)

(* Arithmetic lemmas of general interest (in Z). *)

Lemma to_nat_lt z n :
  (0 ≤ z)%Z →
  (z < Z.of_nat n)%Z →
  (Z.to_nat z < n)%nat.
Proof.
  lia.
Qed.

Hint Resolve to_nat_lt : lia.

(* -------------------------------------------------------------------------- *)

(* [unsigned z] means that [z] lies in the interval of the unsigned
   machine integers. *)

Notation unsigned z :=
  (0 ≤ z < wB).

(* -------------------------------------------------------------------------- *)

(* [φ : int → Z] is an injection. *)
(* [π : Z → int] is a projection. *)

Local Notation "'φ'" := (to_Z).
Local Notation "'π'" := (of_Z).

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

Global Hint Resolve to_Z_inj' : lia.

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

Global Hint Resolve of_Z_inj' : lia.

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

(* More round-trip properties involving [nat]. *)

Global Hint Rewrite
  Z2Nat.id (* ∀ z, 0 ≤ z → Z.of_nat (Z.to_nat z) = z *)
  Nat2Z.id (* ∀ n, Z.to_nat (Z.of_nat n) = n *)
  using (eauto with lia)
: int.

Lemma of_nat_to_nat _i :
  of_nat (to_nat _i) = _i.
Proof.
  int. eauto.
Qed.

(* For the reverse property, see [to_nat_of_nat] below. *)

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

(* Some properties of machine integer arithmetic. *)

Lemma add_sub_conv _i _a _b :
  (_i - _a - _b = _i - (_a + _b))%uint63.
Proof.
  eapply to_Z_inj.
  rewrite !sub_spec, !add_spec.
  rewrite Zminus_mod_idemp_l, Zminus_mod_idemp_r.
  f_equal. lia.
Qed.

Lemma add_sub_comm _i _a _b :
  (_i - _a - _b = _i - _b - _a)%uint63.
Proof.
  rewrite add_sub_conv, add_comm, add_sub_conv. eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* A relational view of the connection between [int] and [nat]. *)

Class isInt (_i : int) (i : nat) :=
  build_isInt : _i = of_nat i.

Global Hint Mode isInt ! - : typeclass_instances.
  (* Instantiate the first parameter only if its head is already known,
     that is, not a metavariable. We often encounter goals of the form
     [isInt (_i + _j) ?k], so we cannot require the second parameter to
     also be already known. *)

Lemma isInt_def _i i :
  isInt _i i ↔ _i = of_nat i.
Proof.
  tauto.
Qed.

Ltac introIsInt :=
  rewrite isInt_def.

Ltac destructIsInt :=
  match goal with h: isInt ?_i _ |- _ =>
    rewrite isInt_def in h; try subst _i
  end.

(* Beyond this point, [isInt] is opaque. *)

(* This is required, e.g., to avoid expansion of [isInt] by [funelim]. *)

Global Opaque isInt.

(* [liftIsIntAndClear] looks for a hypothesis [isInt _i i],
   replaces [_i] with [of_nat i] in the goal, and clears
   [_i] as well the hypothesis [isInt _i i]. *)

Ltac liftIsIntAndClear :=
  match goal with
  h: isInt ?_i ?i |- context[?_i] =>
    rewrite h; clear _i h
  end.

(* Making the following lemma an Instance would be very useful when we
   have a goal such as [isInt 12 12] where both parameters are known.
   However, when we have a goal such as [isInt (_i + 12) ?k],
   [introIsInt] is a bad choice; we want [add_compat] to be used in
   this case. Unfortunately, assigning a high cost to [introIsInt]
   cannot help: if [a] is the cost of [add_compat] and [c] is the cost
   of [introIsInt], we would need to have [a + c ≤ c], which is
   impossible. *)

Lemma introIsInt _i :
  isInt _i (to_nat _i).
Proof.
  introIsInt. int. eauto.
Qed.

Goal isInt 12 12.
Proof.
  tc. (* does not work, for now; TODO *)
  eauto using introIsInt.
Qed.

(* TODO special cases while waiting for the general case *)
Global Instance isInt0 :
  isInt 0 0.
Proof.
  eauto using introIsInt.
Qed.

Global Instance isInt1 :
  isInt 1 1.
Proof.
  eauto using introIsInt.
Qed.

Lemma isInt_inj_1 _i1 _i2 i :
  isInt _i1 i →
  isInt _i2 i →
  _i1 = _i2.
Proof.
  intros. repeat destructIsInt. congruence.
Qed.

(* Addition. *)

Global Instance add_compat _i i _j j :
  isInt _i i →
  isInt _j j →
  isInt (_i+_j) (i+j)%nat.
Proof.
  intros. introIsInt. repeat destructIsInt.
  rewrite add_spec'. f_equal. lia.
Qed.

(* Subtraction. *)

Global Instance sub_compat _i i _j j :
  isInt _i i →
  isInt _j j →
  (j ≤ i)%nat →
  isInt (_i-_j) (i-j)%nat.
Proof.
  intros. introIsInt. repeat destructIsInt.
  rewrite sub_spec'. f_equal. lia.
Qed.

(* Multiplication. *)

Global Instance mul_compat _i i _j j :
  isInt _i i →
  isInt _j j →
  isInt (_i*_j) (i*j)%nat.
Proof.
  intros. introIsInt. repeat destructIsInt.
  rewrite mul_spec'. f_equal. lia.
Qed.

(* The representable natural integers. *)

Definition wBN : nat :=
  Z.to_nat wB.

Definition representable_def (i : nat) :=
  (i < wBN)%nat.

   (* Use [seal] to prevent [eauto] from looking into this definition.
      Otherwise, it might try to normalize [Z.to_nat wB], which does
      not terminate. *)
   Local Definition representable_aux : seal (@representable_def). Proof. by eexists. Qed.

Class representable (i : nat) :=
  build_representable : representable_aux.(unseal) i.

Global Hint Mode representable ! : typeclass_instances.

Lemma representable_iff_nat i :
  representable i ↔ (i < wBN)%nat.
Proof.
  unfold representable.
  rewrite representable_aux.(seal_eq).
  unfold representable_def.
  tauto.
Qed.

Lemma representable_iff_Z i :
  representable i ↔ unsigned (Z.of_nat i).
Proof.
  rewrite representable_iff_nat. unfold wBN. lia.
Qed.

(* This tactic should work for every sufficiently small constant. *)
Ltac representable :=
  rewrite representable_iff_Z; split; [lia | reflexivity].
    (* [lia] proves [0 ≤ k] where [k] is a known constant. *)
    (* [reflexivity] proves [k < wB] because [<] on Z is computable
       and reduces to an equality. *)

Goal representable 0.
Proof. representable. Qed.

Goal representable 1.
Proof. representable. Qed.

Global Hint Extern 1 (representable _) =>
  representable
: typeclass_instances.

Global Instance representable_down_closed i j :
  representable j →
  (i ≤ j)%nat →
  representable i.
Proof.
  rewrite !representable_iff_nat. lia.
Qed.
  (* I believe that this instance does not cause divergence because
     it requires solving [representable ?j] first and checking [i ≤ j]
     afterwards. It cannot pick [j := i] and enter a loop. *)

(* If [i] is representable then going [nat → int → Z] is the same as
   going [nat → Z] directly. *)

Lemma to_Z_of_nat i :
  representable i →
  φ%uint63 (of_nat i) = Z.of_nat i.
Proof.
  rewrite representable_iff_Z.
  intros. rewrite to_of_Z by assumption.
  eauto.
Qed.

Hint Rewrite
  to_Z_of_nat
  using tc
: int.

Definition proj (i : nat) : nat :=
  (i `mod` wBN)%nat.

(* The lemmas that relate [Nat.modulo] and [Z.modulo] are
   [Nat2Z.inj_mod] and [Z2Nat.inj_mod]. *)

Lemma representable_iff_proj i :
  representable i ↔
  proj i = i.
Proof.
  rewrite representable_iff_nat. unfold proj, wBN.
  generalize wB_pos; intro.
  rewrite Nat.mod_small_iff by lia.
  tauto.
Qed.

Lemma representable_proj i :
  representable i →
  proj i = i.
Proof.
  rewrite representable_iff_proj. eauto.
Qed.

Global Hint Resolve
  representable_proj
: lia.

(* [of_nat], restricted to representable numbers, is injective. *)

Lemma of_nat_inj i1 i2 :
  representable i1 →
  representable i2 →
  of_nat i1 = of_nat i2 →
  i1 = i2.
Proof.
  rewrite !representable_iff_Z. eauto using Nat2Z.inj, of_Z_inj.
Qed.

Lemma of_nat_inj' i1 i2 :
  representable i1 →
  representable i2 →
  i1 ≠ i2 →
  of_nat i1 ≠ of_nat i2.
Proof.
  generalize (of_nat_inj i1 i2). tauto.
Qed.

(* [proj : nat → nat] is essentially the same as [π : Z → int]. *)

(* Recall that [of_nat : nat → int] is [π . Z.of_nat]. *)

Lemma to_nat_of_nat i :
  to_nat (of_nat i)       = proj i.
(*to_nat (π (Z.of_nat i)) = proj i *)
Proof.
  generalize wB_pos; intro HwB.
  rewrite of_Z_spec. unfold proj, wBN.
  rewrite Znat.Z2Nat.inj_mod by lia.
  int. eauto.
Qed.

Hint Rewrite to_nat_of_nat : int.

(* An alternate definition of [isInt]. *)

Lemma isInt_alt _i i :
  isInt _i i ↔ to_nat _i = proj i.
Proof.
  rewrite isInt_def.
  rewrite <- to_nat_of_nat. split.
  + congruence.
  + eauto using to_nat_inj.
Qed.

(* Yet another characterization of [isInt],
   restricted to the representable natural integers. *)

Lemma isInt_repr _i i :
  representable i →
  isInt _i i ↔ to_nat _i = i.
Proof.
  intros. rewrite isInt_alt, representable_proj by eauto. tauto.
Qed.

(* [isInt], restricted to the representable natural integers,
   is injective. *)

Lemma isInt_inj_2 _i i _j j :
  isInt _i i →
  isInt _j j →
  _i = _j →
  representable i →
  representable j →
  i = j.
Proof.
  intros. rewrite !isInt_repr in * by eauto. congruence.
Qed.

(* -------------------------------------------------------------------------- *)

(* Equality. *)

(* In the absence of hypotheses about the natural integers [i] and [j], an
   equality test on the machine integers [_i] and [_j] tests the condition
   [proj i = proj j]. *)

Lemma isBool_eqb_proj _i i _j j :
  isInt _i i →
  isInt _j j →
  isBool1 (_i =? _j)%uint63 (proj i = proj j).
Proof.
  intros. eapply isBool_intro. rewrite eqb_spec.
  repeat destructIsInt.
  rewrite <- !to_nat_of_nat.
  split; [ congruence | eauto using to_nat_inj ].
Qed.

(* If the natural integers [i] and [j] are representable then an equality
   test on the machine integers [_i] and [_j] tests the condition [i = j]. *)

Global Instance isBool_eqb _i i _j j :
  isInt _i i →
  isInt _j j →
  representable i →
  representable j →
  isBool1 (_i =? _j)%uint63 (i = j).
Proof.
  intros. eapply isBool1_conseq; [ eapply isBool_eqb_proj; eauto |].
  rewrite !representable_proj by eauto. tauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Comparison. *)

Global Hint Resolve
  Z.mod_pos
: lia.

(* In the absence of hypotheses about the natural integers [i] and [j],
   the test [_i <?_j] tests the condition [proj i < proj j]. *)

Lemma isBool_ltb_proj _i i _j j :
  isInt _i i →
  isInt _j j →
  isBool1 (_i <? _j)%uint63 (proj i < proj j)%nat.
Proof.
  generalize wB_pos; intro HwB. intros.
  eapply isBool_intro; rewrite ltb_spec.
  repeat destructIsInt.
  rewrite !of_Z_spec. unfold proj, wBN.
  rewrite <- (Nat2Z.id i) at 2.
  rewrite <- (Nat2Z.id j) at 2.
  rewrite <- !Z2Nat.inj_mod by eauto with lia.
  apply Z2Nat.inj_lt; eauto with lia.
Qed.

(* If the natural integers [i] and [j] are representable then
   the test [_i <?_j] tests the condition [i < j]. *)

Global Instance isBool_ltb _i i _j j :
  isInt _i i →
  isInt _j j →
  representable i →
  representable j →
  isBool1 (_i <? _j)%uint63 (i < j)%nat.
Proof.
  intros. eapply isBool1_conseq; [ eapply isBool_ltb_proj; eauto |].
  rewrite !representable_proj by eauto. tauto.
Qed.

(* In the absence of hypotheses about the natural integers [i] and [j],
   the test [_i ≤?_j] tests the condition [proj i ≤ proj j]. *)

Lemma isBool_leb_proj _i i _j j :
  isInt _i i →
  isInt _j j →
  isBool1 (_i ≤? _j)%uint63 (proj i ≤ proj j)%nat.
Proof.
  generalize wB_pos; intro HwB. intros.
  eapply isBool_intro; rewrite leb_spec.
  repeat destructIsInt.
  rewrite !of_Z_spec. unfold proj, wBN.
  rewrite <- (Nat2Z.id i) at 2.
  rewrite <- (Nat2Z.id j) at 2.
  rewrite <- !Z2Nat.inj_mod by eauto with lia.
  apply Z2Nat.inj_le; eauto with lia.
Qed.

(* If the natural integers [i] and [j] are representable then
   the test [_i ≤?_j] tests the condition [i ≤ j]. *)

Global Instance isBool_leb _i i _j j :
  isInt _i i →
  isInt _j j →
  representable i →
  representable j →
  isBool1 (_i ≤? _j)%uint63 (i ≤ j)%nat.
Proof.
  intros. eapply isBool1_conseq; [ eapply isBool_leb_proj; eauto |].
  rewrite !representable_proj by eauto. tauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* The operations [_min] and [_max] on machine integers. *)

Definition _min _m _n : int :=
  if (_m ≤? _n)%uint63 then _m else _n.

Definition _max _m _n : int :=
  if (_m ≤? _n)%uint63 then _n else _m.

Global Instance isInt_min _m m _n n :
  isInt _m m →
  isInt _n n →
  representable m →
  representable n →
  isInt (_min _m _n) (m `min` n).
Proof.
  intros. unfold _min.
  destruct (_m ≤? _n)%uint63 eqn:Heq; isBool_magic.
  + rewrite Nat.min_l by lia. eauto.
  + rewrite Nat.min_r by lia. eauto.
Qed.

Global Instance isInt_max _m m _n n :
  isInt _m m →
  representable m →
  isInt _n n →
  representable n →
  isInt (_max _m _n) (m `max` n).
Proof.
  intros. unfold _max.
  destruct (_m ≤? _n)%uint63 eqn:Heq; isBool_magic.
  + rewrite Nat.max_r by lia. eauto.
  + rewrite Nat.max_l by lia. eauto.
Qed.

Global Instance min_representable m n :
  representable m ∨ representable n →
  representable (m `min` n).
Proof.
  rewrite !representable_iff_nat. lia.
Qed.

Global Instance max_representable m n :
  representable m →
  representable n →
  representable (m `max` n).
Proof.
  rewrite !representable_iff_nat. lia.
Qed.

(* -------------------------------------------------------------------------- *)

(* Division of machine integers. *)

(* In the natural integers, [i * j] is at least [i]. *)

Lemma mul_increasing i j :
  (j ≠ 0 → i ≤ j * i)%nat.
Proof. nia. Qed.

(* In the natural integers, [i / j] is at most [i]. *)

Lemma div_decreasing i j :
  (j ≠ 0 → i `div` j ≤ i)%nat.
Proof.
  intros. apply Nat.Div0.div_le_upper_bound. nia.
Qed.

Global Hint Resolve
  mul_increasing
  div_decreasing
: lia.

(* If [i] and [j] are representable, then so is [i / j]. *)

(* No need to make this an instance, as it is already solved
   thanks to [div_decreasing]. *)

Local Lemma div_representable i j :
  representable i →
  representable j →
  j ≠ 0%nat →
  representable (i / j).
Proof.
  (* assert (i `div` j ≤ i)%nat by eauto using div_decreasing. *)
  tc.
Qed.

(* Division of representable integers works. *)

Global Instance div_compat _i i _j j :
  isInt _i i →
  representable i →
  isInt _j j →
  representable j →
  j ≠ 0%nat →
  isInt (_i/_j) (i/j)%nat.
Proof.
  intros.
  rewrite isInt_repr by tc.
  rewrite div_spec.
  rewrite isInt_repr in * by eauto. subst i j.
  rewrite Z2Nat.inj_div by eauto with lia.
  eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Well-foundedness of the orderings on machine integers. *)

(* [ilt] is the ordering [<] on machine integers. *)

(* [igt] is the ordering [>] on machine integers. *)

(* [rilt _a] is the ordering [<] on machine integers, relative to the
   integer [_a]. In this ordering, [_a] is the least element, and the
   remaining machine integers are ordered above it, in a cyclic manner.
   This ordering lets us prove that a loop that counts down towards [_a]
   must end, without assuming [_a ≤ i]. There, underflow is helpful! *)

(* All three orderings are well-founded. *)

Definition ilt _i _j :=
  φ _i < φ _j.

Lemma ilt_wf : well_founded ilt.
Proof.
  eapply wf_incl; [| eapply Z.lt_wf_projected with (z := 0) (f := φ) ].
  intros _i _j. unfold ilt. eauto with lia.
Qed.

Global Instance Wf_ilt : WellFounded ilt :=
  wf_guard 32 ilt_wf.
  (* The use of [wf_guard] is meant to allow computation inside Rocq
     in spite of the opaque well-foundedness proof [ilt_wf]. *)

Definition rilt _a _i _j :=
  ilt (_i - _a) (_j - _a).

Lemma rilt_wf _a : well_founded (rilt _a).
Proof.
  eapply wf_incl; [| eapply Z.lt_wf_projected with (z := 0) (f := λ _i, φ (_i - _a)) ].
  intros _i _j. unfold rilt, ilt. eauto with lia.
Qed.

Global Instance Wf_rilt _a : WellFounded (rilt _a) :=
  wf_guard 32 (rilt_wf _a).
  (* The use of [wf_guard] is meant to allow computation inside Rocq
     in spite of the opaque well-foundedness proof [ilt_wf]. *)

Definition igt _i _j :=
  φ _j < φ _i.

Lemma igt_alt_def _i _j :
  igt _i _j ↔ φ _j < φ _i < wB.
Proof.
  unfold igt. split; eauto with lia.
Qed.

Lemma igt_wf : well_founded igt.
Proof.
  eapply wf_incl;
    [| eapply Z.lt_wf_projected with (z := 0) (f := λ _i, wB - φ _i) ].
  intros _i _j. rewrite igt_alt_def. lia.
Qed.

Global Instance Wf_igt : WellFounded igt :=
  wf_guard 32 igt_wf.
  (* The use of [wf_guard] is meant to allow computation inside Rocq
     in spite of the opaque well-foundedness proof [igt_wf]. *)

(* -------------------------------------------------------------------------- *)

(* By taking advantage of the above well-founded orderings, we are able to
   prove that a loop, counting up or counting down, must terminate. *)

(* Because we use semi-open intervals, which are closed at the bottom end
   and open at the top end, the code and the termination argument are
   asymmetric. When counting down, we use an equality test [_i =? _a].
   When counting up, we use a strict ordering test [_i <? _n]. *)

(* Incrementation is easier to reason about, so let's begin with it. *)

(* Safely incrementing a machine integer, without integer overflow. *)

Lemma safe_increment _i _j :
  φ _i < φ _j →
  (φ _i < φ (_i + 1))%Z.
Proof.
  intros.
  assert (unsigned (φ _i)) by eauto with lia.
  assert (unsigned (φ _j)) by eauto with lia.
  assert (unsigned (φ _i + 1)) by lia.
  rewrite add_spec. change (φ 1) with 1%Z.
  rewrite Z.mod_small by eauto.
  lia.
Qed.

Lemma safe_increment' _i _j :
  (_i <? _j)%uint63 = true →
  igt (_i + 1) _i.
Proof.
  rewrite ltb_spec. unfold igt. eauto using safe_increment.
Qed.

(* Safely decrementing a machine integer, without integer underflow. *)

(* The following two lemmas are correct but inconvenient, as they require
   the hypothesis [⋅φ _a ≤ φ _i], which should not be needed, because
   (thanks to underflow!) termination is guaranteed even without it.
   We keep these lemmas for the record, but they are unused. *)

Local Lemma safe_decrement _a _i :
  φ _a ≤ φ _i →
  _i ≠ _a →
  (φ (_i - 1) < φ _i)%Z.
Proof.
  intros.
  assert (unsigned (φ _a)) by eauto with lia.
  assert (unsigned (φ _i)) by eauto with lia.
  assert (φ _i ≠ φ _a) by eauto with lia.
  assert (unsigned (φ _i - 1)) by lia.
  rewrite sub_spec. change (φ 1) with 1%Z.
  rewrite Z.mod_small by eauto.
  lia.
Qed.

Local Lemma safe_decrement' _i _a :
  (_i =? _a)%uint63 = false →
  φ _a ≤ φ _i →
  ilt (_i - 1) _i.
Proof.
  rewrite bool_neg, eqb_spec.
  unfold ilt. eauto using safe_decrement.
Qed.

(* The following two lemmas remove the hypothesis [φ _a ≤ φ _i],
   but they are specialized to the case where [_a] is 0. *)

Local Lemma safe_decrement_absolute _i :
  0%Z ≠ φ _i →
  (φ (_i - 1) < φ _i)%Z.
Proof.
  intros.
  assert (unsigned (φ _i)) by eauto with lia.
  rewrite sub_spec. change (φ 1) with 1%Z.
  rewrite Z.mod_small by lia.
  lia.
Qed.

Local Lemma safe_decrement_absolute' _i :
  (_i =? 0)%uint63 = false →
  ilt (_i - 1) _i.
Proof.
  rewrite bool_neg, eqb_spec. unfold ilt. intros.
  assert (0 ≠ φ _i)%Z. { change 0%Z with (φ 0). eauto with lia. }
  eauto using safe_decrement_absolute.
Qed.

(* The following two lemmas remove the hypothesis [φ _a ≤ φ _i] and they
   accept an arbitrary choice of [_a]. The relative ordering [rilt _a] is
   used instead of the absolute ordering [ilt]. *)

Lemma safe_decrement_relative _a _i :
  _i ≠ _a →
  (φ (_i - _a - 1) < φ (_i - _a))%Z.
Proof.
  intros. eapply safe_decrement_absolute.
  rewrite sub_spec.
  symmetry.
  rewrite <- Z.cong_iff_0.
  assert (unsigned (φ _a)) by eauto with lia.
  assert (unsigned (φ _i)) by eauto with lia.
  rewrite !Z.mod_small by lia.
  eauto with lia. (* ouf *)
Qed.

Lemma safe_decrement_relative' _i _a :
  (_i =? _a)%uint63 = false →
  rilt _a (_i - 1) _i.
Proof.
  rewrite bool_neg, eqb_spec.
  unfold rilt, ilt.
  rewrite add_sub_comm.
  eauto using safe_decrement_relative.
Qed.

(* -------------------------------------------------------------------------- *)

(* Arithmetic lemmas of general interest (in nat). *)

Open Scope nat_scope.

Global Hint Rewrite
  Nat.sub_add
  using lia
: nat.

(* -------------------------------------------------------------------------- *)

(* A generic specification for a loop over a segment of the integers,
   counting down. *)

(* The producer state is a logical loop index, whose type is [nat].
   The user's observation is a physical loop index, whose type is [int].
   The semi-open interval that is enumerated is [i, k).
   The step relation is as follows. *)

(* In the definition of [step], the equation [j1 = j] means that the user
   observes the new state. Thus, the loop invariant [inv j s] means that
   the loop has run down to index [j] included and the next iteration will
   concern the index [j - 1]. *)

Definition ITER_DOWN {S}
  (body : int → nat → S → (S → Prop) → Prop)
  (loop : S → (S → Prop) → Prop)
  (i k : nat)
:=
  let step j0 _j j j1 :=
    j0 = j + 1 ∧
    j1 = j ∧
    isInt _j j ∧
    representable j ∧
    i ≤ j < k
  in
  ITER step body loop k i.
    (* initial state is [k]; final state is [i] *)

Ltac ITER_DOWN :=
  ITER.

(* In this variant, the loop indices [_k] and [_i] are explicitly passed
   as arguments to the loop. [loop _k _i s Q] means that the loop, applied
   to the extremum indices [_k] and [_i] and to the initial state [s],
   establishes the postcondition [Q]. *)

(* The precondition [P i k] typically expresses the fact that [i] and [k]
   represent a valid segment with respect to a certain data structure. *)

Definition SEGMENT_ITER_DOWN {S}
  (body : int → nat → S → (S → Prop) → Prop)
  (loop : int → int → S → (S → Prop) → Prop)
  (P : nat → nat → Prop)
:=
  ∀ _i i _k k,
  isInt _i i →
  isInt _k k →
  P i k →
  ITER_DOWN body (loop _k _i) i k.

Ltac SEGMENT_ITER_DOWN :=
  do 6 intro;
  let HP := fresh in
  intro HP; unpack in HP;
  ITER_DOWN.

(* -------------------------------------------------------------------------- *)

(* A loop, counting down, using machine integers. *)

Section Down.
Context {S : Type}.
Implicit Types s : S.

Variable _i : int.
Variable f : int → S → S.

(* [down_aux _j s] applies the loop body [f] to every machine integer from
   [_j], included, down to [_i], included. A state of type [S] is carried,
   whose initial value is [s]. *)

(* We are careful to test the condition [_j =? _i] before decrementing [_j].
   Because our semi-open intervals are closed at the bottom end, we cannot
   first decrement and then test the condition [_j <? _i]. If [_i] is zero
   then this would underflow. *)

(* We use Equations to more easily define [down_aux] by well-founded recursion
   over the loop counter [_j]. The somewhat strange [with] syntax is a way of
   expressing the test [_j =? _i]. The use of [inspect] and [inspected] is an
   idiosyncratic way of making the outcome of the test visible at the logical
   level in the branches. In the second branch, the fact that [_j =? _i] is
   false is needed in order to prove that [_j-1] is less than [_j], a fact
   which itself is required by the termination argument. *)

(* It is worth noting that the termination argument does not need the
   hypothesis [φ _i ≤ φ _j]. Even in the absence of this hypothesis,
   termination is guaranteed, thanks to underflow. This said, later on,
   when we give a specification of [down_aux], we assume [a ≤ i]. It would
   be unnatural and inconvenient to propose a specification that allows
   underflow to take place. *)

Equations down_aux _j s : S
by wf _j (rilt _i) :=
down_aux _j s with inspect (_j =? _i)%uint63 => {
| inspected true :=
    do s ← f _j s ;
    s ;
| inspected false :=
    do s ← f _j s ;
    down_aux (_j-1)%uint63 s
}.
Next Obligation.
  eauto using safe_decrement_relative'.
Qed.

(* For the record, here is an alternative direct definition of [down_aux],
   which does not use Equations. At extraction time, this definition produces
   slightly better-looking OCaml code. However, reasoning about it is more
   difficult; we lose the fixed point equation and the induction principle
   produced by Equations, which are used via the tactic [funelim]. *)
Goal int → S → S.
Proof.
  eapply (Fix (rilt_wf _i) (λ _, S → S)). intros _j self s.
  destruct (_j =? _i)%uint63 eqn:Heq.
  + refine (
      do s ← f _j s ;
      s
    ).
  + refine (
      do s ← f _j s ;
      self (_j-1)%uint63 _ s
    ).
    eauto using safe_decrement_relative'.
Defined.

(* A specification of [down_aux]. *)

Lemma wp_down_aux i _j j :
  isInt _i i →
  representable i →
  isInt _j j →
  representable j →
  i ≤ j →
  ITER_DOWN
    (λ _j j s Q, wp (f _j s) Q)
    (λ s Q, wp (down_aux _j s) Q)
    i (j + 1).
Proof.
  intros. ITER_DOWN.
  funelim (down_aux _j s); cleanup; clear Heqcall; intros; isBool_magic.
  (* Case [j = i]. *)
  { subst j. wp_op Hstep s'. wp_ret. eauto. }
  (* Case [j ≠ i]. *)
  { rename H into IH. wp_op Hstep s'. wp_op IH s''. eauto. }
Qed.

End Down.

(* [down _k _i s f] applies the loop body [f] to every machine integer from
   [_k], excluded, down to [_i], included. A state of type [S] is carried,
   whose initial value is [s]. *)

Definition down {S} _k _i (s : S) f :=
  if (_k =? _i)%uint63 then s
  else down_aux _i f (_k-1) s.

(* A specification of [down]. *)

(* This specification requires [i ≤ k]: that is, the start index [k] must
   be greater than or equal to the end index [i]. This hypothesis is
   natural: it is required to guarantee that no underflow takes place. *)

Lemma wp_down {S} (f : int → S → S) :
  SEGMENT_ITER_DOWN
    (λ _j j s Q, wp (f _j s) Q)
    (λ _k _i s Q, wp (down _k _i s f) Q)
    (λ i k, representable i ∧ representable k ∧ i ≤ k).
Proof.
  SEGMENT_ITER_DOWN. unfold down.
  wp_if.
  (* Case [k = i]. *)
  { subst k. wp_ret. eauto. }
  (* Case [k ≠ i]. *)
  { wp_op_nude @wp_down_aux. }
Qed.

(* [down _k _i s @@ λ _j s, ...] is a convenient way of writing a loop. *)

Global Notation "f '@@' x" := (f x) (at level 61, only parsing).

(* -------------------------------------------------------------------------- *)

(* A generic specification for a loop over a segment of the integers,
   counting up. *)

Section Up.

(* The type of the loop-carried state. *)
Context {S : Type}.

(* The user is allowed to choose a loop invariant [inv j s], where
   [j] is the current loop index and [s] is the current state. The
   assertion [inv j s] means that the loop has run up to index [j]
   excluded, so the next iteration will concern the index [j]. *)
Variable inv : nat → S → Prop.

(* The postcondition of the loop. *)
Variable Q : S → Prop.

(* The body of the loop is abstracted as a [wp] judgement. The proposition
   [body _j j s Q'] means that the loop body, with current index [_j] and
   current state [s], establishes the postcondition [Q']. *)
Variable body : int → nat → S → (S → Prop) → Prop.

Section IterUp.

(* The loop is abstracted as a [wp] judgement. The proposition [loop s Q]
   means that the loop, applied to the initial state [s], establishes the
   postcondition [Q]. *)
Variable loop : S → (S → Prop) → Prop.

Definition ITER_UP i k :=
  ∀ s,
  (* If the invariant holds of the start index [i] and start state [s], *)
  inv i s →
  (* If one loop iteration transforms [inv j s] to [inv (j+1) s'], *)
  (∀ _j j s ,
    isInt _j j →
    representable j →
    i ≤ j < k →
    inv j s →
    body _j j s (λ s, inv (j + 1) s)
  ) →
  (* Then, once the loop ends, the invariant holds of the index [i]
     or [k], whichever is greater, and of the final state [s]. *)
  (∀ s, inv (i `max` k) s → Q s) →
  loop s Q.

End IterUp.

Section SegmentIterUp.

(* In this variant, the loop indices [_i] and [_k] are passed as two
   explicit arguments to the loop. *)

(* The loop is abstracted as a [wp] judgement. [loop _i _k s Q] means that
   the loop, applied to the extremum indices [_i] and [_k] and to the
   initial state [s], establishes the postcondition [Q]. *)
Variable loop : int → int → S → (S → Prop) → Prop.

(* The precondition [P i k] typically expresses the fact that [i] and [k]
   represent a valid segment with respect to a certain data structure. *)
Variable P : nat → nat → Prop.

Definition SEGMENT_ITER_UP :=
  ∀ _i i _k k,
  isInt _i i →
  isInt _k k →
  P i k →
  @ITER_UP (loop _i _k) i k.

End SegmentIterUp.

End Up.

Ltac ITER_UP :=
  unfold ITER_UP;
  intro; intros Hinit Hstep Hfinish.

Ltac SEGMENT_ITER_UP :=
  unfold SEGMENT_ITER_UP;
  do 6 intro;
  let HP := fresh in
  intro HP; unpack in HP;
  ITER_UP.

(* -------------------------------------------------------------------------- *)

(* A loop, counting up from [i] to [k], using machine integers. *)

(* Our intervals are semi-open on the right end: [i] is included,
   [k] is excluded. *)

Section UpAux.
Context {S : Type}.
Implicit Types s : S.

(* We hoist the loop-invariant parameters out of the loop, because
   otherwise Equations produces ugly code where these parameters are
   carried around in a tuple, itself encoded using nested pairs. *)

Variable _k : int.
Variable f : int → S → S.

(* [up_aux _i s] applies the loop body [f] to every machine integer from
   [_i], included, up to [_k], excluded. A state of type [S] is carried,
   whose initial value is [s]. *)

(* We use Equations to more easily define [up_aux] by well-founded
   recursion over the loop counter [_i]. The somewhat strange [with]
   syntax is a way of expressing the test [_i <? _k]. The use of [inspect]
   and [inspected] is an idiosyncratic way of making the outcome of the
   test visible at the logical level in the branches. In the second
   branch, the fact that [_i <? _k] is false is needed in order to prove
   that [_i+1] is less than [_i], a fact which itself is required by the
   termination argument. *)

Equations up_aux _i s : S
by wf _i igt :=
up_aux _i s with inspect (_i <? _k)%uint63 => {
| inspected true :=
    do s ← f _i s ;
    do s ← up_aux (_i+1)%uint63 s ;
    s ;
| inspected false :=
    s
}.
Next Obligation.
  eauto using safe_increment'.
Qed.

End UpAux.

Section Up.
Context {S : Type}.
Implicit Types s : S.
Implicit Types f : int → S → S.

(* A specification of [up_aux]. *)

Lemma wp_up_aux f (inv : nat → S → Prop) (Q : S → Prop) :
  SEGMENT_ITER_UP inv Q
    (λ _j j s Q, wp (f _j s) Q)
    (λ _i _k s Q, wp (up_aux _k f _i s) Q)
    (λ i k, representable i ∧ representable k).
Proof.
  SEGMENT_ITER_UP.
  funelim (up_aux _k f _i s); cleanup; clear Heqcall; isBool_magic.
  (* Case [i < k]. *)
  { replace (i `max` k) with k in Hfinish by lia.
    wp_op Hstep s'. wp_op H s''. wp_ret. eauto. }
  (* Case [¬ i < k]. *)
  { replace (i `max` k) with i in Hfinish by lia.
    wp_ret. eauto. }
Qed.

(* A definition of [up], with reordered parameters. *)

(* [up _a _b s f] applies the loop body [f] to every machine integer from
   [_a], included, up to [_b], excluded. A state of type [S] is carried,
   whose initial value is [s]. *)

(* [up _a _b s @@ λ _i s, ...] is a convenient way of writing a loop. *)

Definition up _a _b s f :=
  up_aux _b f _a s.

(* A specification of [up]. *)

(* Copying the specification of [up_aux],
   to obtain a specification of [up],
   would be useless; they are the same up to the order of parameters. *)

Definition wp_up :=
  wp_up_aux.

End Up.

(* -------------------------------------------------------------------------- *)

(* A variant of [up], counting up from [a] to [b], with the possibility of
   interrupting the loop via an early exit: the loop body [f] returns an
   instruction to either continue or stop (break). *)

Global Notation break    := Some.
Global Notation continue := None.

Section InterruptibleUpAux.
Context {S A : Type}.
Implicit Types _a : int.
Implicit Types s : S.

(* We hoist the loop-invariant parameters out of the loop, because
   otherwise Equations produces ugly code where these parameters are
   carried around in a tuple, itself encoded using nested pairs. *)

Variable _b : int.
Variable f : int → S → S * option A.

(* [interruptible_up_aux _a s] applies the loop body [f] to every machine
   integer from [_a], included, up to [_b], excluded. A state of type [S]
   is carried, whose initial value is [s]. If [f] returns [break x] then
   the loop stops and returns the pair [(s, break x)] where [s] is the
   current state. If [f] returns [continue] then the loop continues. If
   [f] never returns [break _] then the loop runs all the way to the end
   and returns [(s, continue)] where [s] is the final state. *)

(* Another possible convention for an interruptible loop would be to
   assume that the loop-carried state contains the continuation flag
   (i.e., the state typically has type [S * option A]) and to let the
   user provide a function that inspects the current state and
   determines whether the loop should continue or stop. *)

Equations interruptible_up_aux _a s : S * option A
by wf _a igt :=
interruptible_up_aux _a s with inspect (_a <? _b)%uint63 => {
| inspected true :=
    do so ← f _a s ;
    let '(s, o) := so in
    match o with
    | continue =>
        interruptible_up_aux (_a+1)%uint63 s
    | break _ =>
        so
    end
| inspected false :=
    (s, continue)
}.
Next Obligation.
  eauto using safe_increment'.
Qed.

End InterruptibleUpAux.

Section InterruptibleUp.
Context {S A : Type}.
Implicit Types _a _b : int.
Implicit Types s : S.
Implicit Types f : int → S → S * option A.

(* The assertion [finished a b i s o] means that the loop has ended.

   It is defined as a disjunction of the following situations:

   - The loop has run at least once. [a < i ≤ b] holds.
     Furthermore, if the loop has stopped early, which is indicated
     by the condition [i < b], then [o] must be [break _].

   - The loop has not run at all, in which case [b ≤ a = i] holds.
     In this case, [i] must be [a] and [o] must be [continue]. *)

Definition finished {A} a b i s (o : option A) :=
  a < i ∧ i ≤ b ∧ (i < b → o ≠ continue) ∨
  b ≤ a ∧ i = a ∧ o = continue.

(* The assertion [finished a b i s o], as defined above, is somewhat strange,
   as it is a disjunction between the case where at least one iteration has
   taken place (a < b) and the case where none has taken place (a ≥ b). What
   seems more natural is a disjunction between the case where the bounds are
   ordered as expected (a ≤ b) and the case where they are not (a > b).
   The following lemma provides an alternate characterization of [finished]
   along these lines. *)

Lemma finished_iff a b i s (o : option A) :
  finished a b i s o ↔
   (
     (* Case [a ≤ b]: *)
       (* Then [i] lies between [a] and [b], inclusive;
          [i] is [a] if and only if the interval is empty;
          if [i] is less than [b] then we must have broken out;
          if the interval is empty then we cannot have broken out. *)
       a ≤ i ∧ i ≤ b ∧ (i = a ↔ a = b) ∧
       (i < b → o ≠ continue) ∧
       (a = b → o = continue)
     ∨
     (* Case [b < a]: *)
         (* Then [i] must be [a] and we cannot have broken out. *)
       b < a ∧ i = a ∧ o = continue
   ).
Proof.
  unfold finished. split; intros [|]; unpack; subst.
  { left. repeat split; eauto with lia. }
  { case (decide (a = b)); intros; [ subst b |].
    + left. eauto with lia.
    + right. eauto with lia. }
  { case (decide (i = a)); intros; [ subst i |].
    + right. eauto with lia.
    + left. eauto with lia. }
  { eauto with lia. }
Qed.

(* Here is a different way of expressing the same result. *)

Lemma finished_iff' a b i s (o : option A) :
  finished a b i s o ↔
   (
     (* Case [a ≤ b]: *)
       a ≤ i ∧ i ≤ b ∧ (i = a ↔ a = b) ∧
       (* If we have broken out then at least one element has been examined.
          If we have not broken out then the loop index has reached the end
          of the interval. *)
       match o with break _ => a < i | continue => i = b end
     ∨
       b < a ∧ i = a ∧ o = continue
   ).
Proof.
  cut (
    a ≤ i ∧ i ≤ b ∧ (i = a ↔ a = b) →
    (i < b → o ≠ continue) ∧ (a = b → o = continue) ↔
    match o with break _ => a < i | continue => i = b end
  ). { rewrite finished_iff. tauto. }
  intros. unpack.
  destruct o; split; intros; unpack; eauto with lia.
  { case (decide (a = b)); intros h; [ exfalso | lia ].
    match goal with H: a = b → _ |- _ => specialize (H h) end.
    congruence. }
  { case (decide (i < b)); intros h; [ exfalso | lia ].
    match goal with H: i < b → _ |- _ => specialize (H h) end.
    congruence. }
Qed.

(* This corollary describes just the case where [a ≤ b] is known to hold.
   It should the most useful corollary in practice. *)

Lemma finished_leq_iff a b i s (o : option A) :
  a ≤ b →
  finished a b i s o ↔
   (
     a ≤ i ∧ i ≤ b ∧ (i = a ↔ a = b) ∧
     match o with break _ => a < i | continue => i = b end
   ).
Proof.
  intros. rewrite finished_iff'. split.
  { intros [|]; [ tauto | lia ]. }
  { tauto. }
Qed.

(* The user is allowed to choose a loop invariant [inv a s o], where [a]
   is the current loop index, [s] is the current state, and [o] is the
   current outcome, that is, the outcome of the previous iteration. The
   assertion [inv a s o] means that the loop has run up to index [a]
   excluded, so the next iteration will concern the index [a]. *)

Variable inv : nat → S → option A → Prop.

(* A specification of [interruptible_up_aux]. *)

Lemma wp_interruptible_up_aux f (Q : S * option A → Prop) :
  ∀ _a a _b b s ,
  isInt _a a →
  representable a →
  isInt _b b →
  representable b →
  (* If the invariant initially holds, *)
  inv a s continue →
  (* If [f] preserves the invariant, *)
  (∀ _i i s ,
    isInt _i i →
    representable i →
    a ≤ i < b →
    inv i s continue →
    wp (f _i s) (λ so, let '(s, o) := so in inv (i + 1) s o)
  ) →
  (* Then, once the loop ends, [inv i s o] holds, where [i], [s], and [o] are
     the final index, final state, and final outcome. They are related by the
     assertion [finished a b i s o]. *)
  (∀ i s o,
     inv i s o →
     finished a b i s o →
     Q (s, o)
  ) →
  wp (interruptible_up_aux _b f _a s) Q.
Proof.
  unfold finished. do 9 intro. intros Hinit Hstep Hfinish.
  funelim (interruptible_up_aux _b f _a s); cleanup; clear Heqcall;
  isBool_magic.
  (* [funelim] creates an induction hypothesis that contains
     spurious parameters of type [S * option A] and [option A]. *)
  assert (dummy: option A). { exact continue. }
  (* Case [a < b]. *)
  { eapply wp_bind; [ eapply Hstep; eauto | simpl; intros [s' [|]] ? ].
    + wp_ret. eauto with lia.
    + eapply H; itc. }
  (* Case [¬ a < b]. *)
  { wp_ret. eauto with lia. }
Qed.

(* A definition of [interruptible_up], with reordered parameters. *)

Definition interruptible_up _a _b s f :=
  interruptible_up_aux _b f _a s.

(* Copying the specification of [interruptible_up_aux],
   to obtain a specification of [interruptible_up],
   would be useless; they are the same up to the order of parameters. *)

Definition wp_interruptible_up :=
  wp_interruptible_up_aux.

(* A rigid variant of the specification of [interruptible_up],
   without a quantification on [Q]. This is useful when the
   call site is flexible about the postcondition (i.e., the
   postcondition is a metavariable). *)

Lemma wp_interruptible_up_rigid f :
  ∀ _a a _b b s ,
  isInt _a a →
  representable a →
  isInt _b b →
  representable b →
  (* If the invariant initially holds, *)
  inv a s continue →
  (* If [f] preserves the invariant, *)
  (∀ _i i s ,
    isInt _i i →
    representable i →
    a ≤ i < b →
    inv i s continue →
    wp (f _i s) (λ so, let '(s, o) := so in inv (i + 1) s o)
  ) →
  (* Then, once the loop ends, [inv i s o] holds, where [i], [s], and [o] are
     the final index, final state, and final outcome. They are related by the
     assertion [finished a b i s o]. *)
  wp (interruptible_up _a _b s f) (λ so,
    let '(s, o) := so in
    exists i,
    inv i s o ∧
    finished a b i s o
  ).
Proof.
  intros. eapply wp_conseq.
  + eapply wp_interruptible_up with (Q := λ so,
      let '(s, o) := so in
      exists i,
      inv i s o ∧
      finished a b i s o
    ); eauto. (* This is so verbose... *)
  + eauto.
Qed.

End InterruptibleUp.

(* This lemma can help prove that a loop invariant can be extended. *)

(* Unfortunately, [eauto] refuses to use it as a hint, and I am also
   unable to use it via [Hint Extern]. *)

Lemma one_step_further {P : nat → Prop} i :
  (∀ j, j < i → P j) →
  P i →
  ∀ j, j < i + 1 → P j.
Proof.
  intros. case (decide (j = i)); intros; try subst; eauto with lia.
Qed.

(* -------------------------------------------------------------------------- *)

(* A variant of [interruptible_up] that does not carry a state. *)

Section InterruptibleUpUnitAux.
Context {A : Type}.
Implicit Types _a : int.

Variable _b : int.
Variable f : int → option A.

Equations interruptible_up_unit_aux _a : option A
by wf _a igt :=
interruptible_up_unit_aux _a with inspect (_a <? _b)%uint63 => {
| inspected true :=
    do o ← f _a ;
    match o with
    | continue =>
        interruptible_up_unit_aux (_a+1)%uint63
    | break _ =>
        o
    end
| inspected false :=
    continue
}.
Next Obligation.
  eauto using safe_increment'.
Qed.

End InterruptibleUpUnitAux.

(* Instead of proving a specification of [interruptible_up_unit_aux],
   we first prove that it is related with [interruptible_up_aux]. *)

(* The relation is [wus], which stands for [with_unit_state]. *)

Definition wus {A} (a : A) (sa' : unit * A) :=
  a =
    do sa' ← sa' ;
    let '(s', a') := sa' in
    a'.

Lemma interruptible_up_unit_aux_eq {A} _a _b
  (f : int → option A)
  (f' : int → unit → unit * option A) :
  (∀ _i, wus (f _i) (f' _i tt)) →
  wus
    (interruptible_up_unit_aux _b f _a)
    (interruptible_up_aux _b f' _a tt).
Proof.
  intros Hf.
  funelim (interruptible_up_unit_aux _b f _a); cleanup; clear Heqcall;
  autorewrite with interruptible_up_aux; simpl; rewrite e.
  (* [funelim] introduces a spurious parameter: *)
  assert (dummy: option A). { exact continue. }
  { rewrite Hf. destruct (f' _a ()) as [ [] [|] ]; unfold bind.
    + unfold wus. eauto.
    + eauto. }
  { unfold wus. eauto. }
Qed.

Section InterruptibleUpUnit.
Context {A : Type}.
Implicit Types _a _b : int.
Implicit Types f : int → option A.

Definition interruptible_up_unit _a _b f :=
  interruptible_up_unit_aux _b f _a.

End InterruptibleUpUnit.

(* When used with [rewrite], the following lemma allows replacing a call
   to [interruptible_up_unit] with a call to [interruptible_up]. *)

Lemma interruptible_up_unit_eq {A} _a _b (f : int → option A) :
  wus
    (interruptible_up_unit _a _b f)
    (interruptible_up _a _b tt (λ _i s, do o ← f _i ; (s, o))).
Proof.
  intros.
  unfold interruptible_up_unit, interruptible_up.
  eapply interruptible_up_unit_aux_eq.
  unfold wus, bind. eauto.
Qed.

(* We do not provide a specification of [interruptible_up_unit].
   Instead, the user is expected to rewrite using the above lemma
   and to use the specification of [interruptible_up]. This can
   introduce a little noise in the proof, but seems bearable. *)
