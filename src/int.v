From stdpp Require Import numbers well_founded.
From Stdlib Require Import Uint63.
(* TODO why is [of_to_Z] an axiom? *)
From Stdlib Require Import Wellfounded.Wellfounded.
From Equations Require Import Equations.
From Equations.Prop Require Import Logic. (* [inspect] *)
Notation inspected x := (exist _ x _).
From marble Require Import tactics bool wp wp_tactics iteration.

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

Global Hint Rewrite
  Nat.min_l Nat.min_r
  Nat.max_l Nat.max_r
  using lia
: nat.

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

(* This helps write specifications. *)

Notation "'∀Int' _i i , P" :=
  ( ∀ _i i ,
    isInt _i i →
    P
  ) (at level 200, _i name, i name).

Notation "'∀IntR' _i i , P" :=
  ( ∀ _i i ,
    isInt _i i →
    representable i →
    P
  ) (at level 200, _i name, i name).

(* -------------------------------------------------------------------------- *)

(* Equality. *)

(* In the absence of hypotheses about the natural integers [i] and [j], an
   equality test on the machine integers [_i] and [_j] tests the condition
   [proj i = proj j]. *)

Lemma isBool_eqb_proj :
  ∀Int _i i ,
  ∀Int _j j ,
  isBool1 (_i =? _j)%uint63 (proj i = proj j).
Proof.
  intros. eapply isBool_intro. rewrite eqb_spec.
  repeat destructIsInt.
  rewrite <- !to_nat_of_nat.
  split; [ congruence | eauto using to_nat_inj ].
Qed.

(* If the natural integers [i] and [j] are representable then an equality
   test on the machine integers [_i] and [_j] tests the condition [i = j]. *)

Global Instance isBool_eqb :
  ∀IntR _i i ,
  ∀IntR _j j ,
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

Lemma isBool_ltb_proj :
  ∀Int _i i ,
  ∀Int _j j ,
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

Global Instance isBool_ltb :
  ∀IntR _i i ,
  ∀IntR _j j ,
  isBool1 (_i <? _j)%uint63 (i < j)%nat.
Proof.
  intros. eapply isBool1_conseq; [ eapply isBool_ltb_proj; eauto |].
  rewrite !representable_proj by eauto. tauto.
Qed.

(* In the absence of hypotheses about the natural integers [i] and [j],
   the test [_i ≤?_j] tests the condition [proj i ≤ proj j]. *)

Lemma isBool_leb_proj :
  ∀Int _i i ,
  ∀Int _j j ,
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

Global Instance isBool_leb :
  ∀IntR _i i ,
  ∀IntR _j j ,
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

Global Instance isInt_min :
  ∀IntR _m m ,
  ∀IntR _n n ,
  isInt (_min _m _n) (m `min` n).
Proof.
  intros. unfold _min.
  destruct (_m ≤? _n)%uint63 eqn:Heq; isBool_magic.
  + rewrite Nat.min_l by lia. eauto.
  + rewrite Nat.min_r by lia. eauto.
Qed.

Global Instance isInt_max :
  ∀IntR _m m ,
  ∀IntR _n n ,
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

Global Instance div_compat :
  ∀IntR _i i ,
  ∀IntR _j j ,
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
   The loop body is parameterized with a physical loop index,
   whose type is [int].
   The semi-open interval that is enumerated is [i, k). *)

(* The hypothesis [isInt _j j1] means that the user observes the new
   state. Thus, the loop invariant [inv j s] means that the loop has
   run down to index [j] included and the next iteration will concern
   the index [j - 1]. *)

(* Once the loop ends, the producer state is [i `min` k]. This accounts
   for the special case where [k < i] and the loop is not executed. *)

Definition ITER_DOWN {S}
  (i k : nat)
  (body : int → nat → S → WP S)
  (loop : S → WP S)
:=
  ITER
    k
    ( λ j, j = i `min` k )
    ( λ j0 j1 s Q,
      ∀ _j,
      j0 = j1 + 1 →
      i ≤ j1 < k →
      isInt _j j1 →
      body _j j1 s Q
    )
    loop.

Ltac wp_down_intros _j j s :=
  let j0 := fresh in
  wp_loop_intros j0 j s;
  intros _j ? ? ?;
  try subst j0.

(* TODO reduce redundancy? *)

Definition XITER_DOWN {S A}
  (i k : nat)
  (body : ∀ {W}, int → nat → S → (S → W) → (S → A → W) → WP W)
  (loop : S → WP (S * outcome A))
:=
  XITER
    k
    ( λ j, j = i `min` k )
    ( λ _ j0 j1 s continue break Q,
      ∀ _j,
      j0 = j1 + 1 →
      i ≤ j1 < k →
      isInt _j j1 →
      body _j j1 s continue break Q
    )
    loop.

Definition UXITER_DOWN {A}
  (i k : nat)
  (body : ∀ {W}, int → nat → (unit → W) → (A → W) → WP W)
  (loop : WP (outcome A))
:=
  UXITER
    k
    ( λ j, j = i `min` k )
    ( λ _ j0 j1 continue break Q,
      ∀ _j,
      j0 = j1 + 1 →
      i ≤ j1 < k →
      isInt _j j1 →
      body _j j1 continue break Q
    )
    loop.

(* -------------------------------------------------------------------------- *)

(* Iteration on a semi-open interval [i, k), in [int], going up. *)

(* This is the same thing as [ITER_NAT_UP], except that [body] now
   receives both [_j] and [j], related by [isInt _j j], instead of
   just [j]. *)

Definition ITER_UP {S}
  (i k : nat)
  (body : int → nat → S → WP S)
  (loop : S → WP S)
:=
  ITER_NAT_UP i k
    (λ j s Q, ∀ _j, isInt _j j → body _j j s Q)
    loop.

Ltac wp_up_intros _j j s :=
  let j1 := fresh in
  wp_loop_intros j j1 s;
  intros _j ? ? ?;
  try subst j1.

(* TODO reduce redundancy? *)

Definition XITER_UP {S A}
  (i k : nat)
  (body : ∀ {W}, int → nat → S → (S → W) → (S → A → W) → WP W)
  (loop : S → WP (S * outcome A))
:=
  XITER
    i
    ( λ j, j = i `max` k )
    ( λ _ j0 j1 s continue break Q,
      ∀ _j,
      j1 = j0 + 1 →
      i ≤ j0 < k →
      isInt _j j0 →
      body _j j0 s continue break Q
    )
    loop.

Definition UXITER_UP {A}
  (i k : nat)
  (body : ∀ {W}, int → nat → (unit → W) → (A → W) → WP W)
  (loop : WP (outcome A))
:=
  UXITER
    i
    ( λ j, j = i `max` k )
    ( λ _ j0 j1 continue break Q,
      ∀ _j,
      j1 = j0 + 1 →
      i ≤ j0 < k →
      isInt _j j0 →
      body _j j0 continue break Q
    )
    loop.

(* -------------------------------------------------------------------------- *)

(* This lemma can help prove that a loop invariant can be extended. *)

(* Unfortunately, [eauto] refuses to use it as a hint, and I am also
   unable to use it via [Hint Extern]. *)

Lemma one_step_up {P : nat → Prop} i :
  (∀ j, j < i → P j) →
  P i →
  ∀ j, j < i + 1 → P j.
Proof.
  intros. case (decide (j = i)); intros; try subst; eauto with lia.
Qed.

(* -------------------------------------------------------------------------- *)

(* A loop, counting down, using machine integers. *)

Section IterDown.
Context {S : Type}.
Implicit Types s : S.

Variable _i : int.
Variable body : int → S → S.

(* [iter_down_aux _j s] applies the loop body [body] to every machine
   integer from [_j], included, down to [_i], included. A state of type [S]
   is carried, whose initial value is [s]. *)

(* We are careful to test the condition [_j =? _i] before decrementing [_j].
   Because our semi-open intervals are closed at the bottom end, we cannot
   first decrement and then test the condition [_j <? _i]. If [_i] is zero
   then this would underflow. *)

(* We use Equations to more easily define [iter_down_aux] by well-founded
   recursion over the loop counter [_j]. The somewhat strange [with] syntax
   is a way of expressing the test [_j =? _i]. The use of [inspect] and
   [inspected] is an idiosyncratic way of making the outcome of the test
   visible at the logical level in the branches. In the second branch, the
   fact that [_j =? _i] is false is needed in order to prove that [_j - 1]
   is less than [_j], a fact which itself is required by the termination
   argument. *)

(* It is worth noting that the termination argument does not need the
   hypothesis [φ _i ≤ φ _j]. Even in the absence of this hypothesis,
   termination is guaranteed, thanks to underflow. This said, later on, when
   we give a specification of [iter_down_aux], we assume [a ≤ i]. It would
   be unnatural and inconvenient to propose a specification that allows
   underflow to take place. *)

Equations iter_down_aux _j s : S
by wf _j (rilt _i) :=
iter_down_aux _j s with inspect (_j =? _i)%uint63 => {
| inspected true :=
    do s ← body _j s ;
    s ;
| inspected false :=
    do s ← body _j s ;
    iter_down_aux (_j - 1)%uint63 s
}.
Next Obligation.
  eauto using safe_decrement_relative'.
Qed.

(* For the record, here is a direct definition of [iter_down_aux], which
   does not use Equations. At extraction time, this definition produces
   slightly better-looking OCaml code. However, reasoning about it is more
   difficult; we lose the fixed point equation and the induction principle
   produced by Equations, which are used via the tactic [funelim]. *)
Goal int → S → S.
Proof.
  eapply (Fix (rilt_wf _i) (λ _, S → S)). intros _j self s.
  destruct (_j =? _i)%uint63 eqn:Heq.
  + refine (
      do s ← body _j s ;
      s
    ).
  + refine (
      do s ← body _j s ;
      self (_j - 1)%uint63 _ s
    ).
    eauto using safe_decrement_relative'.
Defined.

End IterDown.

(* A specification of [iter_down_aux]. *)

(* This specification requires [i ≤ k]: that is, the start index [k] must
   be greater than or equal to the end index [i]. This hypothesis is
   natural: it is required to guarantee that no underflow takes place. *)

Lemma wp_iter_down_aux {S} (body : int → S → S) :
  ∀IntR _i i ,
  ∀IntR _j j ,
  i ≤ j →
  ITER_DOWN
    i (j + 1)
    (λ _j j s Q, wp (body _j s) Q)
    (λ s Q, wp (iter_down_aux _i body _j s) Q).
Proof.
  intros. ITER.
  funelim (iter_down_aux _i body _j s); cleanup; clear Heqcall;
  intros; isBool_magic; autorewrite with nat.
  (* Case [j = i]. *)
  { subst j. wp_op Hstep s'. wp_ret. eauto. }
  (* Case [j ≠ i]. *)
  { rename H into IH. wp_op Hstep s'. wp_op IH s''. eauto. }
Qed.

(* [iter_down _k _i s body] applies the loop body [body] to every machine
   integer from [_k], excluded, down to [_i], included. A state of type [S]
   is carried, whose initial value is [s]. *)

Definition iter_down {S} _k _i (s : S) body :=
  if (_k ≤? _i)%uint63 then s
  else iter_down_aux _i body (_k - 1) s.

(* A specification of [iter_down]. *)

Lemma wp_iter_down {S} (body : int → S → S) :
  ∀IntR _i i ,
  ∀IntR _k k ,
  ITER_DOWN i k
    (λ _j j s Q, wp (body _j s) Q)
    (λ s Q, wp (iter_down _k _i s body) Q).
Proof.
  intros. ITER. unfold iter_down.
  wp_if; autorewrite with nat.
  (* Case [k ≤ i]. *)
  { wp_ret. eauto. }
  (* Case [i < k]. *)
  { wp_op @wp_iter_down_aux s'. eauto. }
Qed.

Global Ltac wp_iter_down I :=
  wp_loop @wp_iter_down I.

(* -------------------------------------------------------------------------- *)

(* An exitable loop, counting down, using machine integers. *)

Section XIterDown.
Context {S A : Type}.
Implicit Types s : S.

(* The lower bound. *)
Variable _i : int.

(* The loop body: [body _j s continue break]. *)
Variable body : ∀ {W}, int → S → (S → W) → (S → A → W) → W.

(* The code. *)
Equations xiter_down_aux _j s : S * outcome A
by wf _j (rilt _i) :=
xiter_down_aux _j s with inspect (_j =? _i)%uint63 => {
| inspected true :=
    let continue s := (s, Continue) in
    let break s x := (s, Break x) in
    body _j s continue break
| inspected false :=
    let continue s := xiter_down_aux (_j - 1)%uint63 s in
    let break s x := (s, Break x) in
    body _j s continue break
}.
Next Obligation.
  eauto using safe_decrement_relative'.
Qed.

End XIterDown.

(* A specification of [xiter_down_aux]. *)

Lemma wp_xiter_down_aux {S A}
  (body : ∀ {W}, int → S → (S → W) → (S → A → W) → W) :
  ∀IntR _i i ,
  ∀IntR _j j ,
  i ≤ j →
  XITER_DOWN i (j + 1)
    (λ _ _j j s continue break Q, wp (body _j s continue break) Q)
    (λ s Q, wp (xiter_down_aux _i (@body) _j s) Q).
Proof.
  intros. XITER.
  funelim (xiter_down_aux _i (@body) _j s); cleanup; clear Heqcall;
  intros; isBool_magic; autorewrite with nat.
  (* Case [j = i]. *)
  { subst j. eapply Hbody; pack; tc; intros; wp_ret; eauto. }
  (* Case [j ≠ i]. *)
  { rename H into IH. eapply Hbody; pack; tc.
    + wp_op IH s'. assumption.
    + wp_ret. eauto. }
Qed.

Definition xiter_down {S A} _k _i (s : S)
  (body : ∀ {W}, int → S → (S → W) → (S → A → W) → W) :=
  if (_k ≤? _i)%uint63 then (s, Continue)
  else xiter_down_aux _i (@body) (_k - 1) s.

(* A specification of [xiter_down]. *)

Lemma wp_xiter_down {S A}
  (body : ∀ {W}, int → S → (S → W) → (S → A → W) → W) :
  ∀IntR _i i ,
  ∀IntR _k k ,
  XITER_DOWN i k
    (λ _ _j j s continue break Q, wp (body _j s continue break) Q)
    (λ s Q, wp (xiter_down _k _i s (@body)) Q).
Proof.
  intros. XITER. unfold xiter_down.
  wp_if; autorewrite with nat.
  (* Case [k ≤ i]. *)
  { wp_ret. eauto. }
  (* Case [i < k]. *)
  { wp_op @wp_xiter_down_aux s'. eauto. }
Qed.

Global Ltac wp_xiter_down I :=
  wp_loop @wp_xiter_down I.

(* -------------------------------------------------------------------------- *)

(* A simplified exitable loop with a state of type [unit]. *)

Section UXIterDown.
Context {A : Type}.

(* The lower bound. *)
Variable _i : int.

(* The loop body: [body _j continue break]. *)
Variable body : ∀ {W}, int → (unit → W) → (A → W) → W.

(* The code. *)
Equations uxiter_down_aux _j : outcome A
by wf _j (rilt _i) :=
uxiter_down_aux _j with inspect (_j =? _i)%uint63 => {
| inspected true :=
    let continue '() := Continue in
    let break x := Break x in
    body _j continue break
| inspected false :=
    let continue '() := uxiter_down_aux (_j - 1)%uint63 in
    let break x := Break x in
    body _j continue break
}.
Next Obligation.
  eauto using safe_decrement_relative'.
Qed.

End UXIterDown.

(* A specification of [uxiter_down_aux]. *)

Lemma wp_uxiter_down_aux {A}
  (body : ∀ {W}, int → (unit → W) → (A → W) → W) :
  ∀IntR _i i ,
  ∀IntR _j j ,
  i ≤ j →
  UXITER_DOWN i (j + 1)
    (λ _ _j j continue break Q, wp (body _j continue break) Q)
    (λ Q, wp (uxiter_down_aux _i (@body) _j) Q).
Proof.
  intros. UXITER.
  funelim (uxiter_down_aux _i (@body) _j); cleanup; clear Heqcall;
  intros; isBool_magic; autorewrite with nat.
  (* Case [j = i]. *)
  { subst j. eapply Hbody; pack; tc; intros; wp_ret; eauto. }
  (* Case [j ≠ i]. *)
  { rename H into IH. eapply Hbody; pack; tc.
    + wp_op (IH()) s'. eauto.
    + wp_ret. eauto. }
Qed.

Definition uxiter_down {A} _k _i
  (body : ∀ {W}, int → (unit → W) → (A → W) → W) :=
  if (_k ≤? _i)%uint63 then Continue
  else uxiter_down_aux _i (@body) (_k - 1).

(* A specification of [uxiter_down]. *)

Lemma wp_uxiter_down {A}
  (body : ∀ {W}, int → (unit → W) → (A → W) → W) :
  ∀IntR _i i ,
  ∀IntR _k k ,
  UXITER_DOWN i k
    (λ _ _j j continue break Q, wp (body _j continue break) Q)
    (λ Q, wp (uxiter_down _k _i (@body)) Q).
Proof.
  intros. UXITER. unfold uxiter_down.
  wp_if; autorewrite with nat.
  (* Case [k ≤ i]. *)
  { wp_ret. eauto. }
  (* Case [i < k]. *)
  { wp_op @wp_uxiter_down_aux s'. eauto. }
Qed.

Global Ltac wp_uxiter_down I :=
  wp_loop @wp_uxiter_down I.

(* -------------------------------------------------------------------------- *)

(* A loop, counting up from [i] to [k], using machine integers. *)

(* Our intervals are semi-open on the right end: [i] is included,
   [k] is excluded. *)

Section IterUp.
Context {S : Type}.
Implicit Types s : S.

(* We hoist the loop-invariant parameters out of the loop, because
   otherwise Equations produces ugly code where these parameters are
   carried around in a tuple, itself encoded using nested pairs. *)

Variable _k : int.
Variable body : int → S → S.

(* [iter_up_aux _i s] applies the loop body [body] to every machine integer
   from [_i], included, up to [_k], excluded. A state of type [S] is
   carried, whose initial value is [s]. *)

(* We use Equations to more easily define [iter_up_aux] by well-founded
   recursion over the loop counter [_i]. The somewhat strange [with]
   syntax is a way of expressing the test [_i <? _k]. The use of [inspect]
   and [inspected] is an idiosyncratic way of making the outcome of the
   test visible at the logical level in the branches. In the second
   branch, the fact that [_i <? _k] is false is needed in order to prove
   that [_i + 1] is less than [_i], a fact which itself is required by the
   termination argument. *)

Equations iter_up_aux _i s : S
by wf _i igt :=
iter_up_aux _i s with inspect (_i <? _k)%uint63 => {
| inspected true :=
    do s ← body _i s ;
    do s ← iter_up_aux (_i + 1)%uint63 s ;
    s ;
| inspected false :=
    s
}.
Next Obligation.
  eauto using safe_increment'.
Qed.

End IterUp.

(* A specification of [iter_up_aux], which also serves for [iter_up]. *)

Lemma wp_iter_up_aux {S} (body : int → S → S) :
  ∀IntR _i i ,
  ∀IntR _k k ,
  ITER_UP i k
    (λ _j j s Q, wp (body _j s) Q)
    (λ s Q, wp (iter_up_aux _k body _i s) Q).
Proof.
  intros. ITER.
  funelim (iter_up_aux _k body _i s); cleanup; clear Heqcall;
  isBool_magic; autorewrite with nat.
  (* Case [i < k]. *)
  { wp_op Hstep s'. wp_op H s''. wp_ret. eauto. }
  (* Case [¬ i < k]. *)
  { wp_ret. eauto. }
Qed.

(* A definition of [iter_up], with reordered parameters. *)

(* [iter_up _i _k s body] applies the loop body [body] to every machine
   integer from [_i], included, up to [_k], excluded. A state of type [S]
   is carried, whose initial value is [s]. *)

Definition iter_up {S} _i _k s (body : int → S → S) :=
  iter_up_aux _k body _i s.

Global Ltac wp_iter_up I :=
  unfold iter_up at 1;
  wp_loop @wp_iter_up_aux I.

(* -------------------------------------------------------------------------- *)

(* An exitable loop, counting up from [i] to [k]. The loop can be broken via
   an early exit: the loop body receives two continuations [continue] and
   [break] and must invoke either [continue s] or [break s x]. *)

Section XiterUp.
Context {S A : Type}.
Implicit Types s : S.

(* The upper bound. *)
Variable _k : int.

(* The loop body: [body _i s continue break]. *)
Variable body : ∀ {W}, int → S → (S → W) → (S → A → W) → W.

(* The code. *)
Equations xiter_up_aux _i s : S * outcome A
by wf _i igt :=
xiter_up_aux _i s
with inspect (_i <? _k)%uint63 => {
| inspected true :=
    let continue s := xiter_up_aux (_i + 1)%uint63 s in
    let break s x := (s, Break x) in
    body _i s continue break
| inspected false :=
    (s, Continue)
}.
Next Obligation.
  eauto using safe_increment'.
Qed.

End XiterUp.

(* A specification of [xiter_up_aux]. *)

Lemma wp_xiter_up_aux {S A}
  (body : ∀ {W}, int → S → (S → W) → (S → A → W) → W) :
  ∀IntR _i i ,
  ∀IntR _k k ,
  XITER_UP i k
    (λ _ _j j s continue break Q, wp (body _j s continue break) Q)
    (λ s Q, wp (xiter_up_aux _k (@body) _i s) Q).
Proof.
  (* The spec is quite complex, but the proof is very simple. *)
  intros. XITER.
  funelim (xiter_up_aux _k (@body) _i s); cleanup; clear Heqcall; intros;
  isBool_magic; autorewrite with nat.
  (* Case [a < b]. *)
  { eapply Hbody; pack; tc; intros.
    (* Normal continuation. *)
    + wp_op H sout. assumption.
    (* Exit continuation. *)
    + wp_ret. eauto. }
  (* Case [b ≤ a]. *)
  { wp_ret. eauto. }
Qed.

(* [xiter_up] with reordered parameters. *)

Definition xiter_up {S A} _i _k s
  (body : ∀ {W}, int → S → (S → W) → (S → A → W) → W) :=
  xiter_up_aux _k (@body) _i s.

(* The specification of [xiter_up]. *)

Definition wp_xiter_up :=
  @wp_xiter_up_aux.

(* -------------------------------------------------------------------------- *)

(* A simplified exitable loop with a state of type [unit]. *)

Section UXIterUp.
Context {A : Type}.

(* The upper bound. *)
Variable _k : int.

(* The loop body: [body _i continue break]. *)
Variable body : ∀ {W}, int → (unit → W) → (A → W) → W.

(* The code. *)
Equations uxiter_up_aux _i : outcome A
by wf _i igt :=
uxiter_up_aux _i
with inspect (_i <? _k)%uint63 => {
| inspected true :=
    let continue '() := uxiter_up_aux (_i + 1)%uint63 in
    let break x := Break x in
    body _i continue break
| inspected false :=
    Continue
}.
Next Obligation.
  eauto using safe_increment'.
Qed.

End UXIterUp.

(* A specification of [uxiter_up_aux]. *)

Lemma wp_uxiter_up_aux {A} (body : ∀ {W}, int → (unit → W) → (A → W) → W) :
  ∀IntR _i i ,
  ∀IntR _k k ,
  UXITER_UP i k
    (λ _ _j j continue break Q, wp (body _j continue break) Q)
    (λ Q, wp (uxiter_up_aux _k (@body) _i) Q).
Proof.
  (* The spec is quite complex, but the proof is very simple. *)
  intros. UXITER.
  funelim (uxiter_up_aux _k (@body) _i); cleanup; clear Heqcall; intros;
  isBool_magic; autorewrite with nat.
  (* Case [a < b]. *)
  { eapply Hbody; pack; tc; intros.
    (* Normal continuation. *)
    + wp_op (H()) out. eauto.
    (* Exit continuation. *)
    + wp_ret. eauto. }
  (* Case [b ≤ a]. *)
  { wp_ret. eauto. }
Qed.

(* [uxiter_up] with reordered parameters. *)

Definition uxiter_up {A} _i _k
  (body : ∀ {W}, int → (unit → W) → (A → W) → W) :=
  uxiter_up_aux _k (@body) _i.

Global Ltac wp_uxiter_up I :=
  unfold uxiter_up at 1;
  wp_loop @wp_uxiter_up_aux I.
