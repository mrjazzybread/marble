From stdpp Require Import numbers well_founded.
From Stdlib Require Import Uint63.
(* TODO why is [of_to_Z] an axiom? *)
From Stdlib Require Import Wellfounded.Wellfounded.
From Equations Require Import Equations.
From Equations.Prop Require Import Logic. (* [inspect] *)
Notation inspected x := (exist _ x _).
From array Require Import tactics bool wp.

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
Implicit Types _i : int.
Implicit Types  i : nat.
Implicit Types  z : Z.

(* -------------------------------------------------------------------------- *)

(* Arithmetic lemmas of general interest. *)

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

Definition isInt (_i : int) (i : nat) :=
  _i = of_nat i.

Ltac introIsInt :=
  unfold isInt.

Ltac destructIsInt :=
  match goal with h: isInt ?_i _ |- _ =>
    unfold isInt in h; try subst _i
  end.

(* [liftIsIntAndClear] looks for a hypothesis [isInt _i i],
   replaces [_i] with [of_nat i] in the goal, and clears
   [_i] as well the hypothesis [isInt _i i]. *)

Ltac liftIsIntAndClear :=
  match goal with
  h: isInt ?_i ?i |- context[?_i] =>
    rewrite h; clear _i h
  end.

Lemma introIsInt _i i :
  _i = of_nat i →
  isInt _i i.
Proof.
  intros. introIsInt. eauto.
Qed.

Lemma introIsInt' _i :
  isInt _i (to_nat _i).
Proof.
  introIsInt. int. eauto.
Qed.

Lemma introIsInt0 :
  isInt 0 0.
Proof.
  eapply introIsInt'.
Qed.

Lemma introIsInt1 :
  isInt 1 1.
Proof.
  eapply introIsInt'.
Qed.

Global Hint Resolve
  introIsInt
  introIsInt0
  introIsInt1
: int.

Lemma isInt_inj_1 _i1 _i2 i :
  isInt _i1 i →
  isInt _i2 i →
  _i1 = _i2.
Proof.
  unfold isInt. congruence.
Qed.

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
  (j ≤ i)%nat →
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

Definition representable_def (i : nat) :=
  (i < wBN)%nat.

  (* Use [seal] to prevent [eauto] from looking into this definition.
     Otherwise, it might try to normalize [Z.to_nat wB], which does
     not terminate. *)
  Local Definition representable_aux : seal (@representable_def). Proof. by eexists. Qed.
  Definition representable := representable_aux.(unseal).
  Local Definition representable_unseal : @representable = @representable_def := representable_aux.(seal_eq).

Lemma representable_iff_nat i :
  representable i ↔ (i < wBN)%nat.
Proof.
  rewrite representable_unseal. unfold representable_def. tauto.
Qed.

Lemma representable_iff_Z i :
  representable i ↔ unsigned (Z.of_nat i).
Proof.
  rewrite representable_iff_nat. unfold wBN. lia.
Qed.

(* This tactic should work for every sufficiently small constant. *)
Ltac representable :=
  rewrite representable_iff_Z; split; [lia | constructor].

Goal representable 0.
Proof. representable. Qed.

Goal representable 1.
Proof. representable. Qed.

Hint Extern 1 (representable _) => representable : representable.

Lemma representable_down_closed i j :
  representable j →
  (i ≤ j)%nat →
  representable i.
Proof.
  rewrite representable_unseal. unfold representable_def. lia.
Qed.

Hint Resolve representable_down_closed : representable.

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
  using (eauto with representable)
: int.

Definition proj (i : nat) : nat :=
  (i `mod` wBN)%nat.

(* The lemmas that relate [Nat.modulo] and [Z.modulo] are
   [Nat2Z.inj_mod] and [Z2Nat.inj_mod]. *)

Lemma representable_iff_proj i :
  representable i ↔
  proj i = i.
Proof.
  rewrite representable_unseal. unfold representable_def, proj, wBN.
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
  unfold isInt. rewrite <- to_nat_of_nat. split.
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

(* Beyond this point, [isInt] is opaque. *)

(* This is required, e.g., to avoid expansion of [isInt] by [funelim]. *)

Local Opaque isInt.

(* At the moment, array.v still needs [isInt] to be transparent. TODO *)

(* TODO dirty *)
Global Ltac isBool ::=
  eauto with int representable typeclass_instances lia.

(* -------------------------------------------------------------------------- *)

(* Well-foundedness of the orderings on machine integers. *)

(* [ilt] is the ordering [<] on machine integers. *)

(* [igt] is the ordering [>] on machine integers. *)

(* Both orderings are well-founded. *)

Definition ilt _i _j :=
  φ _i < φ _j.

(* TODO unused *)
Lemma ltb_spec' _i _j :
  ltb _i _j = true ↔ ilt _i _j.
Proof.
  unfold ilt. rewrite ltb_spec. tauto.
Qed.

(* TODO unused *)
Lemma ilt_alt_def _i _j :
  ilt _i _j ↔ 0 ≤ φ _i < φ _j.
Proof.
  unfold ilt. split; eauto with lia.
Qed.

Lemma ilt_wf : well_founded ilt.
Proof.
  eapply wf_incl; [| eapply Z.lt_wf_projected with (z := 0) (f := φ) ].
  intros _i _j. unfold ilt. eauto with lia.
Qed.

Global Instance Wf_ilt : WellFounded ilt :=
  wf_guard 32 ilt_wf.
  (* The use of [wf_guard] is meant to allow computation inside Rocq
     in spite of the opaque well-foundedness proof [ilt_wf]. *)

(* Safely decrementing an integer, without integer underflow. *)

Lemma safe_decrement _i :
  0%Z ≠ φ _i →
  (φ (_i - 1) < φ _i)%Z.
Proof.
  intros.
  assert (unsigned (φ _i)) by eauto with lia.
  rewrite sub_spec. change (φ 1) with 1%Z.
  rewrite Z.mod_small by lia.
  lia.
Qed.

Lemma safe_decrement' _i :
  (_i =? 0)%uint63 = false →
  ilt (_i - 1) _i.
Proof.
  rewrite bool_neg, eqb_spec. unfold ilt. intros.
  assert (0 ≠ φ _i)%Z. { change 0%Z with (φ 0). eauto with lia. }
  eauto using safe_decrement.
Qed.

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

(* Safely incrementing an integer, without integer overflow. *)

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

(* -------------------------------------------------------------------------- *)

(* Basic facts about the natural integers. *)

Open Scope nat_scope.

Lemma minus_1_plus_1 i :
  0 < i →
  i - 1 + 1 = i.
Proof.
  lia.
Qed.

Global Hint Rewrite
  minus_1_plus_1
  using lia
: nat.

(* -------------------------------------------------------------------------- *)

(* A loop, counting down to zero, using machine integers. *)

Section Down.
Context {S : Type}.
Implicit Types s : S.

Variable f : int → S → S.

(* [down_aux _i s] applies the loop body [f] to every machine integer from
   [_i], included, down to zero, included. A state of type [S] is carried,
   whose initial value is [s]. *)

(* We are careful to test the condition [_i =? 0] before decrementing [_i].
   Because we use unsigned integers, we cannot first decrement and then test
   the condition [_i <? 0]. *)

(* We use Equations to more easily define [down_aux] by well-founded recursion
   over the loop counter [_i]. The somewhat strange [with] syntax is a way of
   expressing the test [_i =? 0]. The use of [inspect] and [inspected] is an
   idiosyncratic way of making the outcome of the test visible at the logical
   level in the branches. In the second branch, the fact that [_i =? 0] is
   false is needed in order to prove that [_i-1] is less than [_i], a fact
   which itself is required by the termination argument. *)

Equations down_aux _i s : S
by wf _i ilt :=
down_aux _i s with inspect (_i =? 0)%uint63 => {
| inspected true :=
    do s ← f _i s ;
    s ;
| inspected false :=
    do s ← f _i s ;
    down_aux (_i-1)%uint63 s
}.
Next Obligation.
  eauto using safe_decrement'.
Qed.

(* For the record, here is an alternative direct definition of [down_aux],
   which does not use Equations. At extraction time, this definition produces
   slightly better-looking OCaml code. However, reasoning about it is more
   difficult; we lose the fixed point equation and the induction principle
   produced by Equations, which are used via the tactic [funelim]. *)
Goal int → S → S.
Proof.
  eapply (Fix ilt_wf (λ _, S → S)). intros _i self s.
  destruct (_i =? 0)%uint63 eqn:Heq.
  + refine (
      do s ← f _i s ;
      s
    ).
  + refine (
      do s ← f _i s ;
      self (_i-1)%uint63 _ s
    ).
    eauto using safe_decrement'.
Defined.

(* A specification of [down_aux]. *)

(* For comments, see the specification of [down], further down. *)

Lemma wp_down_aux (inv : nat → S → Prop) (Q : S → Prop) :
  (∀ _i i s ,
    isInt _i i →
    representable i →
    inv (i + 1) s →
    wp (f _i s) (λ s, inv i s)
  ) →
  (∀ s, inv 0 s → Q s) →
  ∀ _i i s ,
  isInt _i i →
  representable i →
  inv (i + 1) s →
  wp (down_aux _i s) Q.
Proof.
  intros Hstep Hfinish.
  intros _i i s.
  funelim (down_aux _i s); cleanup; clear Heqcall; intros ? ? Hinit;
  isBool_magic.
  (* Case [i = 0]. *)
  { subst i.
    eapply wp_bind; [ eapply Hstep; eauto | simpl; intros s' ? ].
    wp_ret. eauto. }
  (* Case [i ≠ 0]. *)
  { rename H into IH.
    eapply wp_bind; [ eapply Hstep; eauto | simpl; intros s' ?].
    eapply IH; eauto with int representable lia; autorewrite with nat.
    eauto. }
Qed.

End Down.

(* [down _i s f] applies the loop body [f] to every machine integer from [_i],
   excluded, down to zero, included. A state of type [S] is carried, whose
   initial value is [s]. *)

Definition down {S} _i (s : S) f :=
  if (_i =? 0)%uint63 then s
  else down_aux f (_i-1) s.

(* A specification of [down]. *)

(* The user is allowed to choose a loop invariant [inv i s], where
   [i] is the current loop index and [s] is the current state. The
   assertion [inv i s] means that the loop has run down to index [i]
   included, so the next iteration will concern the index [i-1]. *)

Lemma wp_down {S} (inv : nat → S → Prop) (Q : S → Prop) _n n s f :
  (* If the invariant holds of the start index [n] and start state [s], *)
  isInt _n n →
  representable n →
  inv n s →
  (* If [s ← f _i s] transforms the invariant [inv (i+1) s] to [inv i s], *)
  (∀ _i i s ,
    isInt _i i →
    representable i →
    i < n →
    inv (i + 1) s →
    wp (f _i s) (λ s, inv i s)
  ) →
  (* Then, once the loop ends, the invariant holds of the index [0]
     and final state [s]. *)
  (∀ s, inv 0 s → Q s) →
  wp (down _n s f) Q.
Proof.
  intros ? ? Hinit Hstep Hfinish.
  unfold down.
  destruct (_n =? 0)%uint63 eqn:?; isBool_magic.
  (* Case [_n = 0]. *)
  { subst n. wp_ret. eauto. }
  (* Case [_n ≠ 0]. *)
  { (* We strengthen the loop invariant with [i ≤ n]. *)
    eapply wp_down_aux with (inv := λ i s, i ≤ n ∧ inv i s);
      intuition eauto with int lia;
      autorewrite with nat;
      eauto using wp_conseq with representable lia. }
Qed.

(* [down _n s @@ λ _i s, ...] is a convenient way of writing a loop. *)

Global Notation "f '@@' x" := (f x) (at level 61, only parsing).

(* -------------------------------------------------------------------------- *)

(* A loop, counting up from [a] to [b], using machine integers. *)

(* Our intervals are semi-open on the right end: [a] is included,
   [b] is excluded. *)

Section UpAux.
Context {S : Type}.
Implicit Types _a : int.
Implicit Types s : S.

(* We hoist the loop-invariant parameters out of the loop, because
   otherwise Equations produces ugly code where these parameters are
   carried around in a tuple, itself encoded using nested pairs. *)

Variable _b : int.
Variable f : int → S → S.

(* [up_aux _a s] applies the loop body [f] to every machine integer from
   [_a], included, up to [_b], excluded. A state of type [S] is carried,
   whose initial value is [s]. *)

(* We use Equations to more easily define [up_aux] by well-founded
   recursion over the loop counter [_a]. The somewhat strange [with]
   syntax is a way of expressing the test [_a <? _b]. The use of [inspect]
   and [inspected] is an idiosyncratic way of making the outcome of the
   test visible at the logical level in the branches. In the second
   branch, the fact that [_a <? _b] is false is needed in order to prove
   that [_a+1] is less than [_a], a fact which itself is required by the
   termination argument. *)

Equations up_aux _a s : S
by wf _a igt :=
up_aux _a s with inspect (_a <? _b)%uint63 => {
| inspected true :=
    do s ← f _a s ;
    do s ← up_aux (_a+1)%uint63 s ;
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
Implicit Types _a _b : int.
Implicit Types s : S.
Implicit Types f : int → S → S.

(* A specification of [up_aux]. *)

(* The user is allowed to choose a loop invariant [inv a s], where
   [a] is the current loop index and [s] is the current state. The
   assertion [inv a s] means that the loop has run up to index [a]
   excluded, so the next iteration will concern the index [a]. *)

Lemma wp_up_aux f (inv : nat → S → Prop) (Q : S → Prop) :
  ∀ _a a _b b s ,
  isInt _a a →
  representable a →
  isInt _b b →
  representable b →
  (* If the invariant holds of the start index [a] and start state [s], *)
  inv a s →
  (* If [s ← f _i s] transforms the invariant [inv i s] to [inv (i+1) s], *)
  (∀ _i i s ,
    isInt _i i →
    representable i →
    a ≤ i < b →
    inv i s →
    wp (f _i s) (λ s, inv (i + 1) s)
  ) →
  (* Then, once the loop ends, the invariant holds of the index [a]
     or [b], whichever is greater, and of the final state [s]. *)
  (∀ s, inv (a `max` b) s → Q s) →
  wp (up_aux _b f _a s) Q.
Proof.
  do 9 intro. intros Hinit Hstep Hfinish.
  funelim (up_aux _b f _a s); cleanup; clear Heqcall; isBool_magic.
  (* Case [a < b]. *)
  { assert (fact: a `max` b = (a + 1) `max` b) by lia.
    rewrite fact in Hfinish.
    eapply wp_bind; [ eapply Hstep; eauto | simpl; intros s' ? ].
    eauto with int representable lia. }
  (* Case [¬ a < b]. *)
  { assert (fact: a `max` b = a) by lia.
    rewrite fact in Hfinish.
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
  (* TODO [funelim] creates an induction hypothesis that contains
          spurious parameters of type [S * option A] and [option A]. *)
  assert (dummy: option A). { exact continue. }
  (* Case [a < b]. *)
  { eapply wp_bind; [ eapply Hstep; eauto | simpl; intros [s' [|]] ? ].
    + wp_ret. eauto with lia.
    + eapply H; intuition eauto with int representable lia. }
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
