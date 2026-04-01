From stdpp Require Import numbers well_founded.
From Stdlib Require Export ZifyNat.
  (* [ZifyNat] magically makes [lia] more powerful,
     including on goals that involve division in Z *)
From Stdlib Require Import Uint63 ZifyUint63.
  (* [ZifyUint63] magically makes [lia] more powerful *)
From Stdlib Require Import Wellfounded.Wellfounded.
From listz Require Import listz.
From marble Require Import tactics bool wp wp_tactics iteration.
From marble Require Import equations.

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
Implicit Types  i : Z.
Implicit Types  z : Z.

(* -------------------------------------------------------------------------- *)

(* [unsigned z] means that [z] lies in the interval of the unsigned
   machine integers. *)

(* In our comments, we use the word "representable" as a synonym
   for [unsigned]. *)

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
Proof. lia. Qed.
(* This is a reformulation of [is_int]. *)

Goal ∀ z,
  φ (π z) = z `mod` wB.
Proof. apply of_Z_spec. Qed. (* [lia] can also prove this *)

Global Hint Rewrite
  of_to_Z
  to_of_Z                    (* conflicts with [of_Z_spec] *)
  using (eauto with lia)
: int.

(* The rewrite rules in the database [int] can be useful, but we use them
   occasionally. We do not expect an end user to need them. *)

Global Tactic Notation "int" :=
  autorewrite with int.

Global Tactic Notation "int" "in" hyp(h) :=
  autorewrite with int in h.

Global Tactic Notation "int" "in" "*" :=
  autorewrite with int in *.

(* φ is injective. *)

Goal ∀ _i1 _i2, φ _i1 = φ _i2 → _i1 = _i2.
Proof. eapply to_Z_inj. Qed.

Lemma to_Z_inj' _i1 _i2 :
  _i1 ≠ _i2 →
  φ _i1 ≠ φ _i2.
Proof. lia. Qed.

(* The image of φ is the interval of the unsigned machine integers. *)

Lemma to_Z_ge_0 _i :
  0 ≤ φ _i.
Proof. lia. Qed.

Lemma to_Z_lt_wB _i :
  φ _i < wB.
Proof. lia. Qed.

(* π, restricted to the interval of the unsigned machine integers,
   is injective. *)

Lemma of_Z_inj z1 z2 :
  unsigned z1 →
  unsigned z2 →
  π z1 = π z2 →
  z1 = z2.
Proof. lia. Qed.

Lemma of_Z_inj' z1 z2 :
  unsigned z1 →
  unsigned z2 →
  z1 ≠ z2 →
  π z1 ≠ π z2.
Proof. lia. Qed.

(* -------------------------------------------------------------------------- *)

(* Addition in Z commutes with projection. *)

Lemma add_spec' z1 z2 :
  (π z1 + π z2)%uint63 = π (z1 + z2).
Proof. lia. Qed.

(* Subtraction in Z commutes with projection. *)

Lemma sub_spec' z1 z2 :
  (π z1 - π z2)%uint63 = π (z1 - z2).
Proof. lia. Qed.

(* Multiplication in Z commutes with projection. *)

Lemma mul_spec' z1 z2 :
  (π z1 * π z2)%uint63 = π (z1 * z2).
Proof. lia. Qed.

(* Division in Z commutes with projection. *)

Lemma div_spec' z1 z2 :
  unsigned z1 →
  unsigned z2 →
  (π z1 / π z2)%uint63 = π (z1 `div` z2).
Proof.
  intros.
  replace z1 with (φ (π z1)) at 2 by (int; lia).
  replace z2 with (φ (π z2)) at 2 by (int; lia).
  rewrite <- div_spec. int. eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Some properties of machine integer arithmetic. *)

Lemma add_sub_conv _i _a _b :
  (_i - _a - _b = _i - (_a + _b))%uint63.
Proof. lia. Qed.

Lemma add_sub_comm _i _a _b :
  (_i - _a - _b = _i - _b - _a)%uint63.
Proof. lia. Qed.

Lemma add_sub_exch _i _j _k :
  (_k + (_j - _i) = _j + (_k - _i))%uint63.
Proof. lia. Qed.

(* -------------------------------------------------------------------------- *)

(* A relational view of the connection between [int] and [Z]. *)

(* It is debatable whether the logical model of an unsigned machine integer
   should be a natural number of type [nat] or an integer of type [Z]. In
   the beginning I have worked with [nat], but I have now come to think that
   working with [Z] is easier. The integers form a ring; therefore they
   support more powerful simplification tactics, such as [ring_simplify].
   Furthermore, using [Z] as a model implies that subtraction is better
   behaved: subtraction of machine integers corresponds to subtraction of
   ideal integers, without a side condition. This allows verifying programs
   that temporarily use negative machine integers (with wraparound).
   [array.blit] offers an example. The main downside of working with [Z], as
   opposed to [nat], is that we get many obligations to prove that an
   integer is nonnegative. *)

Class isInt (_i : int) (i : Z) :=
  build_isInt : _i = of_Z i.

Global Hint Mode isInt ! - : typeclass_instances.
  (* Instantiate the first parameter only if its head is already known,
     that is, not a metavariable. We often encounter goals of the form
     [isInt (_i + _j) ?k], so we cannot require the second parameter to
     also be already known. *)

Lemma isInt_def _i i :
  isInt _i i ↔ _i = of_Z i.
Proof. tauto. Qed.

(* It is worth keeping this fact in mind. *)

Lemma partial_bijection _i i :
  to_Z _i = i  ↔  _i = of_Z i ∧ unsigned i.
Proof. lia. Qed.

Lemma partial_bijection' _i i :
  to_Z _i = i  ↔   isInt _i i ∧ unsigned i.
Proof. unfold isInt. apply partial_bijection. Qed.

(* Tactics. *)

Ltac introIsInt :=
  rewrite isInt_def.

Ltac destructIsInt :=
  repeat match goal with h: isInt ?_i _ |- _ =>
    rewrite isInt_def in h; try subst _i
  end.

Ltac destructAndKeepIsInt :=
  match goal with h: isInt ?_i _ |- _ =>
    generalize h;
    rewrite isInt_def in h; try subst _i;
    intro h
  end.

Ltac destructIsIntU :=
  repeat match goal with h: isInt ?_i ?i, h': unsigned ?i |- _ =>
    assert (to_Z _i = i) by (rewrite partial_bijection'; eauto);
    clear h h'; subst i
  end.

(* [isInt], restricted to the unsigned integers, is injective
   in its first parameter. *)

Lemma isInt_inj_1 _i1 _i2 i :
  isInt _i1 i →
  isInt _i2 i →
  _i1 = _i2.
Proof.
  unfold isInt. congruence.
Qed.

(* [isInt], restricted to the unsigned integers, is injective
   in its second parameter. *)

Lemma isInt_inj_2 _i i _j j :
  isInt _i i →
  isInt _j j →
  _i = _j →
  unsigned i →
  unsigned j →
  i = j.
Proof.
  unfold isInt. lia.
Qed.

(* Making the following lemma an Instance would be very useful when we
   have a goal such as [isInt 12 12] where both parameters are known.
   However, when we have a goal such as [isInt (_i + 12) ?k],
   [introIsInt] is a bad choice; we want [add_compat] to be used in
   this case. Unfortunately, assigning a high cost to [introIsInt]
   cannot help: if [a] is the cost of [add_compat] and [c] is the cost
   of [introIsInt], we would need to have [a + c ≤ c], which is
   impossible. *)

Lemma introIsInt _i :
  isInt _i (to_Z _i).
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

Global Instance isInt2 :
  isInt 2 2.
Proof.
  eauto using introIsInt.
Qed.

Global Instance isInt3 :
  isInt 3 3.
Proof.
  eauto using introIsInt.
Qed.

(* Addition. *)

Global Instance isInt_add _i i _j j :
  isInt _i i →
  isInt _j j →
  isInt (_i+_j) (i+j).
Proof.
  intros. introIsInt. destructIsInt. lia.
Qed.

(* Subtraction. *)

(* Here, the side condition [j ≤ i] is NOT needed, because we work
   with integers in [Z] at the logical level. *)

Global Instance isInt_sub _i i _j j :
  isInt _i i →
  isInt _j j →
  isInt (_i-_j) (i-j).
Proof.
  intros. introIsInt. destructIsInt. lia.
Qed.

(* Multiplication. *)

Global Instance isInt_mul _i i _j j :
  isInt _i i →
  isInt _j j →
  isInt (_i*_j) (i*j).
Proof.
  intros. introIsInt. destructIsInt. lia.
Qed.

(* Tests. *)

Goal unsigned 42.
Proof. lia. Qed.

Goal unsigned (wB - 1).
Proof. lia. Qed.

Goal ∀ i,
  unsigned i →
  i ≠ 0 →
  unsigned (i - 1).
Proof. tc3. Qed.

Goal (* unsigned_down_closed *) ∀ i j,
  unsigned j → 0 ≤ i ≤ j → unsigned i.
Proof. tc3. Qed.

Goal ∀ _i i _j j ,
  isInt _i i →
  isInt _j j →
  isInt (_i+(_j-1)) (i+(j-1)).
Proof. tc3. Qed.

(* Whereas [π] has type [Z → int],
   the projection [proj] has type [Z → Z]. *)

Notation proj i :=
  (i `mod` wB)
  (only parsing).

(* -------------------------------------------------------------------------- *)

(* This helps write specifications. *)

Notation "'∀Int' _i i , P" :=
  ( ∀ _i i ,
    isInt _i i →
    P
  ) (at level 200, _i name, i name).

Notation "'∀IntU' _i i , P" :=
  ( ∀ _i i ,
    isInt _i i →
    unsigned i →
    P
  ) (at level 200, _i name, i name).

(* -------------------------------------------------------------------------- *)

(* Equality. *)

(* In the absence of hypotheses about the integers [i] and [j], an
   equality test on the machine integers [_i] and [_j] decides the
   condition [proj i = proj j]. *)

Lemma isBool_eqb_proj :
  ∀Int _i i ,
  ∀Int _j j ,
  isBool1 (_i =? _j)%uint63 (proj i = proj j).
Proof.
  intros. eapply isBool1_intro. rewrite eqb_spec.
  destructIsInt. lia.
Qed.

(* If the integers [i] and [j] are representable then an equality test on
   the machine integers [_i] and [_j] decides the condition [i = j]. *)

Global Instance isBool_eqb :
  ∀IntU _i i ,
  ∀IntU _j j ,
  isBool1 (_i =? _j)%uint63 (i = j).
Proof.
  intros. eapply isBool1_intro. rewrite eqb_spec.
  destructIsInt. lia.
Qed.

(* -------------------------------------------------------------------------- *)

(* Comparison. *)

(* In the absence of hypotheses about the integers [i] and [j],
   the test [_i <?_j] decides the condition [proj i < proj j]. *)

Lemma isBool_ltb_proj :
  ∀Int _i i ,
  ∀Int _j j ,
  isBool1 (_i <? _j)%uint63 (proj i < proj j).
Proof.
  intros. eapply isBool1_intro. rewrite ltb_spec.
  destructIsInt. lia.
Qed.

(* If the integers [i] and [j] are representable then
   the test [_i <?_j] decides the condition [i < j]. *)

Global Instance isBool_ltb :
  ∀IntU _i i ,
  ∀IntU _j j ,
  isBool1 (_i <? _j)%uint63 (i < j).
Proof.
  intros. eapply isBool1_intro. rewrite ltb_spec.
  destructIsInt. lia.
Qed.

(* In the absence of hypotheses about the integers [i] and [j],
   the test [_i ≤?_j] decides the condition [proj i ≤ proj j]. *)

Lemma isBool_leb_proj :
  ∀Int _i i ,
  ∀Int _j j ,
  isBool1 (_i ≤? _j)%uint63 (proj i ≤ proj j).
Proof.
  intros. eapply isBool1_intro. rewrite leb_spec.
  destructIsInt. lia.
Qed.

(* If the integers [i] and [j] are representable then
   the test [_i ≤?_j] decides the condition [i ≤ j]. *)

Global Instance isBool_leb :
  ∀IntU _i i ,
  ∀IntU _j j ,
  isBool1 (_i ≤? _j)%uint63 (i ≤ j).
Proof.
  intros. eapply isBool1_intro. rewrite leb_spec.
  destructIsInt. lia.
Qed.

(* -------------------------------------------------------------------------- *)

(* The operations [_min] and [_max] on machine integers. *)

Definition _min _m _n : int :=
  if (_m ≤? _n)%uint63 then _m else _n.

Definition _max _m _n : int :=
  if (_m ≤? _n)%uint63 then _n else _m.

Global Instance isInt_min :
  ∀IntU _m m ,
  ∀IntU _n n ,
  isInt (_min _m _n) (m `min` n).
Proof.
  intros. unfold _min.
  destruct (_m ≤? _n)%uint63 eqn:Heq; isBool_magic; z; eauto.
Qed.

Global Instance isInt_max :
  ∀IntU _m m ,
  ∀IntU _n n ,
  isInt (_max _m _n) (m `max` n).
Proof.
  intros. unfold _max.
  destruct (_m ≤? _n)%uint63 eqn:Heq; isBool_magic; z; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Division of machine integers. *)

(* In the integers, [i * j] is at least [i]. *)

(* Unused *) Lemma mul_increasing i j :
  (0 ≤ i → 0 < j → i ≤ j * i).
Proof. nia. Qed.

(* In the integers, [i / j] is at most [i]. *)

(* Unused *) Lemma div_decreasing i j :
  (0 ≤ i → 0 < j → i `div` j ≤ i).
Proof. nia. Qed.

(* If [i] and [j] are representable, then so is [i / j]. *)

(* Unused *) Local Lemma unsigned_div i j :
  unsigned i →
  unsigned j →
  unsigned (i / j).
Proof.
  lia. (* [ZifyNat] is useful here *)
Qed.

(* Division of representable integers works. *)

(* This lemma is in fact true also when [j] is zero, because (in Rocq)
   division by zero yields zero. Nevertheless we prefer to keep the side
   condition [j ≠ 0], as this will force the user to prove that they do
   not divide by zero. *)

Global Instance isInt_div :
  ∀IntU _i i ,
  ∀IntU _j j ,
  j ≠ 0 →
  isInt (_i/_j) (i/j).
Proof.
  intros. destructIsInt. introIsInt. eauto using div_spec'.
Qed.

(* Beyond this point, [isInt] is opaque. *)

(* This is required, e.g., to avoid expansion of [isInt] by [funelim]. *)

Global Opaque isInt.

(* -------------------------------------------------------------------------- *)

(* Well-foundedness of the orderings on machine integers. *)

(* [ilt] is the ordering [<] on machine integers. *)

(* [igt] is the ordering [>] on machine integers. *)

(* [rilt _a] is the ordering [<] on machine integers, relative to the
   integer [_a]. In this ordering, [_a] is the least element, and the
   remaining machine integers are ordered above it, in a cyclic manner.
   This ordering lets us prove that a loop that counts down towards [_a]
   must end, without assuming [_a ≤ i]. There, underflow is helpful! *)

(* [rigt _a] is the ordering [>] on machine integers, relative to the
   integer [_a]. *)

(* All four orderings are well-founded. *)

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

Definition rigt _a _i _j :=
  igt (_i - _a) (_j - _a).

Lemma rigt_wf _a : well_founded (rigt _a).
Proof.
  eapply wf_incl; [| eapply Z.lt_wf_projected
                     with (z := 0) (f := λ _i, wB - φ (_i - _a)) ].
  intros _i _j. unfold rigt, igt. lia.
Qed.

Global Instance Wf_rigt _a : WellFounded (rigt _a) :=
  wf_guard 32 (rigt_wf _a).

(* -------------------------------------------------------------------------- *)

(* This hint allows [eauto with lia] to kill the proof obligations
   related to these orderings. After the definition of the ordering
   is unfolded, [lia] just solves the underlying goal. *)

Global Hint Unfold ilt igt rilt rigt : lia.

(* The following results are unused. I keep them for the record; they
   are just illustrations of the power of [eauto with lia]. *)

(* By taking advantage of the above well-founded orderings, we are able to
   prove that a loop, counting up or counting down, must terminate. *)

(* Because we use semi-open intervals, which are closed at the bottom end
   and open at the top end, the code and the termination argument are
   asymmetric. When counting down, we use an equality test [_i =? _a].
   When counting up, we use a strict ordering test [_i <? _n]. *)

(* Safely incrementing a machine integer, without integer overflow. *)

Local Lemma safe_increment _i _j :
  (_i <? _j)%uint63 = true → igt (_i + 1) _i.
Proof.
  (* φ _i < φ _j → φ _i < φ (_i + 1) *)
  eauto with lia.
Qed.

(* Safely decrementing a machine integer, without integer underflow. *)

(* The following lemma is correct but inconvenient, as it requires
   [φ _a ≤ φ _i], which should not be needed, because (thanks to
   underflow!) termination is guaranteed even without it. We keep
   this lemma for the record, but it is unused. *)

Local Lemma safe_decrement _i _a :
  (_i =? _a)%uint63 = false →
  φ _a ≤ φ _i →
  ilt (_i - 1) _i.
Proof.
  (* _i ≠ _a → φ _a ≤ φ _i → φ (_i - 1) < φ _i *)
  eauto with lia.
Qed.

(* The following lemma removes the hypothesis [φ _a ≤ φ _i],
   but it is specialized to the case where [_a] is 0.
   It is also unused. *)

Local Lemma safe_decrement_absolute _i :
  (_i =? 0)%uint63 = false →
  ilt (_i - 1) _i.
Proof.
  (* _i ≠ 0%uint63 → φ (_i - 1) < φ _i *)
  eauto with lia.
Qed.

(* The following lemma removes the hypothesis [φ _a ≤ φ _i] and accepts
   an arbitrary choice of [_a]. The relative ordering [rilt _a] is used
   instead of the absolute ordering [ilt]. *)

Local Lemma safe_decrement_relative _i _a :
  (_i =? _a)%uint63 = false →
  rilt _a (_i - 1) _i.
Proof.
  (* _i ≠ _a → φ (_i - 1 - _a) < φ (_i - _a) *)
  eauto with lia.
Qed.

(* -------------------------------------------------------------------------- *)

(* TODO I would like to split this file here *)

Local Obligation Tactic :=
  simpl in *;
  Tactics.program_simplify;
  CoreTactics.equations_simpl;
  try Tactics.program_solve_wf;
  eauto 3 with lia.

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

(* For the record, here is a direct definition of [iter_down_aux], which
   does not use Equations. At extraction time, this definition produces
   slightly better-looking OCaml code. However, reasoning about it is more
   difficult; we lose the fixed point equation and the induction principle
   produced by Equations, which are used via the tactic [funelim]. *)
Goal int → S → S.
Proof.
  eapply (Fix (Wf_rilt _i) (λ _, S → S)). intros _j self s.
  destruct (_j =? _i)%uint63 eqn:Heq.
  + refine (
      do s ← body _j s ;
      s
    ).
  + refine (
      do s ← body _j s ;
      self (_j - 1)%uint63 _ s
    ).
    eauto using safe_decrement_relative.
Defined.

End IterDown.

(* A specification of [iter_down_aux]. *)

(* This specification requires [i ≤ j]: that is, the start index [j] must
   be greater than or equal to the end index [i]. This hypothesis is
   natural: it is required to guarantee that no underflow takes place. *)

Lemma wp_iter_down_aux {S} (body : int → S → S) :
  ∀IntU _i i ,
  ∀IntU _j j ,
  i ≤ j →
  ITER_Z
    i (j + 1) Down
    (λ j s Q, ∀ _j, isInt _j j → wp (body _j s) Q)
    (λ s Q, wp (iter_down_aux _i body _j s) Q).
Proof.
  intros. ITER.
  funelim (iter_down_aux _i body _j s); cleanup; clear Heqcall;
  intros; isBool_magic; z.
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

(* TODO exchange _k and _i in the parameters of [iter_down]? *)

Lemma wp_iter_down {S} (body : int → S → S) :
  ∀IntU _i i ,
  ∀IntU _k k ,
  ITER_Z i k Down
    (λ j s Q, ∀ _j, isInt _j j → wp (body _j s) Q)
    (λ s Q, wp (iter_down _k _i s body) Q).
Proof.
  intros. ITER. unfold iter_down.
  wp_if; z.
  (* Case [k ≤ i]. *)
  { wp_ret. eauto. }
  (* Case [i < k]. *)
  { wp_loop @wp_iter_down_aux inv. }
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

End XIterDown.

(* A specification of [xiter_down_aux]. *)

Lemma wp_xiter_down_aux {S A}
  (body : ∀ {W}, int → S → (S → W) → (S → A → W) → W) :
  ∀IntU _i i ,
  ∀IntU _j j ,
  i ≤ j →
  XITER_Z i (j + 1) Down
    (λ j _ s continue break Q, ∀ _j, isInt _j j → wp (body _j s continue break) Q)
    (λ s Q, wp (xiter_down_aux _i (@body) _j s) Q).
Proof.
  intros. XITER.
  funelim (xiter_down_aux _i (@body) _j s); cleanup; clear Heqcall;
  intros; isBool_magic; z.
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
  ∀IntU _i i ,
  ∀IntU _k k ,
  XITER_Z i k Down
    (λ j _ s continue break Q, ∀ _j, isInt _j j → wp (body _j s continue break) Q)
    (λ s Q, wp (xiter_down _k _i s (@body)) Q).
Proof.
  intros. XITER. unfold xiter_down.
  wp_if; z.
  (* Case [k ≤ i]. *)
  { wp_ret. eauto. }
  (* Case [i < k]. *)
  { wp_loop @wp_xiter_down_aux inv. }
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

End UXIterDown.

(* A specification of [uxiter_down_aux]. *)

Lemma wp_uxiter_down_aux {A}
  (body : ∀ {W}, int → (unit → W) → (A → W) → W) :
  ∀IntU _i i ,
  ∀IntU _j j ,
  i ≤ j →
  UXITER_Z i (j + 1) Down
    (λ j _ continue break Q, ∀ _j, isInt _j j → wp (body _j continue break) Q)
    (λ Q, wp (uxiter_down_aux _i (@body) _j) Q).
Proof.
  intros. UXITER.
  funelim (uxiter_down_aux _i (@body) _j); cleanup; clear Heqcall;
  intros; isBool_magic; z.
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
  ∀IntU _i i ,
  ∀IntU _k k ,
  UXITER_Z i k Down
    (λ j _ continue break Q, ∀ _j, isInt _j j → wp (body _j continue break) Q)
    (λ Q, wp (uxiter_down _k _i (@body)) Q).
Proof.
  intros. UXITER. unfold uxiter_down.
  wp_if; z.
  (* Case [k ≤ i]. *)
  { wp_ret. eauto. }
  (* Case [i < k]. *)
  { wp_loop @wp_uxiter_down_aux inv. }
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

End IterUp.

(* A specification of [iter_up_aux], which also serves for [iter_up]. *)

Lemma wp_iter_up_aux {S} (body : int → S → S) :
  ∀IntU _i i ,
  ∀IntU _k k ,
  ITER_Z i k Up
    (λ j s Q, ∀ _j, isInt _j j → wp (body _j s) Q)
    (λ s Q, wp (iter_up_aux _k body _i s) Q).
Proof.
  intros. ITER.
  funelim (iter_up_aux _k body _i s); cleanup; clear Heqcall;
  isBool_magic; z.
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

End XiterUp.

(* A specification of [xiter_up_aux]. *)

Lemma wp_xiter_up_aux {S A}
  (body : ∀ {W}, int → S → (S → W) → (S → A → W) → W) :
  ∀IntU _i i ,
  ∀IntU _k k ,
  XITER_Z i k Up
    (λ j _ s continue break Q, ∀ _j, isInt _j j → wp (body _j s continue break) Q)
    (λ s Q, wp (xiter_up_aux _k (@body) _i s) Q).
Proof.
  (* The spec is quite complex, but the proof is very simple. *)
  intros. XITER.
  funelim (xiter_up_aux _k (@body) _i s); cleanup; clear Heqcall; intros;
  isBool_magic; z.
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

End UXIterUp.

(* A specification of [uxiter_up_aux]. *)

Lemma wp_uxiter_up_aux {A} (body : ∀ {W}, int → (unit → W) → (A → W) → W) :
  ∀IntU _i i ,
  ∀IntU _k k ,
  UXITER_Z i k Up
    (λ j _ continue break Q, ∀ _j, isInt _j j → wp (body _j continue break) Q)
    (λ Q, wp (uxiter_up_aux _k (@body) _i) Q).
Proof.
  (* The spec is quite complex, but the proof is very simple. *)
  intros. UXITER.
  funelim (uxiter_up_aux _k (@body) _i); cleanup; clear Heqcall; intros;
  isBool_magic; z.
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
