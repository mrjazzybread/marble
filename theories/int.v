(******************************************************************************)
(*                                                                            *)
(*                                  Marble                                    *)
(*                                                                            *)
(*                       François Pottier, Inria Paris                        *)
(*                                                                            *)
(*       Copyright 2026--2026 Inria. All rights reserved. This file is        *)
(*       distributed under the terms of the GNU Library General Public        *)
(*       License, with an exception, as described in the file LICENSE.        *)
(*                                                                            *)
(******************************************************************************)

From stdpp Require Import numbers well_founded.
From Stdlib Require Export ZifyNat.
  (* [ZifyNat] magically makes [lia] more powerful,
     including on goals that involve division in Z *)
From Stdlib Require Import Uint63 ZifyUint63.
  (* [ZifyUint63] magically makes [lia] more powerful *)
From Stdlib Require Import Wellfounded.Wellfounded.
From listz Require Import listz.
From marble Require Import tactics bool.
From marble Require Import equations.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

(* This file provides support for working with unsigned primitive integers. *)

(* The type of 63-bit unsigned primitive integers is named [int]. *)

(* Documentation:
   https://rocq-prover.org/doc/v9.1/stdlib/Stdlib.Numbers.Cyclic.Int63.Uint63.html
   https://rocq-prover.org/doc/V9.0.1/corelib/Corelib.Numbers.Cyclic.Int63.Uint63Axioms.html
 *)

Open Scope Z_scope.
Implicit Types _i _j _k : int.
Implicit Types  i : Z.
Implicit Types  z : Z.

(* -------------------------------------------------------------------------- *)

(* The type [int] is inhabited. *)

Instance Inhabited_int : Inhabited int.
Proof. constructor. exact 0%uint63. Defined.

(* -------------------------------------------------------------------------- *)

(* [unsigned z] means that [z] lies in the interval of the unsigned
   machine integers. *)

(* In our comments, we use the word "representable" as a synonym
   for [unsigned]. *)

Notation unsigned z :=
  (0 ≤ z < wB).

(* [wB] is just a name for 2^63. *)

Goal wB = 2^63.
Proof. reflexivity. Qed.

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

Notation isIntU _i i :=
  (isInt _i i ∧ unsigned i).

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

(* This lemma allows solving every goal of the form [isInt _i ?i]
   where [?i] is a metavariable. However, this is not always a good
   idea; see below. *)

Lemma introIsInt _i i :
  to_Z _i = i →
  isInt _i i.
Proof.
  intros. subst. introIsInt. int. eauto.
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

(* Set up a tactic to prove [isInt _ _]. *)

(* I cannot rely purely on type class search because I don't know how
   to teach it this rule: apply [introIsInt] only if the left-hand
   side is a primitive integer literal. *)

Ltac proveIsInt :=
  lazymatch goal with
  | h: isInt ?_i ?i1 |- isInt ?_i ?i2 =>
      (* Exploit a hypothesis. *)
      replace i2 with i1 by lia;
      exact h
  | |- isInt ?_i ?i =>
      (* If [_i] is a primitive integer literal, such as [12%uint63], then
          we want to apply the lemma [introIsInt] and use [compute] in the
          premise, so that [i] is instantiated with [12%Z] (if it is a
          metavariable). On the other hand, if [_i] is not a primitive
          integer literal then we do not want to apply [introIsInt]. *)
      (* [unify] is a way of testing whether [_i] is (convertible with)
         a primitive integer literal. Thanks to Guillaume Melquiond! *)
      unify (add _i 0)%uint63 _i ;
      eapply introIsInt; compute; eauto 2 with lia
  end.

Global Hint Extern 1 (isInt _ _) =>
  proveIsInt
: typeclass_instances.

(* Tests: proving [isInt _ _]. *)

Goal ∀ _i i, isInt _i i → isInt _i (1 + i - 1).
Proof. tc. Qed.

Goal ∀ _i i, isInt _i i → isInt (_i + 1) (i + 1).
Proof. tc. Qed.

Goal ∀ _i i, isInt _i i → unsigned i → isInt (_max _i 22) (i `max` 22).
Proof. tc. Qed.

Goal ∀ _i i, isInt _i i → unsigned i → isInt (_min 0 _i) (0 `min` i).
Proof. tc. Qed.

Goal isInt (1)%uint63 (1)%Z.
Proof. tc. Qed.

Goal isInt (1)%uint63 (2^63+1)%Z.
Proof.
  (* This one is tricky; [tc] cannot prove it. *)
  rewrite isInt_def. lia.
Qed.

Goal isInt 12 12.
Proof. tc. Qed.

Goal ∃ i, isInt 512 i ∧ i = 512.
Proof. tc. Qed.

Goal ∃ i, isInt 512 i ∧ i = 512.
Proof.
  (* Same example, interactively. *)
  eexists. split. tc. tc.
Qed.

Goal ∀ _i, ∃ i, isInt _i i.
Proof.
  (* We do not want [tc] to solve this goal. *)
  intro. eexists. Fail solve [tc].
Abort.

Goal ∀ _i i _j j ,
  isInt _i i →
  isInt _j j →
  isInt (_i+(_j-1)) (i+(j-1)).
Proof. tc3. Qed.

(* Test: proving [unsigned _]. *)

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

(* Placing the lemmas [Acc_ilt] and friends in the hint database [marble]
   lets us write [ltac:(tc)] where a proof of accessibility is expected. *)

(* [ilt] *)

Definition ilt _i _j :=
  φ _i < φ _j.

Global Hint Extern 1 (ilt _ _) =>
  (rewrite ?isInt_def in *; unfold ilt; lia) : marble.

Lemma ilt_wf : well_founded ilt.
Proof.
  eapply wf_incl; [| eapply Z.lt_wf_projected with (z := 0) (f := φ) ].
  intros _i _j. eauto with marble.
Qed.

Global Instance Wf_ilt : WellFounded ilt :=
  wf_guard 32 ilt_wf.
  (* The use of [wf_guard] is meant to allow computation inside Rocq
     in spite of the opaque well-foundedness proof [ilt_wf]. *)

Lemma Acc_ilt _n : Acc ilt _n.
Proof. eapply Wf_ilt. Defined.
Hint Resolve Acc_ilt : marble.

(* The following lemmas are useful in direct definitions of recursive
   functions by structural induction on a proof of accessibility. *)

Lemma ilt_n_minus_1 _n :
  (_n =? 0)%uint63 = false →
  ilt (_n - 1)%uint63 _n.
Proof. eauto with marble. Qed.

Goal ∀IntU _n n, n ≠ 0 → ilt (_n - 1) _n.
Proof. eauto with marble. Qed.

(* [rilt] *)

Definition rilt _a _i _j :=
  ilt (_i - _a) (_j - _a).

Global Hint Extern 1 (rilt _ _ _) =>
  (rewrite ?isInt_def in *; unfold rilt, ilt; lia) : marble.

Lemma rilt_wf _a : well_founded (rilt _a).
Proof.
  eapply wf_incl; [| eapply Z.lt_wf_projected with (z := 0) (f := λ _i, φ (_i - _a)) ].
  intros _i _j. eauto with marble.
Qed.

Global Instance Wf_rilt _a : WellFounded (rilt _a) :=
  wf_guard 32 (rilt_wf _a).

Lemma Acc_rilt _a _i : Acc (rilt _a) _i.
Proof. eapply Wf_rilt. Defined.
Hint Resolve Acc_rilt : marble.

(* The following lemmas are useful in direct definitions of recursive
   functions by structural induction on a proof of accessibility. *)

Lemma rilt_n_minus_1 _k _i :
  (_k =? _i)%uint63 = false →
  (rilt _i) (_k - 1)%uint63 _k.
Proof. eauto with marble. Qed.

Goal ∀IntU _k k, ∀IntU _i i, k ≠ i → rilt _i (_k - 1) _k.
Proof. eauto with marble. Qed.

(* [igt] *)

Definition igt _i _j :=
  φ _j < φ _i.

Lemma igt_alt_def _i _j :
  igt _i _j ↔ φ _j < φ _i < wB.
Proof.
  unfold igt. split; eauto with lia.
Qed.

Global Hint Extern 1 (igt _ _) =>
  (rewrite ?isInt_def in *; unfold igt; lia) : marble.

Lemma igt_wf : well_founded igt.
Proof.
  eapply wf_incl;
    [| eapply Z.lt_wf_projected with (z := 0) (f := λ _i, wB - φ _i) ].
  intros _i _j. rewrite igt_alt_def. lia.
Qed.

Global Instance Wf_igt : WellFounded igt :=
  wf_guard 32 igt_wf.

Lemma Acc_igt _n : Acc igt _n.
Proof. eapply Wf_igt. Defined.
Hint Resolve Acc_igt : marble.

(* The following lemmas are useful in direct definitions of recursive
   functions by structural induction on a proof of accessibility. *)

Lemma igt_n_plus_1 _n _k :
  (_n <? _k)%uint63 = true →
  igt (_n + 1)%uint63 _n.
Proof. eauto with marble. Qed.

Goal ∀IntU _n n, ∀IntU _k k, n < k → igt (_n + 1) _n.
Proof. eauto with marble. Qed.

(* [rigt] *)

Definition rigt _a _i _j :=
  igt (_i - _a) (_j - _a).

Global Hint Extern 1 (rigt _ _ _) =>
  (rewrite ?isInt_def in *; unfold rigt, igt; lia) : marble.

Lemma rigt_wf _a : well_founded (rigt _a).
Proof.
  eapply wf_incl; [| eapply Z.lt_wf_projected
                     with (z := 0) (f := λ _i, wB - φ (_i - _a)) ].
  intros _i _j. unfold rigt, igt. lia.
Qed.

Global Instance Wf_rigt _a : WellFounded (rigt _a) :=
  wf_guard 32 (rigt_wf _a).

Lemma Acc_rigt _a _i : Acc (rigt _a) _i.
Proof. eapply Wf_rigt. Defined.
Hint Resolve Acc_rigt : marble.

(* -------------------------------------------------------------------------- *)

(* The following results are unused. I keep them for the record; they
   are just illustrations of the power of [eauto with marble]. *)

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
  eauto with marble.
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
  eauto with marble.
Qed.

(* The following lemma removes the hypothesis [φ _a ≤ φ _i],
   but it is specialized to the case where [_a] is 0.
   It is also unused. *)

Local Lemma safe_decrement_absolute _i :
  (_i =? 0)%uint63 = false →
  ilt (_i - 1) _i.
Proof.
  (* _i ≠ 0%uint63 → φ (_i - 1) < φ _i *)
  eauto with marble.
Qed.

(* The following lemma removes the hypothesis [φ _a ≤ φ _i] and accepts
   an arbitrary choice of [_a]. The relative ordering [rilt _a] is used
   instead of the absolute ordering [ilt]. *)

Local Lemma safe_decrement_relative _i _a :
  (_i =? _a)%uint63 = false →
  rilt _a (_i - 1) _i.
Proof.
  (* _i ≠ _a → φ (_i - 1 - _a) < φ (_i - _a) *)
  eauto with marble.
Qed.

(* -------------------------------------------------------------------------- *)

(* This instance can be useful when we use natural numbers
   at compile time and convert them to machine integers. *)

Instance isInt_of_nat n : isInt (of_nat n) (Z.of_nat n).
Proof. rewrite isInt_def. lia. Qed.

Lemma Z_of_nat_S n :  Z.of_nat (S n) = Z.of_nat n + 1.
Proof. lia. Qed.
  (* Nat2Z.inj_succ : Z.of_nat (S n) = Z.succ (Z.of_nat n) *)

Hint Rewrite Z_of_nat_S : uz z.
