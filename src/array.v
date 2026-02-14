Unset Universe Minimization ToSet.
Generalizable All Variables.
Local Set Universe Polymorphism.
From stdpp Require Import base list.
From Stdlib Require Import Utf8.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.
From Stdlib Require Import Uint63.
From Stdlib Require Import Array.PArray.
(* TODO why is of_to_Z an axiom? *)

(* TODO lists *)
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

Local Hint Extern 1 (_ < List.length _) => (list; lia) : lia.

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


(* TODO move *)
(* [unsigned z] means that [z] lies in the interval of the unsigned
   machine integers. *)
Notation unsigned z :=
  (0 ≤ z < wB)%Z.

Section Zstuff.
Open Scope Z_scope.
Implicit Types z : Z.

Lemma to_of_Z z :
  unsigned z →
  to_Z (of_Z z) = z.
Proof.
  rewrite of_Z_spec. intros. eauto using Z.mod_small.
Qed.

Lemma of_Z_inj z1 z2 :
  unsigned z1 →
  unsigned z2 →
  of_Z z1 = of_Z z2 →
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
  of_Z z1 ≠ of_Z z2.
Proof.
  intros ? ? Hzz ?. apply Hzz. eauto using of_Z_inj.
Qed.

End Zstuff.

(* TODO move *)
Section intstuff.
Open Scope Z_scope.
Implicit Types i : int.

Lemma to_Z_ge_0 i :
  0 ≤ to_Z i.
Proof.
  apply (to_Z_bounded i).
Qed.

Lemma to_Z_lt_wB i :
  to_Z i < wB.
Proof.
  apply (to_Z_bounded i).
Qed.

End intstuff.

Global Hint Resolve
  to_Z_ge_0 to_Z_lt_wB
: int.

(* Documentation:
   https://rocq-prover.org/doc/V9.0.0/stdlib/Stdlib.Lists.List.html
   https://rocq-prover.org/doc/V9.0.1/corelib/Corelib.Numbers.Cyclic.Int63.Uint63Axioms.html
   https://rocq-prover.org/doc/v9.0/stdlib/Stdlib.Numbers.Cyclic.Int63.Uint63.html
   https://rocq-prover.org/doc/V9.0.1/corelib/Corelib.Array.PrimArray.html
   https://rocq-prover.org/doc/V9.0.1/corelib/Corelib.Array.ArrayAxioms.html
   https://rocq-prover.org/doc/v9.0/stdlib/Stdlib.Array.PArray.html
 *)

(* TODO logic *)
Definition wp {A} (a : A) (Q : A → Prop) :=
  Q a.

Lemma wp_conseq {A} (a : A) (Q Q' : A → Prop) :
  wp a Q →
  (∀ x, Q x → Q' x) →
  wp a Q'.
Proof.
  unfold wp. eauto.
Qed.

Lemma wp_ret {A} (a : A) (Q : A → Prop) :
  Q a ->
  wp a Q.
Proof.
  eauto.
Qed.

Definition bind {A B} (a : A) (b : A → B) : B :=
  let x := a in b x.

Lemma wp_bind {A B} (a : A) (b : A → B) (P : A → Prop) (Q : B → Prop) :
  wp a P →
  (∀ x, P x → wp (b x) Q) →
  wp (bind a b) Q.
Proof.
  eauto.
Qed.

Lemma wp_bind_eq {A B} (a : A) (b : A → B) (Q : B → Prop) :
  (∀ x, x = a → wp (b x) Q) →
  wp (bind a b) Q.
Proof.
  eauto.
Qed.

(* TODO this prevents computing inside Rocq:
  Global Opaque bind.
 *)
  (* TODO [bind] should be inlined away at extraction *)
Global Opaque wp.

Definition I (_i : int) (i : nat) :=
  _i = of_nat i.

Local Ltac introI :=
  unfold I.

Local Ltac destructI :=
  match goal with h: I ?_i _ |- _ => unfold I in h; try subst _i end.

Lemma project n :
  I (of_nat n) n.
Proof.
  unfold I. eauto.
Qed.

Global Hint Resolve
  project
: I.

Notation valid i xs :=
  (i < List.length xs).

Definition max_array_length : nat :=
  to_nat max_length.

Lemma max_length_spec :
  I max_length max_array_length.
Proof.
  introI. unfold max_array_length.
  rewrite Z2Nat.id by eauto with int.
  rewrite of_to_Z.
  eauto.
Qed.

Lemma max_length_eq :
  to_nat max_length = max_array_length.
Proof.
  unfold max_array_length. reflexivity.
Qed.

(* [max_array_length] is equal to [2 ^ 54 - 1]. *)

Lemma two_54_lt_wB :
  (2 ^ 54 < wB)%Z.
Proof.
  unfold wB, size. change (Z.of_nat 63) with 63%Z. lia.
Qed.

Lemma max_array_length_lt_two_54 :
  (Z.of_nat max_array_length < 2 ^ 54)%Z.
Proof.
  unfold max_array_length.
  rewrite Z2Nat.id by eauto with int.
  replace (2 ^ 54)%Z with (to_Z (lsl (1%uint63) 54)).
  { (* Prove the goal by using machine integers. *)
    rewrite <- ltb_spec. reflexivity. }
  { (* Check that 2^54 is representable. *)
    rewrite lsl_spec, to_Z_1, Z.mul_1_l.
    change (to_Z 54) with 54%Z.
    rewrite Z.mod_small; [ eauto |].
    split; [ lia | apply two_54_lt_wB ]. }
Qed.

Lemma max_array_length_lt_wB :
  (Z.of_nat max_array_length < wB)%Z.
Proof.
  eapply Z.lt_trans.
  + eapply max_array_length_lt_two_54.
  + eapply two_54_lt_wB.
Qed.

(* Local Hint Resolve max_array_length_lt_wB : int. *)

Definition R `{Inhabited A} (a : array A) (xs : list A) :=
  let n := List.length xs in
  I (length a) n ∧
  n ≤ max_array_length ∧
  ∀ i, valid i xs → a.[of_nat i] = xs !!! i.

(* TODO prove that R a xs is equivalent to to_list a = xs *)

Local Ltac introR :=
  split; [| split ].

Local Ltac destructR :=
  match goal with h: R _ _ |- _ => destruct h as (?&?&?) end.

Section PrimSpec.
Context `{Inhabited A}.
Implicit Types a : array A.
Implicit Types x : A.
Implicit Types xs : list A.

Lemma bounded_length a xs :
  R a xs →
  List.length xs ≤ max_array_length.
Proof.
  intros. destructR. eauto.
Qed.

Lemma wp_make _n n x :
  I _n n →
  n ≤ max_array_length →
  wp (make _n x) (λ a, R a (replicate n x)).
Proof.
  generalize max_array_length_lt_wB; intro.
  intros. eapply wp_ret. destructI. introR; list.
  { introI.
    assert ((of_nat n ≤? max_length)%uint63 = true) as Hbound.
    { rewrite leb_spec.
      rewrite max_length_spec.
      do 2 rewrite to_of_Z by lia.
      lia. }
    rewrite length_make.
    rewrite Hbound.
    eauto. }
  { eauto. }
  intros i ?.
  rewrite get_make.
  rewrite lookup_total_replicate_2 by eauto.
  eauto.
Qed.

Lemma wp_get _i i a xs :
  I _i i →
  R a xs →
  valid i xs →
  wp a.[_i] (λ x, x = xs !!! i).
Proof.
  (* This proof is trivial because the definition of [R] relies on [get]. *)
  intros. destructR. repeat destructI. eapply wp_ret. eauto.
Qed.
(* TODO offer a variant where the conclusion is just an equation? *)

Lemma wp_set _i i a xs x :
  I _i i →
  R a xs →
  valid i xs →
  wp a.[_i <- x] (λ a', R a' (<[i := x]>xs)).
Proof.
  intros. eapply wp_ret.
  destructR. repeat destructI. introR; list.
  { rewrite length_set. eauto. }
  { eauto. }
  intros j ?.
  generalize max_array_length_lt_wB; intro.
  destruct (decide (i = j)).
  + subst j.
    rewrite list_lookup_total_insert_eq by eauto.
    rewrite get_set_same.
    { eauto. }
    { rewrite ltb_spec.
      match goal with h: length ?a = _ |- _ => rewrite h end.
      rewrite !to_of_Z by lia.
      lia. }
  + rewrite list_lookup_total_insert_ne by eauto.
    rewrite get_set_other.
    { eauto. }
    { eapply of_Z_inj'; lia. }
Qed.

Lemma wp_length a xs :
  R a xs →
  wp (length a) (λ _i, I _i (List.length xs)).
Proof.
  intros. eapply wp_ret. destructR. eauto.
Qed.

End PrimSpec.

Global Ltac wp_set a Ha :=
  eapply wp_conseq; [
    eapply wp_set; eauto with lia
  | simpl; intros a Ha; insert in Ha ].

Section ListIteri.
Context {A S : Type}.

Fixpoint iteri (f : S → int → A → S) (s : S) (_i : int) (xs : list A) : S :=
  match xs with
  | [] =>
      s
  | x :: xs =>
      let s := f s _i x in
      iteri f s (succ _i) xs
  end.

End ListIteri.

Lemma wp_iteri {S A} (f : S → int → A → S) s _i xs Q (inv : S → list A → Prop) :
  let permitted history x := (history ++ [x]) `prefix_of` xs in
  let complete history := history = xs in
  inv s [] →
  ( ∀ s history _i x,
    I _i (List.length history) →
    inv s history →
    permitted history x →
    wp (f s _i x) (λ s, inv s (history ++ [x]))
  ) →
  (∀ s history, complete history → inv s history → Q s) →
  wp (iteri f s _i xs) Q.
Proof.
  (* TODO *)
Admitted.

Section OfList.
Context `{Inhabited A}.

Definition of_list (xs : list A) : array A :=
  bind (List.length xs) (λ n,
  bind (make (of_nat n) inhabitant) (λ a,
  iteri set a 0 xs
  )).

(* TODO move *)
Lemma expand_replicate `{Inhabited A} n (x : A) :
  0 < n →
  replicate n x = x :: replicate (n-1) x.
Proof.
  intros. destruct n as [| n]; [ lia |].
  rewrite replicate_S. do 2 f_equal. lia.
Qed.

Ltac apply_prefix_length :=
  match goal with h: _ `prefix_of` _ |- _ =>
    generalize h;
    let h' := fresh h in
    intro h'; apply prefix_length in h';
    list in h'
  end.

Lemma wp_of_list (xs : list A) :
  List.length xs ≤ max_array_length →
  wp (of_list xs) (λ a, R a xs).
Proof.
  intros. unfold of_list.
  eapply wp_bind_eq; intros n Hn.
  set (P := (λ (a : array A), R a (replicate n inhabitant))).
  (* TODO why do I need to specify [P]? *)
  eapply wp_bind with (P := P); [| intros a Ha ].
  { Fail eapply wp_make. (* TODO why does this fail? *)
    eapply (@wp_make A H (of_nat n) n (@inhabitant A H)).
    + eauto with I.
    + rewrite Hn. eauto. }
  unfold P in Ha.
  set (inv :=
    λ (a : array A) (history : list A),
    let h := List.length history in
    R a (history ++ replicate (n-h) inhabitant)
  ).
  eapply wp_iteri with (inv := inv).
  (* Initialization. *)
  { unfold inv. list. eauto. }
  (* Preservation. *)
  { intros. apply_prefix_length. wp_set s' Hs'. unfold inv. list. eauto. }
  (* Conclusion. *)
  { intros s ? ->. unfold inv. list. eauto. }
Qed.

End OfList.

Eval compute in (of_list [1;2;3]).
