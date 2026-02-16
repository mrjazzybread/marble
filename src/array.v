(* TODO useful?
Unset Universe Minimization ToSet.
Generalizable All Variables.
Local Set Universe Polymorphism.
 *)

From stdpp Require Import numbers list.
From Stdlib Require Import Uint63.
From Stdlib Require Import Array.PArray.
From array Require Import list_extra bool int wp.

Open Scope nat_scope.

(* Documentation:
   https://rocq-prover.org/doc/V9.0.1/corelib/Corelib.Array.PrimArray.html
   https://rocq-prover.org/doc/V9.0.1/corelib/Corelib.Array.ArrayAxioms.html
   https://rocq-prover.org/doc/v9.0/stdlib/Stdlib.Array.PArray.html
 *)

Global Notation valid i xs :=
  (i < List.length xs).

Definition max_array_length : nat :=
  to_nat max_length.

Lemma max_length_spec :
  isInt max_length max_array_length.
Proof.
  introIsInt. unfold max_array_length. int. eauto.
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
  unfold max_array_length. int.
  replace (2 ^ 54)%Z with (φ (lsl (1%uint63) 54)).
  { (* Prove the goal by using machine integers. *)
    rewrite <- ltb_spec. reflexivity. }
  { (* Check that 2^54 is representable. *)
    rewrite lsl_spec, to_Z_1, Z.mul_1_l.
    change (φ 54) with 54%Z.
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

Definition isArray `{Inhabited A} (a : array A) (xs : list A) :=
  let n := List.length xs in
  isInt (length a) n ∧
  n ≤ max_array_length ∧
  ∀ i, valid i xs → a.[of_nat i] = xs !!! i.

(* TODO prove that R a xs is equivalent to to_list a = xs *)

Local Ltac introIsArray :=
  split; [| split ].

Local Ltac destructIsArray :=
  match goal with h: isArray _ _ |- _ => destruct h as (?&?&?) end.

Section PrimSpec.
Context `{Inhabited A}.
Implicit Types a : array A.
Implicit Types x : A.
Implicit Types xs : list A.

Lemma bounded_length a xs :
  isArray a xs →
  List.length xs ≤ max_array_length.
Proof.
  intros. destructIsArray. eauto.
Qed.

Lemma wp_make _n n x :
  isInt _n n →
  n ≤ max_array_length →
  wp (make _n x) (λ a, isArray a (replicate n x)).
Proof.
  generalize max_array_length_lt_wB; intro.
  intros. eapply wp_ret. destructIsInt. introIsArray; list.
  { introIsInt.
    assert ((of_nat n ≤? max_length)%uint63 = true) as Hbound.
    { rewrite leb_spec, max_length_spec. int. lia. }
    rewrite length_make, Hbound. eauto. }
  { eauto. }
  intros i ?.
  rewrite get_make.
  rewrite lookup_total_replicate_2 by eauto.
  eauto.
Qed.

Lemma wp_get _i i a xs :
  isInt _i i →
  isArray a xs →
  valid i xs →
  wp a.[_i] (λ x, x = xs !!! i).
Proof.
  (* This proof is trivial because the definition of [R] relies on [get]. *)
  intros. destructIsArray. repeat destructIsInt. eapply wp_ret. eauto.
Qed.
(* TODO offer a variant where the conclusion is just an equation? *)

Lemma wp_set _i i a xs x :
  isInt _i i →
  isArray a xs →
  valid i xs →
  wp a.[_i <- x] (λ a', isArray a' (<[i := x]>xs)).
Proof.
  intros. eapply wp_ret.
  destructIsArray. repeat destructIsInt. introIsArray; list.
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
      int. lia. }
  + rewrite list_lookup_total_insert_ne by eauto.
    rewrite get_set_other.
    { eauto. }
    { eapply of_Z_inj'; lia. }
Qed.

Lemma wp_length a xs :
  isArray a xs →
  wp (length a) (λ _i, isInt _i (List.length xs)).
Proof.
  intros. eapply wp_ret. destructIsArray. eauto.
Qed.

End PrimSpec.

Global Ltac wp_set a Ha :=
  eapply wp_conseq; [
    eapply wp_set; eauto with lia
  | simpl; intros a Ha; list in Ha ].

Section ListIteri.
Context {A S : Type}.

Fixpoint iteri (f : S → int → A → S) (s : S) (_i : int) (xs : list A) : S :=
  match xs with
  | [] =>
      s
  | x :: xs =>
      ' s ⇜ f s _i x ;
      iteri f s (_i + 1) xs
  end.

End ListIteri.

Lemma wp_iteri_aux {S A} (f : S → int → A → S) (inv : S → list A → Prop) xs :
  ∀ future s _i history,
  isInt _i (List.length history) →
  inv s history →
  history ++ future = xs →
  ( ∀ s future history _i x,
    isInt _i (List.length history) →
    inv s history →
    history ++ future = xs →
    [x] `prefix_of` future →
    wp (f s _i x) (λ s, inv s (history ++ [x]))
  ) →
  wp (iteri f s _i future) (λ s, inv s xs).
Proof.
  induction future as [| x future ];
  intros ??? HI Hinv Hxs Hpreservation;
  simpl iteri.
  { list in Hxs. subst history. eapply wp_ret. eauto. }
  { eapply wp_bind.
    { eapply Hpreservation; eauto using prefix_cons, prefix_nil. }
    simpl. intros s' Hs'.
    eapply IHfuture with (history := history ++ [x]);
      list; eauto with int. }
Qed.

Lemma wp_iteri {S A} (f : S → int → A → S) xs Q (inv : S → list A → Prop) s :
  inv s [] →
  ( ∀ s history _i x,
    isInt _i (List.length history) →
    inv s history →
    history ++ [x] `prefix_of` xs →
    wp (f s _i x) (λ s, inv s (history ++ [x]))
  ) →
  (∀ s, inv s xs → Q s) →
  wp (iteri f s 0 xs) Q.
Proof.
  intros Hinv Hpreservation Hcompletion.
  eapply wp_conseq.
  { eapply wp_iteri_aux; eauto; list.
    - introIsInt. eauto.
    - intros. subst. eauto using prefix_app. }
  { eauto. }
Qed.

Section ListLength.
Context {A : Type}.
Implicit Types xs : list A.

Fixpoint list_length_aux (_s : int) xs : int :=
  match xs with [] => _s | _ :: xs => list_length_aux (_s + 1) xs end.

Definition list_length xs : int :=
  list_length_aux 0 xs.

Lemma wp_list_length_aux xs : ∀ _s s,
  isInt _s s →
  wp (list_length_aux _s xs) (λ _i, isInt _i (s + List.length xs)).
Proof.
  induction xs as [| x xs ]; simpl; intros.
  { eapply wp_ret. rewrite Nat.add_0_r. eauto. }
  { eapply wp_conseq; [ eauto with int |]. simpl.
    rewrite <- Nat.add_assoc. eauto. }
Qed.

Lemma wp_list_length xs :
  wp (list_length xs) (λ _i, isInt _i (List.length xs)).
Proof.
  eapply wp_conseq.
  { eapply wp_list_length_aux. eapply introIsInt'. }
  { simpl. eauto. }
Qed.

End ListLength.

Section OfList.
Context `{Inhabited A}.

Definition of_list (xs : list A) : array A :=
  ' n ⇜ list_length xs ;
  ' a ⇜ make n inhabitant ;
  iteri set a 0 xs.

Lemma wp_of_list (xs : list A) :
  List.length xs ≤ max_array_length →
  wp (of_list xs) (λ a, isArray a xs).
Proof.
  intros. unfold of_list.
  eapply wp_bind; [ eapply wp_list_length | simpl ].
  set (n := List.length xs).
  intros _n H_n.
  set (P := (λ (a : array A), isArray a (replicate n inhabitant))).
  (* TODO why do I need to specify [P]? *)
  eapply wp_bind with (P := P); [| intros a Ha ].
  { Fail eapply wp_make. (* TODO why does this fail? *)
    eapply (@wp_make A H _n n (@inhabitant A H)); eauto with lia. }
  unfold P in Ha.
  (* The loop invariant. *)
  set (inv :=
    λ (a : array A) (history : list A),
    let h := List.length history in
    isArray a (history ++ replicate (n-h) inhabitant)
  ).
  eapply wp_iteri with (inv := inv).
  (* Initialization. *)
  { unfold inv. list. eauto. }
  (* Preservation. *)
  { intros. apply_prefix_length. wp_set s' Hs'. unfold inv. list. eauto. }
  (* Conclusion. *)
  { unfold inv. list. eauto. }
Qed.

End OfList.

(* TODO
From Stdlib Require Extraction ExtrOCamlInt63 ExtrOCamlPArray.
Extraction Inline bind.
 *)

(* TODO:
 + better monadic notation
 + better loop notation with @@
 + set up extraction in a clean way
 + test extracting to defensive mutable arrays
 *)
