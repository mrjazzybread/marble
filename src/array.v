From stdpp Require Import numbers list.
From Stdlib Require Import Uint63.
From Stdlib Require Import Array.PArray.
From array Require Import list_extra bool int wp.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

Open Scope nat_scope.

(* Documentation:
   https://rocq-prover.org/doc/V9.0.1/corelib/Corelib.Array.PrimArray.html
   https://rocq-prover.org/doc/V9.0.1/corelib/Corelib.Array.ArrayAxioms.html
   https://rocq-prover.org/doc/v9.0/stdlib/Stdlib.Array.PArray.html
 *)

(* -------------------------------------------------------------------------- *)

(* An index [i : nat] is valid with respect to a list [xs] if and only if
   it is less than the length of the list. *)

Local Notation valid i xs :=
  (i < List.length xs).

(* -------------------------------------------------------------------------- *)

(* The maximum length of an array. *)

(* We have [max_length : int]; we define [max_array_length : nat]. *)

Definition max_array_length : nat :=
  to_nat max_length.

(* These constants are related by [isInt]. *)

Lemma max_length_spec :
  isInt max_length max_array_length.
Proof.
  introIsInt. unfold max_array_length. int. eauto.
Qed.
  (* do not use this lemma as a resolve hint *)
  (* this makes everything hopelessly slow!  *)

(* [max_array_length] is representable. *)

Lemma representable_max_array_length :
  representable max_array_length.
Proof.
  rewrite representable_iff_Z. split; [ lia |].
  (* (Z.of_nat max_array_length < wB)%Z *)
  unfold max_array_length. int.
  (* (φ%uint63 max_length < wB)%Z *)
  reflexivity.
Qed.

Hint Resolve representable_max_array_length : representable.

(* Any number that is bounded by [max_array_length] is representable. *)

Goal ∀ n, n ≤ max_array_length → representable n.
Proof. eauto with representable. Qed.

(* The length of an array, converted to a natural number,
   is bounded by [max_array_length]. *)

Local Lemma leb_length' {A} (a : array A) :
  to_nat (length a) <= max_array_length.
Proof.
  generalize (leb_length _ a); intro H.
  rewrite leb_spec in H.
  rewrite max_length_spec in H.
  unfold max_array_length in *.
  rewrite of_nat_to_nat in H. (* [int in H] takes 10 seconds *)
  lia.
Qed. (* a bit slow *)

Local Hint Resolve leb_length' : representable.

(* The length of an array is representable. *)

Lemma representable_to_nat_length {A} (a : array A) :
  representable (to_nat (length a)).
Proof.
  eauto using leb_length' with representable.
Qed.

Hint Resolve representable_to_nat_length : representable.

(* -------------------------------------------------------------------------- *)

(* The proposition [isArray a xs] means that the elements of the array [a]
   form the list [xs]. *)

(* We will later establish that the proposition [isArray a xs] is equivalent
   to [to_list a = xs]. One might wonder whether we should define it in this
   way. My answer is: I don't know, but it is probably useful to have access
   to both definitions anyway. *)

(* The definition requires the array [a] and the list [xs] to have the same
   length and to hold the same element at every valid index. *)

Definition isArray `{Inhabited A} (a : array A) (xs : list A) :=
  let n := List.length xs in
  isInt (length a) n ∧
  n ≤ max_array_length ∧
  ∀ i, valid i xs → a.[of_nat i] = xs !!! i.

(* Local tactics and lemmas. *)

Local Ltac introIsArray :=
  split; [| split ].

Local Ltac destructIsArray :=
  match goal with h: isArray _ _ |- _ => destruct h as (?&?&?) end.

Local Lemma isArray_pi3 `{Inhabited A} (a : array A) (xs : list A) :
  isArray a xs →
  ∀ i, valid i xs →
  a.[of_nat i] = xs !!! i.
Proof.
  intros. destructIsArray. eauto.
Qed.

(* TODO avoid using [destructIsArray] except in a very local way *)

(* [isArray a _] is injective. *)

Lemma isArray_inj_2 `{Inhabited A} a (xs ys : list A) :
  isArray a xs → isArray a ys → xs = ys.
Proof.
  intros.
  assert (List.length xs = List.length ys).
  { repeat destructIsArray. eauto using isInt_inj_2 with representable. }
  eapply list_eq_same_length; eauto; intros.
  rewrite !list_lookup_lookup_total_lt in * by eauto with lia.
  erewrite <- isArray_pi3 in * by eauto with lia.
  congruence.
Qed.

(* [isArray _ xs] is injective. *)

(* TODO move *)
Lemma qwd z n :
  (0 ≤ z)%Z →
  (z < Z.of_nat n)%Z →
  (Z.to_nat z < n)%nat.
Proof.
  lia.
Qed.

Hint Resolve qwd : lia.

Lemma isArray_inj_1 `{Inhabited A} a b (xs : list A) :
  isArray a xs →
  isArray b xs →
  default a = default b →
  a = b.
Proof.
  intros. repeat destructIsArray.
  assert (representable (List.length xs)) by eauto with representable.
  eapply array_ext.
  { eauto using isInt_inj_1. }
  { intros _i Hi.
    (* This is a bit messier than I would like. *)
    rewrite ltb_spec in Hi.
    match goal with h: isInt (length a) _ |- _ => rewrite h in Hi end.
    int in Hi.
    assert (Hv: valid (to_nat _i) xs) by eauto with lia.
    (* TODO use isArray_pi3 *)
    repeat match goal with h: ∀ i : nat, _ |- _ =>
      specialize (h _ Hv); int in h; rewrite h; clear h
    end.
    reflexivity. }
  { eauto. }
Qed.

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

Lemma length_make' _n n x :
  isInt _n n →
  n <= max_array_length →
  length (make _n x) = _n.
Proof.
  unfold isInt. intros. subst.
  assert ((of_nat n ≤? max_length)%uint63 = true) as Hbound.
  { rewrite leb_spec, max_length_spec. int. lia. }
  rewrite length_make, Hbound. eauto.
Qed.

Lemma wp_make _n n x :
  isInt _n n →
  n ≤ max_array_length →
  wp (make _n x) (λ a, isArray a (replicate n x)).
Proof.
  intros. eapply wp_ret. destructIsInt. introIsArray; list.
  { introIsInt. eauto using length_make' with int. }
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
    { eapply of_nat_inj'; eauto with representable. }
Qed.

Lemma wp_length a xs :
  isArray a xs →
  wp (length a) (λ _n,
    isInt _n (List.length xs) ∧
    representable (List.length xs)
  ).
Proof.
  generalize representable_max_array_length; intro.
  intros. eapply wp_ret. destructIsArray.
  eauto with representable.
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
      do s ← f s _i x ;
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
  do n ← list_length xs ;
  do a ← make n inhabitant ;
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

Section ToList.
Context `{Inhabited A}.
Implicit Types a : array A.
Implicit Types xs : list A.

Definition to_list a :=
  do _n ← length a ;
  down _n [] @@ λ _i xs,
  do x ← a.[_i] ;
  x :: xs.

Lemma wp_to_list a xs :
  isArray a xs →
  wp (to_list a) (λ xs', xs' = xs).
Proof.
  intro. unfold to_list.
  (* TODO why? *)
  set (P := λ _n,
    let n := List.length xs in
    isInt _n n ∧ representable n
  ).
  eapply @wp_bind with (P := P).
  { eapply (@wp_length _ _ a xs). eauto. }
  unfold P.
  set (n := List.length xs).
  intros _n [? ?].
  (* The loop. *)
  set (inv := λ i ys, ys = drop i xs).
  eapply wp_down with (inv := inv); eauto; unfold inv; intros.
  (* Initialization. *)
  { unfold n. rewrite drop_all. eauto. }
  (* Preservation. *)
  { eapply wp_bind; [ eapply wp_get; eauto with lia | simpl; intros x ? ].
    eapply wp_ret.
    subst. rewrite drop_S' by eauto with lia. eauto. }
Qed.

(* TODO this spec is stronger *)
Lemma wp_to_list' a :
  wp (to_list a) (λ xs, isArray a xs).
Proof.
  intros. unfold to_list.
  eapply wp_bind_eq. intros _n ?.
  set (n := to_nat _n).
  assert (n ≤ max_array_length) by (subst n _n; eauto with representable).
  assert (representable n) by eauto with representable.
  (* The loop. *)
  set (inv := λ i (ys : list A),
    List.length ys = n - i ∧
    ∀ j, i ≤ j < n → a.[of_nat j] = ys !!! (j - i)
  ).
  eapply wp_down with (inv := inv); eauto using introIsInt';
    unfold inv; intros.
  (* Initialization. *)
  { split.
    + rewrite length_nil. lia.
    + intros. exfalso. lia. }
  (* Preservation. *)
  { rename s into ys.
    match goal with h: _ ∧ _ |- _ => destruct h as [Hys Hlookup] end.
    eapply wp_bind_eq. intros x ->.
    eapply wp_ret.
    split; [ simpl; lia |].
    intros j ?.
    assert (i = j ∨ i < j) as [|] by lia.
    { subst j. rewrite Nat.sub_diag. simpl. congruence. }
    { match goal with h: ∀ j : nat, _ |- _ => rewrite h by lia end.
      rewrite lookup_total_cons_ne_0 by lia. f_equal. lia. }
  }
  (* Conclusion. *)
  { rename s into ys.
    match goal with h: _ ∧ _ |- _ => destruct h as [Hys Hlookup] end.
    rewrite Nat.sub_0_r in Hys.
    introIsArray.
    + introIsInt. rewrite Hys. subst n. int. congruence.
    + rewrite Hys. assumption.
    + intros j ?. rewrite Hlookup, Nat.sub_0_r by lia. eauto.
  }
Qed.

End ToList.

(* TODO Eval compute is unable to run [down_aux] *)
Eval    compute in to_list (of_list [1;2;3]).
Eval vm_compute in to_list (of_list [1;2;3]).
(* TODO try native_compute *)

Lemma to_list_of_list `{Inhabited A} (xs : list A) :
  List.length xs ≤ max_array_length →
  to_list (of_list xs) = xs.
Proof.
  intros.
  assert (fact:
    wp (
      do a ← of_list xs ;
      do ys ← to_list a ;
      ys
    ) (λ ys, xs = ys)
  ).
  { eapply wp_bind; [ eapply wp_of_list; eauto | simpl; intros a ? ].
    eapply wp_bind; [ eapply wp_to_list; eauto | simpl; intros ? ->].
    eapply wp_ret. eauto. }
  symmetry. exact fact.
Qed.

(* With some effort, one could prove this lemma,
   but I am not sure that it is worth the trouble.
Lemma of_list_to_list `{Inhabited A} (a : array A) :
  default a = inhabitant →
  of_list (to_list a) = a.
 *)

(* TODO
  prove that [isArray a xs] is equivalent to [to_list a = xs]
 *)
