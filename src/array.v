From stdpp Require Import numbers list.
From Stdlib Require Import Uint63.
From Stdlib Require Import Array.PArray.
From array Require Import list_extra bool int wp.
Implicit Types _i _j _n _s : int.

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

(* These tactics and lemmas help work with [isArray]. *)

Local Ltac introIsArray :=
  split; [| split ].

Local Ltac destructIsArray :=
  match goal with h: isArray _ _ |- _ => destruct h as (?&?&?) end.

(* This lemma can be viewed as a specification of [length],
   viewed as a "pure function", so [wp] is not used. *)

Lemma isArray_length_spec `{Inhabited A} (a : array A) (xs : list A) :
  isArray a xs →
  isInt (length a) (List.length xs).
Proof.
  intros. destructIsArray. eauto.
Qed.

Lemma isArray_bounded_length `{Inhabited A} (a : array A) (xs : list A) :
  isArray a xs →
  List.length xs ≤ max_array_length.
Proof.
  intros. destructIsArray. eauto.
Qed.

Lemma isArray_bounded_length' `{Inhabited A} (a : array A) (xs : list A) :
  ∀ n,
  isArray a xs →
  n ≤ List.length xs →
  n ≤ max_array_length.
Proof.
  intros. destructIsArray. lia.
Qed.

Global Hint Resolve
  isArray_bounded_length'
: lia.

Lemma isArray_representable `{Inhabited A} (a : array A) (xs : list A) :
  isArray a xs →
  representable (List.length xs).
Proof.
  intros. destructIsArray. eauto with representable.
Qed.

Global Hint Resolve isArray_representable : representable.

Local Lemma isArray_pi3 `{Inhabited A} (a : array A) (xs : list A) :
  isArray a xs →
  ∀ i, valid i xs →
  a.[of_nat i] = xs !!! i.
Proof.
  intros. destructIsArray. eauto.
Qed.

Local Lemma isArray_pi3' `{Inhabited A} (a : array A) (xs : list A) :
  isArray a xs →
  ∀ _i, valid (to_nat _i) xs →
  a.[_i] = xs !!! (to_nat _i).
Proof.
  intros. erewrite <- isArray_pi3 by eauto. int. eauto.
Qed.

Local Lemma isArray_show_valid `{Inhabited A} (a : array A) (xs : list A) _i :
  isArray a xs →
  (_i <? length a)%uint63 = true →
  valid (to_nat _i) xs.
Proof.
  intro. rewrite ltb_spec, isArray_length_spec by eauto. int.
  eauto with lia. (* [to_nat_lt] and [to_Z_ge_0] are exploited *)
Qed.

Local Lemma isArray_use_valid `{Inhabited A} (a : array A) (xs : list A) i :
  isArray a xs →
  valid i xs →
  (of_nat i <? length a)%uint63 = true.
Proof.
  intros. rewrite ltb_spec, isArray_length_spec by eauto. int. lia.
Qed.

(* [isArray _ xs] is injective, up to the side condition
   [default a = default b], which is rather painful. *)

Lemma isArray_inj_1 `{Inhabited A} a b (xs : list A) :
  isArray a xs →
  isArray b xs →
  default a = default b →
  a = b.
Proof.
  intros.
  eapply array_ext.
  { eauto using isInt_inj_1, isArray_length_spec. }
  { intros _i ?.
    repeat erewrite isArray_pi3' by eauto using isArray_show_valid.
    eauto. }
  { eauto. }
Qed.

(* [isArray a _] is injective. *)

Lemma isArray_inj_2 `{Inhabited A} a (xs ys : list A) :
  isArray a xs → isArray a ys → xs = ys.
Proof.
  intros.
  assert (List.length xs = List.length ys).
  { eauto 6 using isInt_inj_2, isArray_length_spec with representable. }
  eapply list_eq_same_length; eauto; intros.
  rewrite !list_lookup_lookup_total_lt in * by eauto with lia.
  erewrite <- isArray_pi3 in * by eauto with lia.
  congruence.
Qed.

(* -------------------------------------------------------------------------- *)

(* The primitive operations on arrays are [make], [get], [set], and [length]. *)

(* We provide specifications for these operations in terms of [isArray]. *)

(* One might believe that these four lemmas are the only places where the
   definition of [isArray] matters; so that, from there on, everything is
   built on top of these four operations and their specs. However, we will
   later argue that it is also desirable to give a direct proof of [to_list]. *)

Section PrimSpec.
Context `{Inhabited A}.
Implicit Types a : array A.
Implicit Types x : A.
Implicit Types xs : list A.

(* A specialized variant of the axiom [length_make]
   for the case where the desired length is smaller
   than [max_array_length]. *)

Local Lemma length_make' _n n x :
  isInt _n n →
  n <= max_array_length →
  isInt (length (make _n x)) n.
Proof.
  unfold isInt. intros. subst.
  assert ((of_nat n ≤? max_length)%uint63 = true) as Hbound.
  { rewrite leb_spec, max_length_spec. int. lia. }
  rewrite length_make, Hbound. eauto.
Qed.

(* The public specification of [make]. *)

Lemma wp_make _n n x :
  isInt _n n →
  n ≤ max_array_length →
  wp (make _n x) (λ a, isArray a (replicate n x)).
Proof.
  intros. eapply wp_ret.
  introIsArray; list; eauto using length_make' with int.
  intros i ?.
  rewrite get_make.
  rewrite lookup_total_replicate_2 by eauto.
  eauto.
Qed.

(* The public specification of [get]. *)

Lemma wp_get _i i a xs :
  isInt _i i →
  isArray a xs →
  valid i xs →
  wp a.[_i] (λ x, x = xs !!! i).
Proof.
  (* Easy, because the definition of [isArray] relies on [get]. *)
  intros. destructIsArray. repeat destructIsInt. eapply wp_ret. eauto.
Qed.

(* The public specification of [set]. *)

Lemma wp_set _i i a xs x :
  isInt _i i →
  isArray a xs →
  valid i xs →
  wp a.[_i <- x] (λ a', isArray a' (<[i := x]>xs)).
Proof.
  intros. eapply wp_ret. introIsArray; list.
  { rewrite length_set. eauto using isArray_length_spec. }
  { eauto with lia. }
  intros j ?. liftIsIntAndClear.
  destruct (decide (i = j)).
  + subst j.
    rewrite list_lookup_total_insert_eq by eauto.
    rewrite get_set_same.
    { eauto. }
    { Fail eapply isArray_use_valid. (* TODO why does this fail? *)
      simple eapply isArray_use_valid; eauto. }
  + rewrite list_lookup_total_insert_ne by eauto.
    rewrite get_set_other by eauto 10 using of_nat_inj' with representable.
    erewrite isArray_pi3 by eauto.
    eauto.
Qed.

(* The public specification of [length]. *)

(* See also [isArray_length_spec]. *)

Lemma wp_length a xs :
  isArray a xs →
  wp (length a) (λ _n,
    isInt _n (List.length xs) ∧
    representable (List.length xs)
  ).
Proof.
  intros. eapply wp_ret.
  eauto using isArray_length_spec with representable.
Qed.

End PrimSpec.

(* The following tactics help use the above specifications. *)

(* In each case, we try applying [wp_bind] first; if this does
   not work then we try applying the operation's specification
   directly; if this does not work then we use [wp_conseq] first. *)

Global Ltac wp_length_nude :=
  simple eapply wp_length; eauto.

Global Ltac wp_length_intros n :=
  let Hn := fresh in
  simpl; intros n Hn;
  list in Hn;
  destruct Hn as [? ?].

Global Ltac wp_length_bind n :=
  eapply wp_bind; [ wp_length_nude | wp_length_intros n ].

Global Ltac wp_length n :=
  first [
    wp_length_bind n
  | wp_length_nude
  | eapply wp_conseq; [ wp_length_nude | wp_length_intros n ]
  ].

Global Ltac wp_get_nude :=
  simple eapply wp_get; eauto with int lia.

Global Ltac wp_get_intros x :=
  let Hx := fresh in
  simpl; intros x Hx;
  list in Hx.

Global Ltac wp_get_bind x :=
  eapply wp_bind; [ wp_get_nude | wp_get_intros x ].

Global Ltac wp_get x :=
  first [
    wp_get_bind x
  | wp_get_nude
  | eapply wp_conseq; [ wp_get_nude | wp_get_intros x ]
  ].

Global Ltac wp_set_nude :=
  simple eapply wp_set; eauto with int lia.

Global Ltac wp_set_intros a :=
  let Ha := fresh in
  simpl; intros a Ha;
  list in Ha.

Global Ltac wp_set_bind a :=
  match goal with
  |- wp (@bind _ _ (set ?a0 ?i ?x) _) ?Q =>
    eapply wp_bind; [
      wp_set_nude
    | wp_set_intros a;
      (* Forget about the previous array, and rename the new array
         using the name of the previous array. Thus we keep only one
         copy at hand in the course of a proof. *)
      clear dependent a0; rename a into a0
    ]
  end.

Global Ltac wp_set a :=
  first [
    wp_set_bind a
  | wp_set_nude
  | eapply wp_conseq; [ wp_set_nude | wp_set_intros a ]
  ].

Global Ltac wp_make_nude :=
  simple eapply wp_make; eauto with int lia.

Global Ltac wp_make_intros b :=
  simpl; intros b ?.

Global Ltac wp_make_bind b :=
  eapply wp_bind; [ wp_make_nude | wp_make_intros b ].

Global Ltac wp_make b :=
  first [
    wp_make_bind b
  | wp_make_nude
  | eapply wp_conseq; [ wp_make_nude | wp_make_intros b ]
  ].

(* TODO can we reduce the boilerplate that is needed for each tactic? *)

(* -------------------------------------------------------------------------- *)

(* The tactic [isArray] is applicable when the goal is [isArray a ys]
   and there is a hypothesis [isArray a xs]. The goal is then reduced
   to the equation [xs = ys], and this equation is simplified. If the
   equation is trivial then the goal is solved. *)

Global Ltac isArray :=
  match goal with
  | h: isArray ?a ?xs |- isArray ?a ?ys =>
    cut (xs = ys); [
      let Heq := fresh in intro Heq; try rewrite <- Heq; exact h
    | clear h; simplify_list_equality_goal; eauto
    ]
  end.

(* -------------------------------------------------------------------------- *)

(* Converting an array to a list: [to_list]. *)

Section ToList.
Context `{Inhabited A}.
Implicit Types a : array A.
Implicit Types xs : list A.

(* The code. *)

Definition to_list a :=
  (* Obtain the length [n] of the array. *)
  do _n ← length a ;
  (* For [i] ranging from [n-1] down to 0,
     with a running state [xs], which is initially empty, *)
  down _n [] @@ λ _i xs,
  (* Read the [i]-th element of the array [a], *)
  do x ← a.[_i] ;
  (* and prepend it in front of [xs]. *)
  x :: xs.

(* One public specification of [to_list]. *)

(* This specification is based on the specifications of [length] and [get]
   that were given above. Because of this, the proposition [isArray a xs]
   appears in the precondition of [to_list]. A stronger specification is
   given later on. *)

Lemma wp_to_list a xs :
  isArray a xs →
  wp (to_list a) (λ xs', xs' = xs).
Proof.
  (* This proof relies on the lemmas [wp_length] and [wp_get].
     It does not need to unfold the definition of [isArray]. *)
  intro. unfold to_list.
  wp_length _n.
  (* The loop invariant. *)
  set (inv := λ i ys, ys = drop i xs).
  eapply wp_down with (inv := inv); eauto; unfold inv; intros.
  (* Initialization. *)
  { rewrite drop_all. eauto. }
  (* Preservation. *)
  { wp_get x.
    eapply wp_ret.
    subst. rewrite drop_S' by eauto.
    eauto. }
Qed.

(* A second (stronger) public specification of [to_list]. *)

(* In this specification, the proposition [isArray a xs] appears in the
   postcondition. The precondition is trivial: there is none. *)

Lemma wp_to_list' a :
  wp (to_list a) (λ xs, isArray a xs).
Proof.
  (* This proof is based directly on the definition of [isArray a xs].
     It does not rely on the lemmas [wp_length] and [wp_get]. *)
  intros. unfold to_list.
  (* Obtain the length of the array. *)
  eapply wp_bind_eq. intros _n ?.
  set (n := to_nat _n).
  assert (isInt _n n) by eauto using introIsInt'.
  assert (n ≤ max_array_length) by (subst n _n; eauto with representable).
  assert (representable n) by eauto with representable.
  (* The loop invariant: when the loop index is [i] and the state is [xs],
     the length of [xs] is [n - i] and the elements of [xs] are the elements
     found at indices [i, n) in the array [a]. *)
  set (inv := λ i (ys : list A),
    List.length ys = n - i ∧
    ∀ j, i ≤ j < n → a.[of_nat j] = ys !!! (j - i)
  ).
  eapply wp_down with (inv := inv); eauto; unfold inv; list; intros.
  (* Initialization. *)
  { split; intros; lia. }
  (* Preservation. *)
  { rename s into xs.
    match goal with h: _ ∧ _ |- _ => destruct h as [Hxs Hlookup] end.
    liftIsIntAndClear.
    eapply wp_bind_eq. intros x ->.
    eapply wp_ret.
    list; split; [ lia |].
    intros j ?.
    destruct (decide (i = j)); [ subst j |]; list.
    { eauto. }
    { rewrite Hlookup by lia. f_equal. lia. } }
  (* Completion. *)
  { rename s into xs.
    match goal with h: _ ∧ _ |- _ => destruct h as [Hxs Hlookup] end.
    introIsArray; try rewrite Hxs.
    + introIsInt. subst n. int. eauto.
    + eauto.
    + intros j ?. rewrite Hlookup by lia. list. eauto. }
Qed.

(* [isArray a xs] is equivalent to [to_list a = xs]. *)

Lemma isArray_iff a xs :
  isArray a xs ↔
  to_list a = xs.
Proof.
  intros.
  generalize (wp_to_list' a); intro fact.
  rewrite wp_iff in fact.
  split; intros; subst; eauto using isArray_inj_2.
Qed.

End ToList.

(* -------------------------------------------------------------------------- *)

(* [list_iteri] iterates on a list, from left to right,
   with a running index of type [int]
   and a running state of type [S]. *)

Section ListIteri.
Context {S A : Type}.
Implicit Types s : S.
Implicit Types xs : list A.
Implicit Types f : S → int → A → S.
Implicit Types inv : S → list A → Prop.

(* The code. *)

Fixpoint list_iteri f s _i xs :=
  match xs with
  | [] =>
      s
  | x :: xs =>
      do s ← f s _i x ;
      list_iteri f s (_i + 1) xs
  end.

(* An inductive specification. (This is just an auxiliary lemma.) *)

(* The user-provided loop invariant [inv s history] is parameterized with the
   current state [s] and the already-visited elements [history]. It does not
   need to be parameterized with the current index [i], because it is just the
   length of the list [history]. *)

Local Lemma wp_list_iteri_aux f inv xs :
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
  wp (list_iteri f s _i future) (λ s, inv s xs).
Proof.
  induction future as [| x future ];
  intros ??? HI Hinv Hxs Hpreservation;
  simpl list_iteri.
  { list in Hxs. subst history. eapply wp_ret. eauto. }
  { eapply wp_bind.
    { eapply Hpreservation; eauto using prefix_cons, prefix_nil. }
    simpl. intros s' Hs'.
    eapply IHfuture with (history := history ++ [x]);
      list; eauto with int. }
Qed.

(* The public specification of [list_iteri]. *)

Lemma wp_list_iteri f xs Q inv s :
  (* Initialization. The invariant must be true of the initial state [s]
     and the empty history. *)
  inv s [] →
  (* Preservation. If the invariant holds of the current state [s] and
     current history [history], if the index [_i] represents the length
     of the list [history], and if [x] is the first unvisited element of
     the list [xs], then the function call [f s _i x] must return a new
     state [s] such that the invariant holds of the state [s] and of the
     new history [history ++ [x]]. *)
  ( ∀ s history _i x,
    isInt _i (List.length history) →
    inv s history →
    history ++ [x] `prefix_of` xs →
    wp (f s _i x) (λ s, inv s (history ++ [x]))
  ) →
  (* Completion. The invariant, applied to the final state [s] and to
     the complete list [xs], must imply the postcondition [Q]. *)
  (∀ s, inv s xs → Q s) →
  (* Under these three hypotheses, the loop establishes [Q]. *)
  wp (list_iteri f s 0 xs) Q.
Proof.
  intros Hinv Hpreservation Hcompletion.
  eapply wp_conseq.
  { eapply wp_list_iteri_aux; eauto; list; eauto with int.
   intros. subst. eauto using prefix_app. }
  { simpl. eauto. }
Qed.

End ListIteri.

(* -------------------------------------------------------------------------- *)

(* [list_length] computes the length of a list, as a machine integer. *)

Section ListLength.
Context {A : Type}.
Implicit Types xs : list A.

(* The code. *)

Fixpoint list_length_aux _s xs : int :=
  match xs with [] => _s | _ :: xs => list_length_aux (_s + 1) xs end.

Definition list_length xs : int :=
  list_length_aux 0 xs.

(* A specification of [list_length_aux]. *)

Local Lemma wp_list_length_aux xs : ∀ _s s,
  isInt _s s →
  wp (list_length_aux _s xs) (λ _i, isInt _i (s + List.length xs)).
Proof.
  induction xs as [| x xs ]; simpl; intros.
  { eapply wp_ret. list. eauto. }
  { eapply wp_conseq; [ eauto with int | simpl ].
    rewrite <- Nat.add_assoc. eauto. }
Qed.

(* The public specification of [list_length]. *)

Lemma wp_list_length xs :
  wp (list_length xs) (λ _i, isInt _i (List.length xs)).
Proof.
  eapply wp_conseq.
  { eapply wp_list_length_aux; eauto with int. }
  { simpl. eauto. }
Qed.

End ListLength.

Ltac wp_list_length _n :=
  eapply wp_bind; [
    eapply wp_list_length
  | simpl; intros _n ?
  ].

(* -------------------------------------------------------------------------- *)

(* Converting a list to an array: [of_list]. *)

Section OfList.
Context `{Inhabited A}.
Implicit Types a : array A.
Implicit Types xs history : list A.

(* The code. *)

Definition of_list xs :=
  (* Compute the length [n] of the list. *)
  do _n ← list_length xs ;
  (* Allocate an array of size [n]. *)
  do a ← make _n inhabitant ;
  (* Initialize the array by iterating on the list. *)
  list_iteri set a 0 xs.

(* The public specification of [of_list]. *)

(* There is no protection against integer overflow in [list_length]
   or [list_iteri]. Instead, a bound on the length of the list [xs]
   is imposed as a precondition in this specification. *)

Lemma wp_of_list xs :
  List.length xs ≤ max_array_length →
  wp (of_list xs) (λ a, isArray a xs).
Proof.
  intros. unfold of_list.
  wp_list_length _n.
  eapply wp_bind.
  { Fail eapply wp_make. (* TODO why does this fail? *)
    simple eapply wp_make; eauto. }
  simpl. intros a ?.
  (* The loop invariant. *)
  set (n := List.length xs).
  set (inv := λ a history,
    let h := List.length history in
    isArray a (history ++ replicate (n-h) inhabitant)
  ).
  eapply wp_list_iteri with (inv := inv); unfold inv; list; eauto.
  (* Preservation. *)
  { intros. apply_prefix_length. wp_set s'. list. eauto. }
Qed.

End OfList.

(* -------------------------------------------------------------------------- *)

(* A round-trip property: [to_list . of_list] is the identity. *)

(* This is true only of sufficiently short lists. *)

Lemma to_list_of_list `{Inhabited A} (xs : list A) :
  List.length xs ≤ max_array_length →
  to_list (of_list xs) = xs.
Proof.
  intros.
  cut (
    wp (
      do a ← of_list xs ;
      do ys ← to_list a ;
      ys
    ) (λ ys, xs = ys)
  ).
  { rewrite wp_iff. eauto. }
  eapply wp_bind; [ eapply wp_of_list; eauto | simpl; intros a ? ].
  eapply wp_bind; [ eapply wp_to_list; eauto | simpl; intros ? ->].
  eapply wp_ret. eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Some tests of [to_list . of_list]. *)

(* This test shows that [Eval compute] is unable to properly evaluate
   a call to [down_aux]. I don't know whether this is normal. TODO *)
(* Eval    compute in to_list (of_list [1;2;3]). *)

(* This test shows that [Eval vm_compute] works as desired. *)
(* Eval vm_compute in to_list (of_list [1;2;3]). *)

(* This test shows that [Eval native_compute] works as desired. *)
(* TODO native_compute must be configured at installation time; how? *)
(* Eval vm_compute in to_list (of_list [1;2;3]). *)

(* -------------------------------------------------------------------------- *)

(* The reverse round-trip property, [of_list . to_list = id], cannot be
   naively stated using equality of arrays, as follows:

     of_list (to_list a) = a

   Indeed, the two arrays on either side of this equation must contain the
   same elements, but could have different default elements.

   To work around this problem, one approach would be to add a side
   condition regarding the default element:

     default a = inhabitant → of_list (to_list a) = a

   This statement should be true, but its proof would be painful, because
   the proposition [isArray a xs] does not constrain the default element of
   the array [a]. The specifications of the operations on arrays that we
   have given are expressed in terms of [isArray], so we have no easy way of
   recording and maintaing information about the default element. This is a
   deliberate decision; most of the time, we do not care about the default
   element, and do not wish to keep track of it.

   Another work-around is to state the round-trip property in terms of a
   coarser notion of extensional equality on arrays, which compares the
   elements of the arrays and does not compare their default elements. *)

(* This problem is related with the statement of the lemma [isArray_inj_1],
   where the side condition [default a = default b] is needed in order to
   conclude [a = b]. *)

(* For the moment, we do nothing, and hope that we can live without this
   round-trip property. *)

(* -------------------------------------------------------------------------- *)

(* Copying data from an array to another array: [blit]. *)

Section Blit.
Context `{Inhabited A}.
Implicit Types a b : array A.
Implicit Types xs ys : list A.

(* The code. *)

(* Please note: to obtain the desired performance, the arrays [a] and
   [b] must be two *independent* arrays; that is, they should not be
   two persistent arrays that are backed by the same underlying
   physical array. *)

Definition blit a _i b _j _n :=
  up _i (_i + _n)%uint63 b @@ λ _k b,
  do x ← get a _k ;
  do b ← set b (_j + (_k - _i))%uint63 x ;
  b.

(* The public specification of [blit]. *)

Lemma wp_blit a xs _i i b ys _j j _n n :
  isArray a xs →
  isInt _i i →
  isArray b ys →
  isInt _j j →
  isInt _n n →
  valid_seg i (i + n) xs →
  valid_seg j (j + n) ys →
  wp (blit a _i b _j _n) (λ b, isArray b
    (initial_seg j ys ++ sub i n xs ++ final_seg (j + n) ys)
  ).
Proof.
  intros. unfold blit.
  eapply wp_up with (inv := λ k b,
    isArray b
      (initial_seg j ys ++ seg i k xs ++ final_seg (j + (k - i)) ys)
  );
  eauto with int representable lia; list; eauto 1.
  (* Preservation. *)
  { clear dependent b. intros _k k b. intros.
    wp_get x. subst x.
    wp_set b'.
    wp_ret. isArray. }
Qed.

End Blit.

(* TODO more boilerplate! *)

Global Ltac wp_blit_nude :=
  eapply wp_blit; eauto with int lia; (list; lia).

Global Ltac wp_blit_intros b :=
  wp_set_intros b. (* shortcut *)

Global Ltac wp_blit_bind b :=
  match goal with
  |- wp (@bind _ _ (blit ?a ?i ?b0 ?j ?n) _) ?Q =>
    eapply wp_bind; [
      wp_blit_nude
    | wp_blit_intros b;
      (* Forget about the previous array, and rename the new array
         using the name of the previous array. Thus we keep only one
         copy at hand in the course of a proof. *)
      clear dependent b0; rename b into b0
    ]
  end.

Global Ltac wp_blit b :=
  first [
    wp_blit_bind b
  | wp_blit_nude
  | eapply wp_conseq; [ wp_blit_nude | wp_blit_intros b ]
  ].

(* -------------------------------------------------------------------------- *)

(* Creating a fresh copy of an array: [copy]. *)

Section Copy.
Context `{Inhabited A}.
Implicit Types a b : array A.
Implicit Types xs ys : list A.

(* The code. *)

Definition copy a :=
  do _n ← length a ;
  do b ← make _n inhabitant ;
  do b ← blit a 0 b 0 _n ;
  b.

(* The public specification of [copy]. *)

Lemma wp_copy a xs :
  isArray a xs →
  wp (copy a) (λ b, isArray b xs).
Proof.
  intros. unfold copy.
  wp_length n.
  wp_make b.
  wp_blit b'. (* TODO avoid naming [b'] for no reason *)
  wp_ret. isArray.
Qed.

End Copy.

(* -------------------------------------------------------------------------- *)

(* Extracting a segment of an array: [sub]. *)

Section Sub.
Context `{Inhabited A}.
Implicit Types a b : array A.
Implicit Types xs ys : list A.

(* The code. *)

Definition sub a _i _n :=
  do b ← make _n inhabitant ;
  do b ← blit a _i b 0 _n ;
  b.

(* The public specification of [sub]. *)

Lemma wp_sub a _i i _n n xs :
  isArray a xs →
  isInt _i i →
  isInt _n n →
  valid_seg i (i + n) xs →
  wp (sub a _i _n) (λ b, isArray b (list_extra.sub i n xs)).
  (* TODO name clash on [sub] *)
Proof.
  intros. unfold sub.
  wp_make b.
  wp_blit b'.
  wp_ret. isArray.
Qed.

End Sub.
