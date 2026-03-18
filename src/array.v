From stdpp Require Import numbers list.
Notation len := List.length.
From Stdlib Require Import Uint63.
From Stdlib Require Import Array.PArray.
From marble Require Import tactics list_extra bool iteration int wp wp_tactics.
Implicit Types _i _j _k _n : int.

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

Definition max_array_length_def : nat :=
  to_nat max_length.

  (* Without sealing, making [max_length_spec] an instance slows down
     [eauto with typeclass_instances] in an unbearable way. *)

  Local Definition max_array_length_aux : seal (@max_array_length_def).
  Proof. by eexists. Qed.
  Definition max_array_length := max_array_length_aux.(unseal).
  Local Definition max_array_length_unseal :
    @max_array_length = @max_array_length_def := max_array_length_aux.(seal_eq).

  Local Ltac max_array_length_def :=
    rewrite max_array_length_unseal;
    unfold max_array_length_def.

(* These constants are related by [isInt]. *)

Global Instance max_length_spec :
  isInt max_length max_array_length.
Proof.
  introIsInt. max_array_length_def. int. eauto.
Qed.

(* [max_array_length] is representable. *)

Lemma representable_max_array_length :
  representable max_array_length.
Proof.
  rewrite representable_iff_Z. split; [ lia |].
  (* (Z.of_nat max_array_length < wB)%Z *)
  max_array_length_def. int.
  (* (φ%uint63 max_length < wB)%Z *)
  reflexivity.
Qed.
  (* We do not make this lemma an Instance because the more powerful
     lemma [representable_le_max_array_length] follows. *)

(* [2 * max_array_length] is still representable. *)

Lemma representable_twice_max_array_length :
  representable (2 * max_array_length).
Proof.
  (* This proof should work for larger constants as well. *)
  max_array_length_def.
  assert (∀ x : Z, 0 ≤ x → 0 ≤ 2 * x)%Z by lia.
  rewrite representable_iff_Z.
  change 2 with (Z.to_nat 2).
  rewrite <- Z2Nat.inj_mul by eauto with lia.
  int.
  (* The goal is now an inequality in Z. *)
  (* To my surprise, computation in Z solves this goal. *)
  compute. split; congruence.
Qed.

(* [max_array_length] is not ridiculously small. *)

Lemma max_array_length_is_large :
  1024 < max_array_length.
Proof.
  (* This proof will work for any constant that really is less
     than [max_array_length]. *)
  max_array_length_def.
  change 1024 with (to_nat 1024).
  rewrite <- Z2Nat.inj_lt by eauto with lia.
  rewrite <- ltb_spec.
  reflexivity.
Qed.

(* Any number that is bounded by [max_array_length] is representable. *)

Global Instance representable_le_max_array_length n :
  n ≤ max_array_length → representable n.
Proof.
  eauto using representable_max_array_length with typeclass_instances.
  (* [eauto with typeclass_instances] would be unable to solve this goal,
     even if we made [representable_max_array_length] an Instance, because
     that would require guessing [?i := max_array_length] in a subgoal of
     the form [representable ?i]. We have used [Hint Mode] to forbid such
     guessing. *)
Qed.

(* The length of an array, converted to a natural number,
   is bounded by [max_array_length]. *)

Local Lemma leb_length' {A} (a : array A) :
  to_nat (length a) <= max_array_length.
Proof.
  generalize (leb_length _ a).
  rewrite leb_spec.
  rewrite max_length_spec. (* rewriting through [isInt] *)
  max_array_length_def.
  rewrite of_nat_to_nat. (* [int] takes 10 seconds *)
  lia.
Qed.

(* The length of an array is representable. *)

Local Lemma representable_to_nat_length {A} (a : array A) :
  representable (to_nat (length a)).
Proof.
  eapply representable_down_closed; [| eapply leb_length' ].
  tc.
Qed.

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
  let n := len xs in
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
  isInt (length a) (len xs).
Proof.
  intros. destructIsArray. eauto.
Qed.

Lemma isArray_bounded_length `{Inhabited A} (a : array A) (xs : list A) :
  isArray a xs →
  len xs ≤ max_array_length.
Proof.
  intros. destructIsArray. eauto.
Qed.

Lemma isArray_bounded_length' `{Inhabited A} (a : array A) (xs : list A) :
  ∀ n,
  isArray a xs →
  n ≤ len xs →
  n ≤ max_array_length.
Proof.
  intros. destructIsArray. lia.
Qed.

Global Hint Resolve
  isArray_bounded_length'
: lia.

Global Instance isArray_representable `{Inhabited A} (a : array A) xs :
  isArray a xs →
  representable (len xs).
Proof.
  intros. destructIsArray. tc.
Qed.

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
  assert (len xs = len ys).
  { eauto 6 using isInt_inj_2, isArray_length_spec with typeclass_instances. }
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
  rewrite !isInt_def. intros. subst.
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
  intros. wp_ret.
  introIsArray; list; eauto using length_make'.
  intros i ?.
  rewrite get_make. list. eauto.
Qed.

(* The public specification of [get]. *)

Lemma wp_get _i i a xs :
  isInt _i i →
  isArray a xs →
  valid i xs →
  wp a.[_i] (λ x, x = xs !!! i).
Proof.
  (* Easy, because the definition of [isArray] relies on [get]. *)
  intros. destructIsArray. repeat destructIsInt. wp_ret. eauto.
Qed.

(* The public specification of [set]. *)

Lemma wp_set _i i a xs x :
  isInt _i i →
  isArray a xs →
  valid i xs →
  wp a.[_i <- x] (λ a', isArray a' (<[i := x]>xs)).
Proof.
  intros. wp_ret. introIsArray; list.
  { rewrite length_set. eauto using isArray_length_spec. }
  { eauto with lia. }
  intros j ?. liftIsIntAndClear.
  destruct (decide (i = j)); [ subst j |]; list.
  + rewrite get_set_same by eauto using isArray_use_valid.
    eauto.
  + rewrite get_set_other by eauto 10 using of_nat_inj' with typeclass_instances lia.
    erewrite isArray_pi3 by eauto.
    eauto.
Qed.

(* The public specification of [length]. *)

(* See also [isArray_length_spec]. *)

Lemma wp_length a xs :
  isArray a xs →
  wp (length a) (λ _n,
    isInt _n (len xs) ∧
    representable (len xs)
  ).
Proof.
  intros. wp_ret.
  eauto using isArray_length_spec with typeclass_instances.
Qed.

End PrimSpec.

(* The following tactics help use the above specifications. *)

Global Ltac wp_length n :=
  wp_op wp_length n.

Global Ltac wp_get x :=
  wp_op wp_get x.

Global Ltac wp_set :=
  match goal with |- context[set ?a _ _] =>
    wp_op_overwrite wp_set a
  end.

Global Ltac wp_make a :=
  wp_op wp_make a.

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

(* Converting an array segment to a list: [segment_to_list]. *)

(* Converting an array to a list: [to_list]. *)

Section ToList.
Context `{Inhabited A}.
Implicit Types a : array A.
Implicit Types xs : list A.

(* The code. *)

Definition segment_to_list a _i _k :=
  (* For [_j] ranging from [_k] down to [_i],
     with running state [xs], initially empty, *)
  int.iter_down _k _i [] @@ λ _j xs,
  (* Read the [_j]-th element of the array [a], *)
  do x ← a.[_j] ;
  (* and prepend it in front of [xs]. *)
  x :: xs.

Definition to_list a :=
  (* Obtain the length [n] of the array. *)
  do _n ← length a ;
  (* Convert all of the array to a list. *)
  segment_to_list a 0 _n.

(* A specification of [segment_to_list],
   and a first specification of [to_list]. *)

(* This specification is based on the specifications of [length] and [get]
   that were given above. Because of this, the proposition [isArray a xs]
   appears in the precondition of [to_list]. A stronger specification of
   [to_list] is given later on. *)

Lemma wp_segment_to_list a xs :
  isArray a xs →
  ∀Int _i i ,
  ∀Int _k k ,
  valid_seg i k xs →
  wp (segment_to_list a _i _k) (λ xs', xs' = seg i k xs).
Proof.
  (* This proof relies on the lemmas [wp_length] and [wp_get].
     It does not need to unfold the definition of [isArray]. *)
  intros. unfold segment_to_list.
  (* The loop invariant. *)
  int.wp_iter_down (λ j ys, ys = seg j k xs).
  (* Preservation. *)
  { wp_down_intros _j j xs'.
    wp_get x.
    wp_ret. subst.
    rewrite cons_is_append. list. eauto. }
Qed.

Lemma wp_to_list a xs :
  isArray a xs →
  wp (to_list a) (λ xs', xs' = xs).
Proof.
  intro. unfold to_list.
  wp_length _n.
  wp_op wp_segment_to_list xs'.
  eauto.
Qed.

(* A second (stronger) specification of [to_list]. *)

(* In this specification, the proposition [isArray a xs] appears in the
   postcondition. The precondition is trivial: there is none. *)

(* It is not clear whether a specification of [segment_to_list] in this
   style can be given. The proposition [isArray a _] in the postcondition
   would then be able to describe just a segment of the array. Therefore
   an existential quantification would be required to describe the two
   unknown segments of the array. That would be strange and perhaps not
   very useful. *)

Lemma wp_to_list' a :
  wp (to_list a) (λ xs, isArray a xs).
Proof.
  (* This proof is based directly on the definition of [isArray a xs].
     It does not rely on the lemmas [wp_length] and [wp_get]. *)
  intros. unfold to_list, segment_to_list.
  (* Obtain the length of the array. *)
  eapply wp_bind_eq. intros _n ?.
  set (n := to_nat _n).
  assert (isInt _n n) by eauto using introIsInt.
  assert (n ≤ max_array_length).
  { subst n _n. simple eapply leb_length'. }
  assert (representable n) by tc.
  (* The loop invariant: when the loop index is [j] and the state is [ys],
     the length of [ys] is [n - j] and the elements of [ys] are the elements
     found at indices [j, n) in the array [a]. *)
  int.wp_iter_down (λ j ys,
    len ys = n - j ∧
    ∀ o, j ≤ o < n → a.[of_nat o] = ys !!! (o - j)
  ).
  (* Preservation. *)
  { wp_down_intros _j j ys.
    liftIsIntAndClear.
    wp_bind_eq.
    wp_ret.
    list; split; [ lia |].
    rewrite cons_is_append.
    intros o ?.
    destruct (decide (j = o)); [ subst o |]; list.
    { eauto. }
    { replace (o - j - 1) with (o - (j + 1)) by lia.
      eauto with lia. } }
  (* Completion. *)
  { (* TODO avoid this *)
    match goal with h: len ?s = _ |- _ =>
    rename s into xs; rename h into Hxs end.
    introIsArray; try rewrite Hxs.
    + introIsInt. subst n. int. eauto.
    + eauto.
    + intros o ?.
      replace o with (o - 0) at 2 by lia.
      eauto with lia. }
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

(* It is usually invoked with start index 0,
   but we do not define a helper function for this. *)

Section ListIteri.
Context {S A : Type}.
Implicit Types s : S.
Implicit Types xs : list A.
Implicit Types f : S → int → A → S.

(* The code. *)

Fixpoint list_iteri _i xs s f :=
  match xs with
  | [] =>
      s
  | x :: xs =>
      do s ← f s _i x ;
      list_iteri (_i + 1) xs s f
  end.

(* An inductive specification. (This is an auxiliary lemma.) *)

(* The user-provided loop invariant [inv history s] is parameterized
   with the already-visited elements [history] and the current user
   state [s]. It does not need to be parameterized with the current
   index [i], because [i] is just the length of the list [history]. *)

Local Lemma wp_list_iteri_aux xs f :
  ∀ future history _i ,
  xs = history ++ future →
  isInt _i (len history) →
  ITERI_LIST
    history xs
    (λ x i s Q, ∀ _i, isInt _i i → wp (f s _i x) Q)
    (λ s Q, wp (list_iteri _i future s f) Q).
(* Extend [tc] with hints for this proof. *)
Local Hint Extern 1 (_ `prefix_of` _) =>
  (econstructor; list; reflexivity) : typeclass_instances.
Local Hint Extern 1 (_ ++ _ ++ ?xs = _ ++ ?xs) =>
  (rewrite app_assoc; f_equal) : typeclass_instances.
Local Hint Resolve prefix_app_l : typeclass_instances.
Proof.
  induction future as [| x future ]; simpl list_iteri; intros;
  ITER; subst xs; list in *; lengths.
  (* Case: the future is empty. *)
  { wp_ret. eauto. }
  (* Case: the future begins with [x]. *)
  { rewrite cons_is_append in *.
    wp_op Hstep s'.
    eapply IHfuture; tc; list; tc. }
Qed.

(* The public specification of [list_iteri]. *)

Lemma wp_list_iteri xs s f :
  ITERI_LIST
    [] xs
    (λ x i s Q, ∀ _i, isInt _i i → wp (f s _i x) Q)
    (λ s Q, wp (list_iteri 0 xs s f) Q).
Proof.
  unfold ITERI_LIST. eapply wp_list_iteri_aux; tc.
Qed.

End ListIteri.

(* In the following section, we play with two alternate specifications
   of [list_iteri]. Insteead of using [ITER_LIST], where the producer
   state is a list (the history of past elements), we use [ITER_NAT_UP],
   where the producer state is an integer index, and we indicate that
   the user function receives the [i]-th element of the list as an
   argument during the [i]-th iteration of the loop. *)

Section Attic.
Context {S : Type}.
Context `{Inhabited A}.
Implicit Types s : S.
Implicit Types xs : list A.
Implicit Types f : S → int → A → S.

(* In this variant, we keep the decomposition [xs = history ++ future]. *)

Local Lemma wp_list_iteri_aux_variant_1 f :
  ∀ future history xs _i i ,
  xs = history ++ future →
  isInt _i i →
  i = len history →
  ITER_NAT
    i (len xs) Up
    (λ j s Q, ∀ _j, isInt _j j → ∀ x, x = xs !!! j → wp (f s _j x) Q)
    (λ s Q, wp (list_iteri _i future s f) Q).
Proof.
  expand_ITER.
  induction future as [| x future ];
  intros history xs _i i ? ? ?;
  ITER;
  simpl list_iteri; try rewrite cons_is_append in *;
  subst; list in *.
  { wp_ret. eauto. }
  { wp_op Hstep s'.
    (* The system cannot guess how we want to extend the history
       because any history of length [len history + 1] will do! *)
    eapply wp_conseq.
    - eapply IHfuture with (history := history ++ {[x]});
      list; tc3; list; tc3.
    - wp_loop_exit. }
Qed.

(* In this variant, we get rid of [history] and we keep track only
   of the equation [final_seg i xs = future], which means that the
   future is the segment of [xs] that begins at index [i]. *)

(* This specification is just as concise as the previous one, but
   the proof is slightly longer, as I am unable to automate the use
   of the lemmas [lookup_total_through_seg] and [seg_through_seg]. *)

Local Lemma wp_list_iteri_aux_variant_2 xs f :
  ∀ future _i i ,
  isInt _i i →
  i ≤ len xs →
  final_seg i xs = future →
  ITER_NAT
    i (len xs) Up
    (λ j s Q, ∀ _j, isInt _j j → ∀ x, x = xs !!! j → wp (f s _j x) Q)
    (λ s Q, wp (list_iteri _i future s f) Q).
Proof.
  expand_ITER.
  induction future as [| x future ];
  intros _i i ? ? ?;
  ITER;
  simpl list_iteri; try rewrite cons_is_append in *;
  subst; list in *; lengths.
  (* Case: the future is empty. We have [i = len xs]. *)
  { assert (i = len xs) by lia. subst.
    wp_ret. eauto. }
  (* Case: the future begins with [x]. We have [i < len xs]. *)
  { assert (x = xs !!! i).
    { erewrite lookup_total_through_seg by eauto with lia. list. eauto. }
    assert (final_seg (i + 1) xs = future).
    { erewrite seg_through_seg by eauto with lia. list. eauto. }
    wp_op Hstep s'.
    eapply wp_conseq.
    - eapply IHfuture; list; tc3; list; tc3.
    - wp_loop_exit. }
Qed.

End Attic.

(* -------------------------------------------------------------------------- *)

(* [list_length] computes the length of a list, as a machine integer. *)

Section ListLength.
Context {A : Type}.
Implicit Types xs : list A.

(* The code. *)

Fixpoint list_length_aux _n xs : int :=
  match xs with [] => _n | _ :: xs => list_length_aux (_n + 1) xs end.

Definition list_length xs : int :=
  list_length_aux 0 xs.

(* A specification of [list_length_aux]. *)

Local Lemma wp_list_length_aux xs : ∀ _n n,
  isInt _n n →
  wp (list_length_aux _n xs) (λ _i, isInt _i (n + len xs)).
Proof.
  induction xs as [| x xs ]; simpl; intros.
  { wp_ret. list. eauto. }
  { wp_op IHxs _n'.
    eauto. }
Qed.

(* The public specification of [list_length]. *)

Lemma wp_list_length xs :
  wp (list_length xs) (λ _i, isInt _i (len xs)).
Proof.
  unfold list_length.
  wp_op wp_list_length_aux _i.
  eauto.
Qed.

End ListLength.

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
  list_iteri 0 xs a set.

(* The public specification of [of_list]. *)

(* There is no protection against integer overflow in [list_length]
   or [list_iteri]. Instead, a bound on the length of the list [xs]
   is imposed as a precondition in this specification. *)

Lemma wp_of_list xs :
  len xs ≤ max_array_length →
  wp (of_list xs) (λ a, isArray a xs).
Proof.
  intros. unfold of_list.
  wp_op @wp_list_length _n.
  wp_make a.
  (* The loop invariant. *)
  wp_loop @wp_list_iteri (λ history a,
    isArray a (history ++ replicate (len xs - len history) inhabitant)
  ).
  (* Preservation. *)
  { clear dependent a.
    wp_loop_intros history0 history1 a.
    intros x i _; intros. subst history1. (* TODO tactic? *)
    lengths. wp_set. isArray. }
Qed.

End OfList.

(* -------------------------------------------------------------------------- *)

(* A round-trip property: [to_list . of_list] is the identity. *)

(* This is true only of sufficiently short lists. *)

Lemma to_list_of_list `{Inhabited A} (xs : list A) :
  len xs ≤ max_array_length →
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
  wp_op @wp_of_list a.
  wp_op @wp_to_list ys.
  wp_ret. eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Some tests of [to_list . of_list]. *)

(* This test shows that [compute] is unable to properly evaluate
   a call to [int.iter_down_aux]. I don't know whether this is normal. *)
Goal to_list (of_list [1;2;3]) = [1;2;3].
Proof. compute. Abort.

(* This test shows that [vm_compute] works as desired. *)
Goal to_list (of_list [1;2;3]) = [1;2;3].
Proof. vm_compute. reflexivity. Qed.

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
  int.iter_up _i (_i + _n)%uint63 b @@ λ _k b,
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
    (initial_seg j ys ++ seg i (i + n) xs ++ final_seg (j + n) ys)
  ).
Proof.
  intros. unfold blit.
  int.wp_iter_up (λ k b, isArray b
    (initial_seg j ys ++ seg i k xs ++ final_seg (j + (k - i)) ys)
  ).
  (* Preservation. *)
  { clear dependent b.
    wp_up_intros _k k b.
    wp_get x. subst x.
    wp_set.
    wp_ret. isArray. }
Qed.

End Blit.

Global Ltac wp_blit :=
  match goal with |- context[blit _ _ ?b _ _] =>
    wp_op_overwrite wp_blit b
  end.

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
  wp_blit.
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
  wp (sub a _i _n) (λ b, isArray b (seg i (i + n) xs)).
Proof.
  intros. unfold sub.
  wp_make b.
  wp_blit.
  wp_ret. isArray.
Qed.

End Sub.

(* -------------------------------------------------------------------------- *)

(* Concatenating two arrays: [append]. *)

Section Append.
Context `{Inhabited A}.
Implicit Types a b : array A.
Implicit Types xs ys : list A.

(* The code. *)

Definition append a b :=
  do _m ← length a ;
  do _n ← length b ;
  do c ← make (_m + _n)%uint63 inhabitant ;
  do c ← blit a 0 c 0 _m ;
  do c ← blit b 0 c _m _n ;
  c.

(* The public specification of [append]. *)

Lemma wp_append a xs b ys :
  isArray a xs →
  isArray b ys →
  len xs + len ys ≤ max_array_length →
  wp (append a b) (λ c, isArray c (xs ++ ys)).
Proof.
  intros. unfold append.
  wp_length _m.
  wp_length _n.
  wp_make c.
  wp_blit.
  wp_blit.
  wp_ret. isArray.
Qed.

End Append.

(* -------------------------------------------------------------------------- *)

(* Copying a value into an array segment: [fill]. *)

Section Fill.
Context `{Inhabited A}.
Implicit Types a b : array A.
Implicit Types xs ys : list A.

(* The code. *)

Definition fill a _i _n x :=
  int.iter_up _i (_i + _n)%uint63 a @@ λ _k a,
  do a ← set a _k x ;
  a.

(* The public specification of [fill]. *)

Lemma wp_fill a xs _i i _n n  x :
  isArray a xs →
  isInt _i i →
  isInt _n n →
  valid_seg i (i + n) xs →
  wp (fill a _i _n x) (λ a, isArray a
    (initial_seg i xs ++ replicate n x ++ final_seg (i + n) xs)
  ).
Proof.
  intros. unfold fill.
  int.wp_iter_up (λ k a, isArray a
    (initial_seg i xs ++ replicate (k - i) x ++ final_seg k xs)
  ).
  (* Preservation. *)
  { clear dependent a. wp_up_intros _k k a.
    wp_set.
    wp_ret. isArray. }
Qed.

End Fill.

Global Ltac wp_fill :=
  match goal with |- context[fill ?a _ _ _] =>
    wp_op_overwrite wp_fill a
  end.

(* -------------------------------------------------------------------------- *)

(* Searching for an element in an array: [find_index]. *)

Section FindIndex.
Context `{Inhabited A}.
Implicit Types a : array A.
Implicit Types xs : list A.
Implicit Types s : unit.
Implicit Types o : option int.

Variable f : A → bool.

(* The code. *)

Definition find_index a : outcome int :=
  do _n ← length a ;
  int.uxiter_up 0 _n @@ λ _ _i continue break,
  do x ← get a _i ;
  if f x then break _i else continue ().

(* Our hypothesis about [f]. *)

(* If no specification of [f] in terms of [isBool] is available, then one
   can pick [OK := λ x, f x = true] and [notOK := λ x, f x = false]. Then
   the hypothesis [f_spec] is trivially satisfied. *)

Variable     OK : A → bool.
Variable  notOK : A → bool.
Variable f_spec :
  ∀ x, isBool (f x) (OK x) (notOK x).

(* The proposition [find_index_inv xs n out] serves to describe both
   the postcondition of [find_index] and its loop invariant. Here is
   its statement: *)

Definition find_index_inv xs n out :=
  match out with
  | Continue =>
      (* Up to index [n], no element [x] of the list [xs] is OK. *)
      ∀ j, j < n → notOK (xs !!! j)
  | Break _i =>
      (* The machine integer [_i] represents the index [i], which is a
         valid index into the list [xs]; the element [x] found at this
         index is OK; and no earlier element is OK. *)
      ∃ i , isInt _i i ∧ valid i xs ∧ OK (xs !!! i) ∧
      ∀ j, j < i → notOK (xs !!! j)
  end.

(* The public specification of [find_index]. *)

Lemma wp_find_index a xs :
  isArray a xs →
  wp (find_index a) (λ out, find_index_inv xs (len xs) out).
Proof.
  intros. unfold find_index.
  wp_length _n.
  eapply wp_conseq.
  { int.wp_uxiter_up (find_index_inv xs); tc;
    unfold find_index_inv in *.
    (* Initialization. *)
    { eauto with lia. }
    (* Preservation. *)
    { (* TODO need variant of [wp_loop_intros] or [wp_up_intros] without state? *)
      let h := fresh "Hinv" in intros j j1 h; unpack in h.
      intros; unpack; subst.
      wp_get x. subst x.
      wp_if; wp_bind_eq.
      (* Case: [OK x]. *)
      + tc.
      (* Case: [notOK x]. *)
      + match goal with H: _ → ?goal |- ?goal => eapply H end.
        eapply one_step_up; eauto. }}
  { autorewrite with nat.
    intros [|] (k&?&?).
    (* Subcase: the loop has ended by breaking. The loop index is an
       unknown [i]. Fortunately [find_index_inv xs k (Break i)] is
       independent of [k]. *)
    + assumption.
    (* Subcase: the loop has ended normally. *)
    + assert (k = len xs) by tauto. subst k. assumption. }
Qed.

End FindIndex.

(* A test. *)

(* Finding the index of the leftmost multiple of 7 in an array. *)

Local Definition multiple_of_7 (z : Z) : bool :=
  (z `mod` 7 =? 0)%Z.

Goal
  find_index multiple_of_7 (of_list [2;3;4;14;12;14])%Z =
  Break 3%uint63.
Proof. vm_compute. reflexivity. Qed.

Goal
  find_index multiple_of_7 (of_list [])%Z =
  Continue.
Proof. vm_compute. reflexivity. Qed.

Goal
  find_index multiple_of_7 (of_list [1;2;3])%Z =
  Continue.
Proof. vm_compute. reflexivity. Qed.

Goal
  find_index multiple_of_7 (of_list [1;1;1;1;1;1;1;1;1;1;0])%Z =
  Break 10%uint63.
Proof. vm_compute. reflexivity. Qed.

Goal
  find_index multiple_of_7 (of_list [140;1;1;1;1;1;1;1;1;1;0])%Z =
  Break 0%uint63.
Proof. vm_compute. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)

(* [exist]. *)

Section Exist.
Context `{Inhabited A}.
Implicit Types a : array A.
Implicit Types xs : list A.

Variable f : A → bool.

Definition exist a :=
  do out ← find_index f a ;
  did_break out.

(* Our hypothesis about [f]. (See [find_index].) *)

Variable     OK : A → bool.
Variable  notOK : A → bool.
Variable f_spec :
  ∀ x, isBool (f x) (OK x) (notOK x).

(* The public specification of [exist]. *)

Lemma wp_exist a xs :
  isArray a xs →
  wp (exist a) (λ b,
    isBool b
      (∃ j, valid j xs ∧ OK (xs !!! j))
      (∀ j, valid j xs → notOK (xs !!! j))
  ).
Proof.
  intros. unfold exist.
  wp_op @wp_find_index out.
  destruct out as [ _i |]; unfold find_index_inv in *; unpack;
  wp_ret; tc.
Qed.

End Exist.

(* -------------------------------------------------------------------------- *)

(* [for_all]. *)

Section ForAll.
Context `{Inhabited A}.
Implicit Types a : array A.
Implicit Types xs : list A.

Variable f : A → bool.

(* The code. *)

Definition for_all a :=
  do out ← find_index (λ x, negb (f x)) a ;
  did_not_break out.

(* Our hypothesis about [f]. (See [find_index].) *)

Variable     OK : A → bool.
Variable  notOK : A → bool.
Variable f_spec :
  ∀ x, isBool (f x) (OK x) (notOK x).

(* The public specification of [for_all]. *)

Lemma wp_for_all a xs :
  isArray a xs →
  wp (for_all a) (λ b,
    isBool b
      (∀ j, valid j xs → OK (xs !!! j))
      (∃ j, valid j xs ∧ notOK (xs !!! j))
  ).
Proof.
  intros. unfold for_all.
  wp_op @wp_find_index out.
  destruct out as [ _i |]; unfold find_index_inv in *; unpack;
  wp_ret; tc.
Qed.

End ForAll.

(* -------------------------------------------------------------------------- *)

(* [equal]. *)

Section Equal.
Context `{Inhabited A}.
Implicit Types a b : array A.
Implicit Types xs ys : list A.

Variable eq : A → A → bool.

(* The code. *)

Definition equal_aux _m a b : outcome unit :=
  int.uxiter_up 0 _m @@ λ _ _i continue break ,
  do x ← get a _i ;
  do y ← get b _i ;
  if eq x y then continue () else break ().

Definition equal a b : bool :=
  do _m ← length a ;
  do _n ← length b ;
  if (_m =? _n)%uint63 then
    do out ← equal_aux _m a b ;
    did_not_break out
  else
    false.

(* Our hypothesis about [eq]. *)

Variable EQ : A → A → Prop.

Local Infix "≡" := EQ (at level 70, no associativity).

Variable eq_spec :
  ∀ x y, isBool1 (eq x y) (x ≡ y).

(* The proposition [equal_inv xs n i o] is the loop invariant. *)

Definition equal_inv xs ys i o :=
  match o with
  | Continue =>
      (* Up to index [i], the lists [xs] and [ys] agree. *)
      ∀ j, j < i → xs !!! j ≡ ys !!! j
  | Break () =>
      (* [i - 1] is a valid index into the list [xs], the two lists
         agree up to index [i - 1], and they disagree at this index. *)
      let i := i - 1 in
      valid i xs ∧
      ¬ xs !!! i ≡ ys !!! i ∧
      ∀ j, j < i → xs !!! j ≡ ys !!! j
  end.

(* The public specification of [equal]. *)

Lemma wp_equal a xs b ys :
  isArray a xs →
  isArray b ys →
  wp (equal a b) (λ o,
      isBool1 o (Forall2 EQ xs ys)
  ).
Proof.
  intros. unfold equal.
  wp_length _m.
  wp_length _n.
  wp_if.
  (* First branch: the lengths of the arrays coincide. *)
  { eapply wp_bind.
    { unfold equal_aux.
      int.wp_uxiter_up (equal_inv xs ys);
        tc; unfold equal_inv in *; eauto with lia.
      (* Preservation. *)
      (* TODO need variant of [wp_loop_intros] or [wp_up_intros] without state? *)
      let h := fresh "Hinv" in intros j j1 h; unpack in h.
      intros; unpack; subst.
      wp_get x. wp_get y.
      wp_if; wp_bind_eq; subst.
      (* Case: [eq x y] returns [true]. *)
      { match goal with H: _ → ?goal |- ?goal => apply H end.
        eapply one_step_up; eauto. }
      (* Case: [eq x y] returns [false]. *)
      { list in *. eauto with lia. }
    }
    intros [[]|]; unfold equal_inv; intros (i&?); unpack; wp_ret.
    (* Case: the loop ends by breaking. *)
    { tc. }
    (* Case: the loop ends normally. *)
    { assert (i = len xs) by tauto. subst. tc. }
  }
  (* Second branch: the lengths of the arrays differ. *)
  { wp_ret. tc. }
Qed.

End Equal.

(* As a special case, we recover a simpler specification of [equal]
   in the case where the relation [≡] is equality. *)

Lemma wp_equal_equality `{Inhabited A}
  (eq : A → A → bool)
  (eq_spec : ∀ x y, isBool1 (eq x y) (x = y))
  a xs b ys :
  isArray a xs →
  isArray b ys →
  wp (equal eq a b) (λ o, isBool1 o (xs = ys)).
Proof.
  intros.
  eapply wp_conseq; [ eapply wp_equal; eauto | simpl ].
  intros o Ho. eapply isBool1_conseq; [ eauto |].
  (* [Forall2 (@eq A)] is the same as [@eq (list A)]. *)
  symmetry. eapply list_eq_Forall2.
Qed.

(* -------------------------------------------------------------------------- *)

(* [segment_iteri] and [iteri]. *)

(* An iteration function on an array is not super useful, as the user
   can just as well use [int.iter_up] or [int.iter_down] directly.
   However, this is a good exercise in preparation for defining
   iteration functions on vectors, hash tables, or other containers. *)

(* Although we name this function [iteri], it carries a state, so it
   is of course a fold. *)

Section Iteri.
Context {S : Type}.
Implicit Types s : S.
Context `{Inhabited A}.
Implicit Types a : array A.
Implicit Types xs : list A.
Implicit Types f : int → A → S → S.

(* The code. *)

Definition segment_iteri a _i _k s f : S :=
  int.iter_up _i _k s @@ λ _j s ,
  do x ← get a _j ;
  do s ← f _j x s ;
  s.

Definition iteri a s f :=
  do _n ← length a ;
  segment_iteri a 0 _n s f.

(* The public specification of [segment_iteri]. *)

Lemma wp_segment_iteri a xs f :
  isArray a xs →
  ∀Int _i i ,
  ∀Int _k k ,
  valid_seg i k xs →
  ITER_NAT i k Up
    (λ j s Q, ∀ _j, isInt _j j → ∀ x, x = xs !!! j → wp (f _j x s) Q)
    (λ s Q, wp (segment_iteri a _i _k s f) Q).
Proof.
  intros. ITER. unfold segment_iteri.
  int.wp_iter_up inv.
  clear dependent s.
  (* The loop body. *)
  { wp_up_intros _j j xs'.
    wp_get x.
    wp_op Hstep s'.
    wp_ret. eauto. }
Qed.

(* The public specification of [iteri]. *)

Lemma wp_iteri a xs f :
  isArray a xs →
  ITER_NAT
    0 (len xs) Up
    (λ j s Q, ∀ _j, isInt _j j → ∀ x, x = xs !!! j → wp (f _j x s) Q)
    (λ s Q, wp (iteri a s f) Q).
Proof.
  intros. ITER. unfold iteri.
  wp_length _n.
  wp_loop @wp_segment_iteri inv.
Qed.

End Iteri.
