From stdpp Require Import numbers list.
From listz Require Import listz.
Notation len := length.
From Stdlib Require Import Uint63.
From Stdlib Require Import Array.PArray.
From marble Require Import tactics bool int iteration loop wp logic.
Implicit Types _i _j _k _n : int.
From Corelib Require Derive.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

(* Documentation:
   https://rocq-prover.org/doc/V9.0.1/corelib/Corelib.Array.PrimArray.html
   https://rocq-prover.org/doc/V9.0.1/corelib/Corelib.Array.ArrayAxioms.html
   https://rocq-prover.org/doc/v9.1/stdlib/Stdlib.Array.PArray.html
 *)

Local Ltac wp_intro_hook Hx ::=
  (* Simplify expressions that involve lists and arithmetic. *)
  list in Hx;
  (* Decompose existential quantifiers and conjunctions. *)
  unpack in Hx;
  (* Attempt to (cheaply) solve the goal. *)
  (* This can kill some proof obligations, e.g., at loop exits. *)
  wp_ret_hook.

(* -------------------------------------------------------------------------- *)

(* The maximum length of an array. *)

(* We have [max_length : int]; we define [max_array_length : Z]. *)

Definition max_array_length : Z :=
  to_Z max_length.

(* These constants are related by [isInt]. *)

Instance max_length_spec :
  isInt max_length max_array_length.
Proof.
  introIsInt. unfold max_array_length. lia.
Qed.

(* [max_array_length] is representable. *)

Lemma unsigned_max_array_length :
  unsigned max_array_length.
Proof.
  unfold max_array_length.
  (* This proof should work for larger constants as well. *)
  (* The goal is a conjunction of inequalities in Z. *)
  (* To my surprise, computation in Z solves this goal. *)
  compute. split; congruence.
Qed.

(* [2 * max_array_length] is still representable. *)

Lemma unsigned_twice_max_array_length :
  unsigned (2 * max_array_length).
Proof.
  unfold max_array_length.
  compute. split; congruence.
Qed.

(* [max_array_length] is not ridiculously small. *)

Lemma max_array_length_is_large :
  1024 < max_array_length.
Proof.
  (* This proof will work for any constant that really is less
     than [max_array_length]. *)
  unfold max_array_length.
  compute. eauto.
Qed.

(* The length of an array, converted to an integer,
   is nonnegative, and bounded by [max_array_length]. *)

Lemma leb_length' {A} (a : array A) :
  0 ≤ to_Z (length a) ≤ max_array_length.
Proof.
  generalize (leb_length _ a).
  rewrite leb_spec.
  rewrite max_length_spec. (* rewriting through [isInt] *)
  unfold max_array_length.
  lia.
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
  ∀ i, valid i xs → a.[of_Z i] = xs !!! i.

(* These tactics and lemmas help work with [isArray]. *)

Local Ltac introIsArray :=
  split; [| split ].

Local Ltac destructIsArray :=
  match goal with h: isArray _ _ |- _ => destruct h as (?&?&?) end.

(* This lemma can be viewed as a specification of [length],
   viewed as a "pure function", so [wp] is not used. *)

Instance isInt_length `{Inhabited A} (a : array A) xs :
  isArray a xs →
  isInt (length a) (len xs).
Proof.
  intros. destructIsArray. eauto.
Qed.

Lemma isArray_bounded_length `{Inhabited A} (a : array A) xs :
  isArray a xs →
  0 ≤ len xs ≤ max_array_length.
Proof.
  intros. destructIsArray. lengths. lia.
Qed.

(* Sometimes the fact that an array has bounded length must be
   established a priori, at function definition time, as opposed to a
   posteriori, while verifying a function. The axiom [leb_length] can
   be used for this purpose. *)

Goal ∀ A (a : array A),
  (length a ≤? max_length)%uint63 = true.
Proof. exact leb_length. Qed.

(* The tactic [arrays] looks for hypotheses of the form [isArray a xs]
   and introduces the fact [0 ≤ len xs ≤ max_array_length]. *)

Ltac arrays :=
  repeat match goal with
  h: isArray ?a ?xs |- _ =>
    let h' := fresh h in
    generalize (isArray_bounded_length a xs h); intro h';
    revert h h'
  end;
  intros;
  (* We also introduce [unsigned max_array_length]. *)
  generalize unsigned_max_array_length; intro.

(* One might wish to define [zify_pre_hook] so as to invoke
   [arrays; lengths; ulength in *]. However, in some proofs,
   this can be very slow. *)

Local Ltac Zify.zify_pre_hook ::=
  generalize unsigned_max_array_length; intro;
  ulength.

(* Any number that is bounded by [max_array_length] is representable. *)

Goal ∀ n, 0 ≤ n ≤ max_array_length → unsigned n.
Proof. eauto with lia. Qed.

Goal ∀ `{Inhabited A} (a : array A) xs,
  ∀ n,
  isArray a xs →
  n ≤ len xs →
  n ≤ max_array_length.
Proof. intros. arrays. eauto with lia. Qed.

Goal ∀ `{Inhabited A} (a : array A) xs,
  isArray a xs → unsigned (len xs).
Proof. intros. arrays. eauto with lia. Qed.

Local Lemma isArray_pi3 `{Inhabited A} (a : array A) xs :
  isArray a xs →
  ∀ i, valid i xs →
  a.[of_Z i] = xs !!! i.
Proof.
  intros. destructIsArray. eauto.
Qed.

Local Lemma isArray_pi3' `{Inhabited A} (a : array A) xs :
  isArray a xs →
  ∀ _i, valid (to_Z _i) xs →
  a.[_i] = xs !!! (to_Z _i).
Proof.
  intros. erewrite <- isArray_pi3 by eauto. int. eauto.
Qed.

(* This lemma is currently unused. *)
Local Lemma isArray_show_valid `{Inhabited A} (a : array A) xs :
  ∀IntU _i i,
  isArray a xs →
  (_i <? length a)%uint63 = true →
  valid i xs.
Proof.
  intros ?????. destructIsIntU.
  rewrite ltb_spec, isInt_length by eauto.
  intros. arrays. eauto with lia.
Qed.

Local Lemma isArray_use_valid `{Inhabited A} (a : array A) xs :
  ∀Int _i i,
  isArray a xs →
  valid i xs →
  (_i <? length a)%uint63 = true.
Proof.
  intros ???? Hxs. destructIsInt.
  rewrite ltb_spec, isInt_length by eauto.
  arrays. eauto with lia.
Qed.

(* I am not sure whether it is a good idea to have this instance.
   Perhaps it can be useful to users who do not want to write
   [do _n ← length a ; if (_i <? _n) then ...] and prefer to write
   [if (_i <? length a) then ...]. *)

Instance isBool1_lt_length `{Inhabited A} (a : array A) xs :
  isArray a xs →
  ∀IntU _i i,
  isBool1 (_i <? length a)%uint63 (valid i xs).
Proof.
  intros. arrays. eapply isBool1_variance; tc4. (* so sweet! *)
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
  { eauto using isInt_inj_1, isInt_length. }
  { intros _i ?.
    assert (isInt _i (to_Z _i)) by eauto using introIsInt.
    isBool_magic.
    erewrite !isArray_pi3' by eauto.
    eauto. }
  { eauto. }
Qed.

(* [isArray a _] is injective. *)

Lemma isArray_inj_2 `{Inhabited A} a (xs ys : list A) :
  isArray a xs → isArray a ys → xs = ys.
Proof.
  intros. arrays.
  assert (len xs = len ys).
  { eapply isInt_inj_2;
    eauto using isInt_length with typeclass_instances lia. }
  listx_total o.
  erewrite <- !isArray_pi3 in * by eauto with lia.
  eauto.
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

Local Lemma length_make' x :
  ∀Int _n n,
  0 ≤ n ≤ max_array_length →
  isInt (length (make _n x)) n.
Proof.
  intros. rewrite !isInt_def in *. subst.
  assert ((of_Z n ≤? max_length)%uint63 = true) as Hbound.
  { rewrite leb_spec. rewrite max_length_spec. int. tauto. }
  rewrite length_make, Hbound. eauto.
Qed.

(* The public specification of [make]. *)

Lemma wp_make x :
  ∀Int _n n,
  0 ≤ n ≤ max_array_length →
  wp (make _n x) (λ a, isArray a (replicate n x)).
Proof.
  intros. wp_ret.
  introIsArray; length; eauto using length_make' with lia.
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
  intros. destructIsArray. repeat destructIsInt. wp_ret.
Qed.

(* The public specification of [set]. *)

Lemma wp_set _i i a xs x :
  isInt _i i →
  isArray a xs →
  valid i xs →
  wp a.[_i <- x] (λ a', isArray a' (<[i := x]>xs)).
Proof.
  intros Hi ??. arrays.
  wp_ret. introIsArray; length.
  { rewrite length_set. tc. }
  { eauto with lia. }
  intros j ?. destructAndKeepIsInt.
  destruct (decide (i = j)); [ subst j |]; list.
  + rewrite get_set_same by eauto using isArray_use_valid.
    eauto.
  + rewrite get_set_other
      by eauto using of_Z_inj' with typeclass_instances lia.
    erewrite isArray_pi3 by eauto.
    eauto.
Qed.

(* The public specification of [length]. *)

(* See also [isInt_length]. *)

Lemma wp_length a xs :
  isArray a xs →
  wp (length a) (λ _n,
    isInt _n (len xs)
  ).
Proof.
  intros. wp_ret.
Qed.

End PrimSpec.

(* The following tactics help use the above specifications. *)

Ltac wp_length n :=
  wp_op wp_length introducing: n.

Tactic Notation "wp_get" simple_intropattern(x) :=
  wp_op wp_get introducing: x.

Ltac wp_set :=
  match goal with |- context[set ?a _ _] =>
    wp_op wp_set shadowing: a
  end.

Ltac wp_make a :=
  wp_op wp_make introducing: a.

(* -------------------------------------------------------------------------- *)

(* The tactic [isArray] is applicable when the goal is [isArray a ys]
   and there is a hypothesis [isArray a xs]. The goal is then reduced
   to the equation [xs = ys], and this equation is simplified. If the
   equation is trivial then the goal is solved. *)

Ltac isArray :=
  match goal with
  | h: isArray ?a ?xs |- isArray ?a ?ys =>
    cut (xs = ys); [
      let Heq := fresh in intro Heq; try rewrite <- Heq; exact h
    | clear h;
      try subst; (* this can help *)
      lego
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

Definition plain_segment_to_list a _i _k :=
  (* For [_j] ranging from [_k] (excluded) down to [_i],
     with running state [xs], initially empty, *)
  iter_down _i _k [] @@ λ _j xs,
  (* Read the [_j]-th element of the array [a], *)
  do x ← a.[_j] ;
  (* and prepend it in front of [xs]. *)
  x :: xs.

Section Specialize.
Local Opaque Acc_inv ilt Acc_ilt.
Local Opaque bind.

  Derive segment_to_list
    in (∀ a _i _k, segment_to_list a _i _k = plain_segment_to_list a _i _k)
    as segment_to_list_eq.
  Proof.
    intros. unfold plain_segment_to_list.
    rewrite <- iter_down_unrolled_eq.
    unfold iter_down_unrolled, iter_down_unrolled_aux, iter_down_N.
    (* unfold iter_down, iter_down_aux. *)
    unfold segment_to_list; reflexivity.
  Defined.
  (* Print segment_to_list. *)

End Specialize.

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
  intros. arrays.
  rewrite segment_to_list_eq.
  unfold plain_segment_to_list.
  (* The loop invariant. *)
  wp_op wp_iter_down with invariant: (λ j ys, ys = seg j k xs);
  last wp_intro ?.
  (* Initialization. *)
  { lego. }
  (* Preservation. *)
  { wp_iter_down_body _j j ys.
    wp_get x.
    wp_ret.
    lego. }
Qed.

Lemma wp_to_list a xs :
  isArray a xs →
  wp (to_list a) (λ xs', xs' = xs).
Proof.
  intro. arrays. unfold to_list.
  wp_length _n.
  wp_op wp_segment_to_list introducing: ?.
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
  intros. unfold to_list.
  (* Obtain the length of the array. *)
  eapply wp_bind_eq. intros _n Hn.
  rewrite segment_to_list_eq. unfold plain_segment_to_list.
  set (n := to_Z _n).
  assert (isInt _n n) by eauto using introIsInt.
  assert (0 ≤ n ≤ max_array_length).
  { subst n _n. simple eapply leb_length'. }
  (* The loop invariant: when the loop index is [j] and the state is
     [ys], the length of [ys] is [n - j] and the elements of [ys] are
     the elements found at indices [j, n) in the array [a]. *)
  wp_op wp_iter_down with invariant: (λ j ys,
    len ys = n - j ∧
    ∀ o, j ≤ o < n → a.[of_Z o] = ys !!! (o - j)
  ).
  (* Preservation. *)
  { wp_iter_down_body _j j ys.
    destructIsInt.
    wp_bind_eq.
    wp_ret. split; [ lia |].
    intros o ?. list. case_lookup_app.
    { assert (o = j) by lia. congruence. }
    { replace (o - j - 1) with (o - (j + 1)) by lia. (* painful *)
      eauto with lia. } }
  (* Completion. *)
  { wp_intro xs. subst. z in *.
    introIsArray;
      match goal with h: len xs = _ |- _ => rewrite ?h end; tc3.
    intros o ?.
    replace o with (o - 0) at 2 by lia. (* painful *)
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

Section Body.
Variable body : S → int → A → S.

(* The code. *)

Fixpoint list_iteri_aux _i xs s :=
  match xs with
  | [] =>
      s
  | x :: xs =>
      do s ← body s _i x ;
      list_iteri_aux (_i + 1) xs s
  end.

End Body.

Definition list_iteri _i xs s body :=
  list_iteri_aux body _i xs s.

(* Local lemmas about `prefix_of`. *)

Local Lemma prefix_reflexive {B} (xs : list B) : xs `prefix_of` xs.
Proof. reflexivity. Qed.

Local Lemma prefix_of_app_l {B} (xs ys zs : list B) :
  xs ++ ys `prefix_of` xs ++ ys ++ zs.
Proof.
  econstructor. eapply app_assoc.
Qed.

(* An inductive specification. (This is an auxiliary lemma.) *)

(* The user-provided loop invariant [inv history s] is parameterized
   with the already-visited elements [history] and the current user
   state [s]. It does not need to be parameterized with the current
   index [i], because [i] is just the length of the list [history]. *)

Local Lemma wp_list_iteri_aux xs body :
  ∀ future history,
  ∀Int _i i,
  xs = history ++ future →
  i = len history →
  ITERI_LIST
    history xs
    (λ x i s Q, ∀ _i, isInt _i i → wp (body s _i x) Q)
    (λ s Q, wp (list_iteri_aux body _i future s) Q).
(* Hints for this proof. *)
Local Hint Resolve prefix_reflexive prefix_app_l prefix_of_app_l : marble.
Proof.
  induction future as [| x future ]; simpl list_iteri_aux; intros;
  ITER; subst xs; list in *.
  (* Case: the future is empty. *)
  { wp_ret. }
  (* Case: the future begins with [x]. *)
  { wp_op Hbody shadowing: s.
    wp_op IHfuture shadowing: s. }
Qed.

(* The public specification of [list_iteri]. *)

Lemma wp_list_iteri xs s body :
  ITERI_LIST
    [] xs
    (λ x i s Q, ∀ _i, isInt _i i → wp (body s _i x) Q)
    (λ s Q, wp (list_iteri 0 xs s body) Q).
Proof.
  unfold ITERI_LIST. eapply wp_list_iteri_aux; tc3.
Qed.

End ListIteri.

(* The tactic [wp_list_iteri_body s _i i x history] should be used
   upon entry into the loop body. It introduces the state [s], the
   index [_i] and its integer model [i], the element [x], and the
   ghost parameter [history]. *)

Tactic Notation "wp_list_iteri_body"
  simple_intropattern(s)
  simple_intropattern(_i)
  simple_intropattern(i)
  simple_intropattern(x)
  simple_intropattern(history)
:=
  wp_body history ? s introducing: (fun _ => list_step x i; intros _i ?).

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
  ∀ future history xs,
  ∀Int _i i,
  xs = history ++ future →
  i = len history →
  ITER_Z
    i (len xs) Up
    (λ j s Q, ∀ _j, isInt _j j → ∀ x, x = xs !!! j → wp (f s _j x) Q)
    (λ s Q, wp (list_iteri _i future s f) Q).
Proof.
  expand_ITER.
  induction future as [| x future ];
  intros history xs _i i ? ? ?;
  ITER;
  simpl list_iteri; subst; lengths; list in *.
  { wp_ret. }
  { wp_op Hbody shadowing: s.
    { list. eauto. }
    (* The system cannot guess how we want to extend the history
       because any history of length [len history + 1] will do! *)
    wp_op (IHfuture (history ++ {[x]})) shadowing: s.
    { intros. wp_apply Hbody. }}
Qed.

(* In this variant, we get rid of [history] and we keep track only
   of the equation [final_seg i xs = future], which means that the
   future is the segment of [xs] that begins at index [i]. *)

(* This specification is just as concise as the previous one, but
   the proof is slightly longer, as I am unable to automate the use
   of the lemmas [lookup_total_through_seg] and [seg_through_seg]. *)

Local Lemma wp_list_iteri_aux_variant_2 xs f :
  ∀ future,
  ∀Int _i i ,
  0 ≤ i ≤ len xs →
  final_seg i xs = future →
  ITER_Z
    i (len xs) Up
    (λ j s Q, ∀ _j, isInt _j j → ∀ x, x = xs !!! j → wp (f s _j x) Q)
    (λ s Q, wp (list_iteri _i future s f) Q).
Proof.
  expand_ITER.
  induction future as [| x future ];
  intros _i i ? ? ?;
  ITER;
  simpl list_iteri;
  lengths; ulength in *.
  (* Case: the future is empty. We have [i = len xs]. *)
  { assert (i = len xs) by lia.
    wp_ret. }
  (* Case: the future begins with [x]. We have [i < len xs]. *)
  { assert (i < len xs) by lia.
    assert (x = xs !!! i) by (lookup_through_seg; eauto).
    assert (final_seg (i + 1) xs = future) by (seg_through_seg; eauto).
    wp_op Hbody shadowing: s.
    wp_op IHfuture shadowing: s. }
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
  induction xs as [| x xs ]; simpl list_length_aux; list; intros.
  { wp_ret. }
  { wp_op IHxs shadowing: _n. }
Qed.

(* The public specification of [list_length]. *)

Lemma wp_list_length xs :
  wp (list_length xs) (λ _i, isInt _i (len xs)).
Proof.
  unfold list_length.
  wp_op wp_list_length_aux introducing: ?.
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
  intros. lengths. unfold of_list.
  wp_op wp_list_length introducing: _n.
  wp_make a.
  (* The loop invariant. *)
  wp_op wp_list_iteri with invariant: (λ history a,
    isArray a (history ++ replicate (len xs - len history) inhabitant)
  ); last wp_shadow a.
  (* Preservation. *)
  { clear dependent _n a. wp_list_iteri_body a _i i x history.
    lengths. ulength in *.
    wp_set.
    isArray. }
  (* Completion. *)
  { isArray. }
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
  wp_op wp_of_list introducing: a.
  wp_op wp_to_list introducing: ys.
  wp_ret.
Qed.

(* -------------------------------------------------------------------------- *)

(* Some tests of [to_list . of_list]. *)

(* This test shows that [compute] is able to evaluate a call to
   [iter_down_aux]. *)
Goal to_list (of_list [1;2;3]) = [1;2;3].
Proof. compute. reflexivity. Qed.

(* This test shows that [vm_compute] works as desired. *)
Goal to_list (of_list [1;2;3]) = [1;2;3].
Proof. vm_compute. reflexivity. Qed.

(* This test shows that [lazy] works as desired. *)
Goal to_list (of_list [1;2;3]) = [1;2;3].
Proof. lazy. reflexivity. Qed.

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

(* In [blit], the arrays [a] and [b] must be two *independent* arrays;
   that is, they should not be two persistent arrays that are backed
   by the same underlying physical array. To move data within a single
   array, see [blit']. *)

Section Blit.
Context `{Inhabited A}.
Implicit Types a b : array A.
Implicit Types xs ys : list A.

Section Code.
Open Scope uint63.

(* We compute [_delta] outside of the loop so as to save one addition
   inside the loop. This is a bit subtle, as the difference [_j - _i]
   might be negative, yet we compute it as an unsigned integer. This
   yields the correct result in the end anyway. *)

Definition plain_blit a _i b _j _n :=
  do _delta ← _j - _i ;
  iter_up _i (_i + _n) b @@ λ _k b,
  do x ← get a _k ;
  do b ← set b (_k + _delta) x ;
  b.

End Code.

Section Specialize.
Local Opaque Acc_inv igt Acc_igt.
Local Opaque bind.

  Derive blit in
    (∀ a _i b _j _n, blit a _i b _j _n = plain_blit a _i b _j _n)
    as blit_eq.
  Proof.
    intros. unfold plain_blit.
    setoid_rewrite <- iter_up_unrolled_eq.
    unfold iter_up_unrolled, iter_up_unrolled_aux, iter_up_N.
    unfold iter_up, iter_up_aux.
    unfold blit; reflexivity.
  Defined.
  (* Print blit. *)

End Specialize.

(* The postcondition of a [blit] function. *)

Local Notation blit_post xs i ys j n := (
  λ b,
    isArray b
      (initial_seg j ys ++ seg i (i + n) xs ++ final_seg (j + n) ys)
).

(* [blit] is correct. *)

Lemma wp_blit :
  ∀ a xs,
  isArray a xs →
  ∀Int _i i,
  ∀ b ys,
  isArray b ys →
  ∀Int _j j,
  ∀Int _n n,
  valid_seg i (i + n) xs →
  valid_seg j (j + n) ys →
  wp (blit a _i b _j _n) (blit_post xs i ys j n).
Proof.
  intros. arrays. lengths.
  rewrite blit_eq. unfold plain_blit.
  wp_bind_eq.
  wp_op wp_iter_up with invariant: (λ k, blit_post xs i ys j (k - i));
  last wp_shadow b; try solve [ isArray ].
  (* Preservation. *)
  { clear dependent b. wp_iter_up_body _k k b.
    wp_get x. subst x.
    wp_set. wp_ret. isArray. }
    (* The use of unsigned arithmetic in the computation of [_delta]
       does not cause any problem. Once upon a time, this proof used
       natural numbers as the logical model of machine integers; then
       we had to explicitly say [rewrite int.add_sub_exch] in order to
       pretend that we never created a negative number. Now this trick
       is unnecessary. *)
Qed.

(* -------------------------------------------------------------------------- *)

(* Moving data within an array: [blit']. *)

(* The source and destination segments may overlap. *)

(* [blit'] LOOKS LIKE, but IS NOT, a special case of [blit]. It always
   reads from the latest version of the array, which is both the
   source and the destination array. If one attempted to use a call of
   the form [blit a _i a _j _n] then one would read from outdated
   versions of the array [a]. *)

Section Code.
Open Scope uint63.

Definition plain_blit'_up a _i _j _n :=
  do _delta ← _j - _i ;
  iter_up _i (_i + _n) a @@ λ _k a,
  do x ← get a _k ;
  do a ← set a (_k + _delta) x ;
  a.

Definition plain_blit'_down a _i _j _n :=
  do _delta ← _j - _i ;
  iter_down _i (_i + _n) a @@ λ _k a,
  do x ← get a _k ;
  do a ← set a (_k + _delta) x ;
  a.

Definition plain_blit' a _i _j _n :=
  if _j <=? _i then
    plain_blit'_up a _i _j _n
  else
    plain_blit'_down a _i _j _n.

End Code.

Section Specialize.
Local Opaque Acc_inv ilt igt Acc_ilt Acc_igt.
Local Opaque bind.

  Derive blit' in
    (∀ a _i _j _n, blit' a _i _j _n = plain_blit' a _i _j _n)
    as blit'_eq.
  Proof.
    intros. unfold plain_blit'.
    unfold plain_blit'_up, plain_blit'_down.
    setoid_rewrite <- iter_up_unrolled_eq.
    setoid_rewrite <- iter_down_unrolled_eq.
    unfold iter_up_unrolled, iter_up_unrolled_aux, iter_up_N.
    unfold iter_up, iter_up_aux.
    unfold iter_down_unrolled, iter_down_unrolled_aux, iter_down_N.
    unfold iter_down, iter_down_aux.
    unfold blit'; reflexivity.
  Defined.
  (* About 110 lines of code! *)
  (* Print blit'. *)

End Specialize.

(* [blit'] is correct. *)

Lemma wp_blit' :
  ∀ a xs,
  isArray a xs →
  ∀Int _i i,
  ∀Int _j j,
  ∀Int _n n,
  valid_seg i (i + n) xs →
  valid_seg j (j + n) xs →
  wp (blit' a _i _j _n) (blit_post xs i xs j n).
Proof.
  intros. arrays. lengths.
  rewrite blit'_eq. unfold plain_blit'.
  wp_if.
  (* Case [j ≤ i]. Blit upwards. *)
  { unfold plain_blit'_up.
    wp_bind_eq.
    wp_op wp_iter_up
      with invariant: (λ k, blit_post xs i xs j (k - i));
    last wp_shadow a; try solve [ isArray ].
    (* Preservation. *)
    { clear dependent a. wp_iter_up_body _k k a.
      wp_get x. subst x. wp_set. wp_ret. isArray. }}
  (* Case [i < j]. Blit downwards. *)
  { unfold plain_blit'_down.
    wp_bind_eq.
    wp_op wp_iter_down
      with invariant: (λ k, blit_post xs k xs (k + j - i) (i + n - k));
    last wp_shadow a; try solve [ isArray ].
    (* Preservation. *)
    { clear dependent a. wp_iter_down_body _k k a.
      wp_get x. subst x. wp_set. wp_ret. isArray. }}
Qed.

End Blit.

Ltac wp_blit :=
  match goal with
  | |- context[blit _ _ ?b _ _] =>
      wp_op wp_blit shadowing: b
  | |- context[blit' ?a _ _ _] =>
      wp_op wp_blit' shadowing: a
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
  blit a 0 b 0 _n.

(* The public specification of [copy]. *)

Lemma wp_copy a xs :
  isArray a xs →
  wp (copy a) (λ b, isArray b xs).
Proof.
  intros. arrays. unfold copy.
  wp_length n.
  wp_make b.
  wp_blit.
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
  blit a _i b 0 _n.

(* The public specification of [sub]. *)

Lemma wp_sub a _i i _n n xs :
  isArray a xs →
  isInt _i i →
  isInt _n n →
  valid_seg i (i + n) xs →
  wp (sub a _i _n) (λ b, isArray b (seg i (i + n) xs)).
Proof.
  intros. arrays. unfold sub.
  wp_make b.
  wp_blit.
Qed.

End Sub.

(* -------------------------------------------------------------------------- *)

(* Concatenating two arrays: [append]. *)

Section Append.
Context `{Inhabited A}.
Implicit Types a b : array A.
Implicit Types xs ys : list A.

(* The code. *)

Section Code.
Open Scope uint63.

Definition append a b :=
  do _m ← length a ;
  do _n ← length b ;
  do c ← make (_m + _n) inhabitant ;
  do c ← blit a 0 c 0 _m ;
  do c ← blit b 0 c _m _n ;
  c.

End Code.

(* The public specification of [append]. *)

Lemma wp_append a xs b ys :
  isArray a xs →
  isArray b ys →
  len xs + len ys ≤ max_array_length →
  wp (append a b) (λ c, isArray c (xs ++ ys)).
Proof.
  intros. arrays. unfold append.
  wp_length _m.
  wp_length _n.
  wp_make c.
  wp_blit.
  wp_blit.
Qed.

End Append.

(* -------------------------------------------------------------------------- *)

(* Copying a value into an array segment: [fill]. *)

Section Fill.
Context `{Inhabited A}.
Implicit Types a b : array A.
Implicit Types xs ys : list A.

(* The code. *)

Section Code.
Open Scope uint63.

Definition plain_fill a _i _n x :=
  iter_up _i (_i + _n) a @@ λ _k a,
  do a ← set a _k x ;
  a.

Section Specialize.
Local Opaque Acc_inv igt Acc_igt.
Local Opaque bind.

  Derive fill in
    (∀ a _i _n x, fill a _i _n x = plain_fill a _i _n x)
    as fill_eq.
  Proof.
    intros. unfold plain_fill.
    rewrite <- iter_up_unrolled_eq.
    unfold iter_up_unrolled, iter_up_unrolled_aux, iter_up_N.
    unfold iter_up, iter_up_aux.
    unfold fill; reflexivity.
  Defined.
  (* Print fill. *)

End Specialize.

End Code.

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
  intros. arrays. rewrite fill_eq. unfold plain_fill.
  wp_op wp_iter_up with invariant: (λ k a, isArray a
    (initial_seg i xs ++ replicate (k - i) x ++ final_seg k xs)
  ); last wp_shadow a; try solve [ isArray ].
  (* Preservation. *)
  { clear dependent a. wp_iter_up_body _k k a.
    wp_set. wp_ret. isArray. }
Qed.

End Fill.

Ltac wp_fill :=
  match goal with |- context[fill ?a _ _ _] =>
    wp_op wp_fill shadowing: a
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

Definition plain_find_index a : outcome int :=
  do _n ← length a ;
  uxiter_up 0 _n @@ λ _ _i continue break,
  do x ← get a _i ;
  if f x then break _i else continue ().

Derive find_index
  in (∀ a, find_index a = plain_find_index a)
  as find_index_eq.
Proof.
  intros. unfold plain_find_index.
  unfold uxiter_up, uxiter_up_aux.
  unfold find_index; reflexivity.
Defined.
(* Print find_index. *)

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
      on_seg 0 n (λ j, notOK (xs !!! j))
  | Break _i =>
      (* The machine integer [_i] represents the index [i], which is a
         valid index into the list [xs]; the element [x] found at this
         index is OK; and no earlier element is OK. *)
      ∃ i , isInt _i i ∧ valid i xs ∧ OK (xs !!! i) ∧
      on_seg 0 i (λ j, notOK (xs !!! j))
  end.

(* The public specification of [find_index]. *)

Lemma wp_find_index a xs :
  isArray a xs →
  wp (find_index a) (λ out, find_index_inv xs (len xs) out).
Proof.
  intros. arrays. rewrite find_index_eq. unfold plain_find_index.
  wp_length _n.
  wp_op wp_uxiter_up with invariant: (find_index_inv xs);
  unfold find_index_inv in *.
  (* Initialization. *)
  { eauto with on_seg lia. }
  (* Preservation. *)
  { wp_uxiter_up_body _j j.
    wp_get x. subst x.
    wp_if; wp_bind_eq.
    (* Case: [OK x]. *)
    + wp_break. eauto.
    (* Case: [notOK x]. *)
    + eauto with on_seg. }
  (* Completion. *)
  { z. intros [|] (k&?&?).
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
  wp_op wp_find_index introducing: out.
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
  wp_op wp_find_index introducing: out.
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

Section Code.
Open Scope uint63.

Definition equal_aux _m a b : outcome unit :=
  uxiter_up 0 _m @@ λ _ _i continue break ,
  do x ← get a _i ;
  do y ← get b _i ;
  if eq x y then continue () else break ().

Definition equal a b : bool :=
  do _m ← length a ;
  do _n ← length b ;
  if _m =? _n then
    do out ← equal_aux _m a b ;
    did_not_break out
  else
    false.

End Code.

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
      on_seg 0 i (λ j, xs !!! j ≡ ys !!! j)
  | Break () =>
      (* [i - 1] is a valid index into the list [xs], the two lists
         agree up to index [i - 1], and they disagree at this index. *)
      let i := i - 1 in
      valid i xs ∧
      ¬ xs !!! i ≡ ys !!! i ∧
      on_seg 0 i (λ j, xs !!! j ≡ ys !!! j)
  end.

(* The public specification of [equal]. *)

Lemma wp_equal a xs b ys :
  isArray a xs →
  isArray b ys →
  wp (equal a b) (λ o,
      isBool1 o (Forall2 EQ xs ys)
  ).
Proof.
  intros. arrays. unfold equal.
  wp_length _m.
  wp_length _n.
  (* The second branch, where the lengths differ, is trivial. *)
  wp_if; [| wp_ret ].
  (* We focus on the first branch, where the lengths coincide. *)
  unfold equal_aux.
  wp_op wp_uxiter_up with invariant: (equal_inv xs ys);
  unfold equal_inv in *.
  (* Initialization. *)
  { eauto with on_seg lia. }
  (* Preservation. *)
  { wp_uxiter_up_body _j j.
    wp_get x. wp_get y.
    wp_if; wp_bind_eq; subst.
    (* Case: [eq x y] returns [true]. *)
    { wp_continue. eauto with on_seg. }
    (* Case: [eq x y] returns [false]. *)
    { wp_break. eauto with lia. }}
  (* Completion. *)
  { z. intros [[]|]; unfold equal_inv; intros (i&?); unpack.
    (* Case: the loop ends by breaking. *)
    { wp_ret. }
    (* Case: the loop ends normally. *)
    { assert (i = len xs) by tauto. wp_ret. }}
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
  wp_op wp_equal introducing: o. eapply isBool1_conseq; [ eauto |].
  (* [Forall2 (@eq A)] is the same as [@eq (list A)]. *)
  symmetry. eapply list_eq_Forall2.
Qed.

(* -------------------------------------------------------------------------- *)

(* [segment_iteri] and [iteri]. *)

(* An iteration function on an array is not super useful, as the user
   can just as well use [iter_up] or [iter_down] directly.
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
  iter_up _i _k s @@ λ _j s ,
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
  ITER_Z i k Up
    (λ j s Q, ∀ _j, isInt _j j → ∀ x, x = xs !!! j → wp (f _j x s) Q)
    (λ s Q, wp (segment_iteri a _i _k s f) Q).
Proof.
  intros. arrays. ITER. unfold segment_iteri.
  wp_op wp_iter_up introducing: ?.
  (* The loop body. *)
  { clear dependent s. wp_iter_up_body _j j s.
    wp_get x. }
Qed.

(* The public specification of [iteri]. *)

Lemma wp_iteri a xs f :
  isArray a xs →
  ITER_Z
    0 (len xs) Up
    (λ j s Q, ∀ _j, isInt _j j → ∀ x, x = xs !!! j → wp (f _j x s) Q)
    (λ s Q, wp (iteri a s f) Q).
Proof.
  intros. arrays. ITER. unfold iteri.
  wp_length _n.
  wp_op wp_segment_iteri introducing: ?.
Qed.

End Iteri.

(* Use [wp_segment_iteri_body _j j x s]
    or [wp_iteri_body _j j x s]
   at the start of the loop body. *)

Tactic Notation "wp_segment_iteri_body"
  simple_intropattern(_j) simple_intropattern(j)
  simple_intropattern(x) simple_intropattern(s) :=
  wp_body j ? s introducing: (fun _ => z_step; intros _j ?; wp_intro x).

Tactic Notation "wp_iteri_body"
  simple_intropattern(_j) simple_intropattern(j)
  simple_intropattern(x) simple_intropattern(s) :=
  wp_body j ? s introducing: (fun _ => z_step; intros _j ?; wp_intro x).

(* -------------------------------------------------------------------------- *)

(* [init]. *)

(* This resembles [of_list]. *)

Definition init `{Inhabited A} _n (f : int → A) : array A :=
  do a ← make _n inhabitant ;
  iter_up 0 _n a @@ λ _i a ,
  do x ← f _i ;
  set a _i x.

Lemma wp_init `{Inhabited A} _n n (f : int → A) (ψ : Z → A) :
  isInt _n n →
  0 ≤ n ≤ max_array_length →
  ( ∀IntU _i i, wp (f _i) (eq (ψ i)) ) →
  wp (init _n f) (λ a, isArray a (listz.init n ψ)).
Proof.
  intros. unfold init. wp_last Hf.
  wp_make a.
  wp_op wp_iter_up with invariant: (λ k a,
    isArray a (listz.init k ψ ++ replicate (n - k) inhabitant)
  ); last wp_shadow a.
  (* The loop body. *)
  { clear dependent a. wp_iter_up_body _k k a.
    wp_op Hf introducing: x.
    wp_set.
    isArray. }
  (* Completion. *)
  { isArray. }
Qed.
