From stdpp Require Import numbers list.
From listz Require Import listz.
Notation len := length.
From Stdlib Require Import Uint63.
From Stdlib Require Import Array.PArray.
From marble Require Import tactics bool iteration int wp array.
Implicit Types _i _j _k _n : int.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

Local Ltac wp_intro_hook Hx ::=
  (* Simplify expressions that involve lists and arithmetic. *)
  list in Hx;
  (* Decompose existential quantifiers and conjunctions. *)
  unpack in Hx.

(* -------------------------------------------------------------------------- *)

(* A vector is a pair of a logical length [_n] and an array [a]. *)

Definition vector (A : Type) :=
  (int * array A)%type.

(* The proposition [isVectorCap v xs c] means that [v] is a vector whose
   logical content is [xs] and whose capacity is [c]. *)

Definition isVectorCap `{Inhabited A} (v : vector A) (xs : list A) c :=
  let (_n, a) := v in
  ∃ unoccupied,
  isInt _n (len xs) ∧
  isArray a (xs ++ unoccupied) ∧
  len xs + len unoccupied = c.

(* The proposition [isVectorCapLe v xs c] means that [v] is a vector whose
   logical content is [xs] and whose capacity is at least [c]. *)

Notation isVectorCapLe v xs c :=
  (∃ c', isVectorCap v xs c' ∧ c ≤ c').

(* The proposition [isVector v xs] means that [v] is a vector whose
   logical content is [xs]. *)

Definition isVector `{Inhabited A} (v : vector A) (xs : list A) :=
  ∃ c, isVectorCap v xs c.

(* These tactics and lemmas help work with the above propositions. *)

Local Ltac introIsVector :=
  unfold isVector; eexists.

Local Ltac introIsVectorCap :=
  unfold isVectorCap; eexists; list;
  split; [| split ].

Local Ltac introIsVectorCapWithWitness unoccupied :=
  unfold isVectorCap; exists unoccupied; list;
  split; [| split ].

Local Ltac destructIsVector :=
  match goal with h: isVector ?v _ |- _ =>
    unfold isVector in h;
    let c := fresh "c" in
    destruct h as (c&?)
  end.

Local Ltac destructVector v :=
  match v with
  | (_, _) => idtac
  | _ =>
    let _n := fresh "_n" in
    let a := fresh "a" in
    destruct v as [ _n a ]
  end.

Local Ltac destructIsVectorCap :=
  match goal with h: isVectorCap ?v _ _ |- _ =>
    destructVector v;
    let u := fresh "unoccupied" in
    destruct h as (u&?&?&?)
  end.

Local Ltac destructAndKeepIsVectorCap :=
  match goal with h: isVectorCap ?v _ _ |- _ =>
    destructVector v;
    let u := fresh "unoccupied" in
    generalize h;
    intros (u&?&?&?)
  end.

Lemma isVector_bounded_length `{Inhabited A} (a : vector A) xs :
  isVector a xs →
  0 ≤ len xs ≤ max_array_length.
Proof.
  intros. destructIsVector. destructIsVectorCap.
  arrays. lengths. ulength in *. lia.
Qed.

(* -------------------------------------------------------------------------- *)

(* The tactic [vectors] looks for hypotheses of the form [isArray a xs]
   and introduces the fact [0 ≤ len xs ≤ max_array_length]. Furthermore,
   it simplifies the expression [len xs] using the tactic [length]. *)

Ltac vectors :=
  repeat match goal with
  h: isVector ?a ?xs |- _ =>
    let h' := fresh h in
    generalize (isVector_bounded_length a xs h); intro h';
    revert h h'
  end;
  intros;
  (* We also introduce [unsigned max_array_length]. *)
  generalize unsigned_max_array_length; intro.

(* We let [lia] invoke [vectors; arrays; lengths]. *)

(* We do not make this a setting, because this might disturb or
   surprise the user. We expect the user to reproduce and adapt this
   setting in every file. *)

Local Ltac Zify.zify_pre_hook ::=
  vectors; arrays; lengths; ulength in *.

(* -------------------------------------------------------------------------- *)

Section Operations.
Context `{Inhabited A}.
Implicit Types v : vector A.
Implicit Types xs : list A.
Implicit Types a b : array A.

(* -------------------------------------------------------------------------- *)

(* [capacity v] returns the current capacity of the vector [v]. *)

Local Definition capacity v : int :=
  let '(_, a) := v in
  length a.

(* -------------------------------------------------------------------------- *)

(* Creating an empty vector: [create]. *)

(* A new vector has logical length 0 and physical capacity 0. *)

Section Code.
Open Scope uint63.

Definition create (_ : unit) : vector A :=
  let _n := 0 in
  do a ← make _n inhabitant ;
  (_n, a).

End Code.

Lemma wp_create :
  wp (create ()) (λ v, isVector v []).
Proof.
  unfold create. wp_make a. wp_ret.
  introIsVector. introIsVectorCap; tc.
Qed.

(* -------------------------------------------------------------------------- *)

(* Random access: [get] and [set]. *)

Definition get v _i : A :=
  let (_n, a) := v in
  a.[_i].

Lemma wp_get v xs _i i :
  isInt _i i →
  isVector v xs →
  valid i xs →
  wp (get v _i) (λ x, x = xs !!! i).
Proof.
  intros. unfold get.
  destructIsVector. destructIsVectorCap.
  wp_get x. eauto.
Qed.

Definition set v _i x : vector A :=
  let (_n, a) := v in
  do a ← a.[_i <- x] ;
  (_n, a).

Lemma wp_set v xs _i i x :
  isInt _i i →
  isVector v xs →
  valid i xs →
  wp (set v _i x) (λ v', isVector v' (<[i := x]>xs)).
Proof.
  intros. unfold set.
  destructIsVector. destructIsVectorCap.
  wp_set. wp_ret.
  introIsVector. introIsVectorCap; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Popping an element off the end of a nonempty vector: [pop]. *)

(* The newly emptied slot is not overwritten with a default value. *)

Section Code.
Open Scope uint63.

Definition pop v : A * vector A :=
  let (_n, a) := v in
  let _i := _n - 1 in
  do x ← a.[_i] ;
  (x, (_i, a)).

End Code.

Lemma wp_pop v xs :
  isVector v xs →
  0 < len xs →
  wp (pop v) (λ '(x, v),
    let i := len xs - 1 in
    x = xs !!! i ∧
    isVector v (initial_seg i xs)
  ).
Proof.
  intros. unfold pop.
  destructIsVector. destructIsVectorCap.
  wp_get x. wp_ret. split; [ eauto |].
  introIsVector.
  introIsVectorCapWithWitness ({[x]} ++ unoccupied); tc.
  subst x. isArray.
Qed.

(* -------------------------------------------------------------------------- *)

(* Growing a vector requires allocating a new array and migrating
   the existing data into it. *)

(* In [grow v _c], [_c] is the desired capacity of the new array. *)

(* [grow] returns just the new array, not a vector.
   The logical length of the vector is unchanged. *)

Local Definition grow v _c : array A :=
  let '(_n, a) := v in
  do b ← make _c inhabitant ;
  do b ← blit a 0 b 0 _n ;
  b.

Local Lemma wp_grow _n a xs _c c :
  isVector (_n, a) xs →
  isInt _c c →
  len xs ≤ c ≤ max_array_length →
  wp (grow (_n, a) _c) (λ b,
    isVectorCap (_n, b) xs c
  ).
Proof.
  intros. unfold grow.
  destructIsVector. destructIsVectorCap.
  wp_make b. wp_blit. wp_ret.
  introIsVectorCap; eauto.
  lia.
Qed.

(* -------------------------------------------------------------------------- *)

(* [next_capacity _c] returns a new capacity that is at most equal to
   [max_array_length] and (in practice) at least as great as [_c], but
   this fact is not used in the proof.  *)

Section Code.
Open Scope uint63.

Local Definition next_capacity _c : int :=
  (* If the current capacity [_c] is small, multiply it by 2;
     otherwise multiply it by 3/2.  *)
  do _c ← (
    if _c ≤? 512 then _c * 2
    else _c + _c / 2
  ) ;
  (* Clip it, so that it is at least 8 and at most [max_array_length]. *)
  _min max_length (_max 8 _c).

End Code.

Lemma wp_next_capacity :
  ∀IntU _c c,
  c ≤ max_array_length →
  wp (next_capacity _c) (λ _c', ∃ c',
    isIntU _c' c' ∧ (* c ≤ *) c' ≤ max_array_length
  ).
Proof.
  intros. unfold next_capacity.
  (* First, reason about the [if] construct. *)
  eapply wp_bind with (P := λ _c', ∃ c', isIntU _c' c'). (* c ≤ c' ∧ *)
  {
    (* Lots of preliminary remarks about machine integers. *)
    generalize unsigned_twice_max_array_length; intro. (* UGLY *)
     wp_if; wp_ret; eexists; split; tc. }
  wp_intro _c'.
  wp_ret.
  eexists; split; tc.
Qed.

(* -------------------------------------------------------------------------- *)

(* [really_ensure_capacity v _n'] ensures that the capacity of
   the vector [v] is at least [_n']. It returns a new array. *)

Definition really_ensure_capacity v _n' : array A :=
  (* Get the current capacity [_c] of the vector. *)
  do _c ← capacity v ;
  (* We assume that [_n'] is greater than [_c], so [grow] must be called.
     The new capacity is computed based on the current capacity, and is
     adjusted so as to be at least [_n']. *)
  do _c' ← next_capacity _c ;
  do _c' ← _max _c' _n' ;
  grow v _c'.

Lemma wp_really_ensure_capacity _n a xs c :
  isVectorCap (_n, a) xs c →
  ∀Int _n' n',
  c < n' ≤ max_array_length →
  wp (really_ensure_capacity (_n, a) _n') (λ a ,
    isVectorCapLe (_n, a) xs n'
  ).
Proof.
  intros. unfold really_ensure_capacity, capacity.
  assert (isVector (_n, a) xs). { introIsVector. eauto. }
  destructIsVectorCap.
  wp_length _c.
  wp_op_intro wp_next_capacity _c'.
  wp_bind_eq.
  wp_op_shadow wp_grow a.
  eauto with lia.
Qed.

(* -------------------------------------------------------------------------- *)

(* Pushing an element onto the end of a vector: [push]. *)

Section Code.
Open Scope uint63.

Definition push v x : vector A :=
  let (_n, a) := v in
  (* Ensure that sufficient space exists. *)
  let _n' := _n + 1 in
  do _c ← length a ;
  do a ← (
    if _n' ≤? _c then a
    else really_ensure_capacity v _n'
  ) ;
  (* A free slot now exists. *)
  do a ← a.[_n <- x] ;
  (_n', a).

End Code.

Lemma wp_push v xs x :
  isVector v xs →
  len xs + 1 ≤ max_array_length →
  wp (push v x) (λ v, isVector v (xs ++ {[x]})).
Proof.
  intros. unfold push.
  destructIsVector. destructAndKeepIsVectorCap.
  wp_length _c.
  (* We are looking at the [if] construct. At the join point,
     at least one free slot exists in the array. Indeed, the
     new capacity [c'] is at least [len xs + 1]. *)
  eapply wp_bind with (P := λ a,
    isVectorCapLe (_n, a) xs (len xs + 1)
  ).
  { wp_if.
    (* Case: there is still room. *)
    + wp_ret. eauto with lia.
    (* Case: the array must be grown. *)
    + wp_op_shadow wp_really_ensure_capacity a.
      eauto. }
  clear dependent unoccupied. (* A bit ad hoc. *)
  wp_shadow a.
  destructIsVectorCap.
  (* Write; return. *)
  wp_set. wp_ret.
  introIsVector.
  introIsVectorCapWithWitness (final_seg 1 unoccupied); tc.
  isArray.
Qed.

(* -------------------------------------------------------------------------- *)

(* [segment_iteri] and [iteri]. *)

Section Iteri.
Context {S : Type}.
Implicit Types s : S.
Implicit Types f : int → A → S → S.

(* The code. *)

Definition segment_iteri v _i _k s f : S :=
  let (_n, a) := v in
  array.segment_iteri a _i _k s f.

Definition iteri v s f :=
  let (_n, a) := v in
  array.segment_iteri a 0 _n s f.

(* The public specification of [segment_iteri]. *)

Lemma wp_segment_iteri v xs f :
  isVector v xs →
  ∀Int _i i ,
  ∀Int _k k ,
  valid_seg i k xs →
  ITER_Z i k Up
    (λ j s Q, ∀ _j, isInt _j j → ∀ x, x = xs !!! j → wp (f _j x s) Q)
    (λ s Q, wp (segment_iteri v _i _k s f) Q).
Proof.
  intros. ITER. unfold segment_iteri.
  destructIsVector. destructIsVectorCap.
  wp_loop @array.wp_segment_iteri inv.
  clear dependent s.
  (* The loop body. *)
  { wp_up_intros j s. intros _j ?. wp_intro x.
    wp_op_shadow Hstep s.
    assumption. }
Qed.

(* The public specification of [iteri]. *)

Lemma wp_iteri v xs f :
  isVector v xs →
  ITER_Z
    0 (len xs) Up
    (λ j s Q, ∀ _j, isInt _j j → ∀ x, x = xs !!! j → wp (f _j x s) Q)
    (λ s Q, wp (iteri v s f) Q).
Proof.
  intros. ITER. unfold iteri.
  destructIsVector. destructIsVectorCap.
  wp_loop @array.wp_segment_iteri inv.
  clear dependent s.
  (* The loop body. *)
  { wp_up_intros j s. intros _j ?. wp_intro x.
    wp_op_shadow Hstep s.
    assumption. }
Qed.

End Iteri.

(* -------------------------------------------------------------------------- *)

(* Converting an array to a vector: [steal_array] and [of_array]. *)

(* In [steal_array], the array is not copied; it becomes part of the
   representation of the vector. In [of_array], it is copied. *)

Definition steal_array a :=
  do _n ← length a ;
  (_n, a).

Definition of_array a :=
  do a ← array.copy a ;
  steal_array a.

(* The public specification of [steal_array]. *)

Lemma wp_steal_array a xs :
  isArray a xs →
  wp (steal_array a) (λ v, isVector v xs).
Proof.
  intros. unfold steal_array.
  wp_length _n.
  wp_ret.
  introIsVector.
  introIsVectorCapWithWitness ([] : list A); tc.
Qed.

(* The public specification of [of_array]. *)

Lemma wp_of_array a xs :
  isArray a xs →
  wp (of_array a) (λ v, isVector v xs).
Proof.
  intros. unfold of_array.
  wp_copy b.
  eapply wp_steal_array.
  eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Borrowing an array from a vector. *)

(* [read_borrow] allows the array to be read by the function [body].
   The unoccupied space has unspecified length and therefore cannot
   be accessed. *)

Definition read_borrow {B} v (body : array A → B) : B :=
  let (_n, a) := v in
  body a.

(* The public specification of [read_borrow]. *)

Lemma wp_read_borrow {B} v xs body (Q : B → Prop) :
  isVector v xs →
  ( ∀ a unoccupied,
    isArray a (xs ++ unoccupied) →
    wp (body a) Q
  ) →
  wp (read_borrow v body) Q.
Proof.
  intros. destructIsVector. destructIsVectorCap. unfold read_borrow.
  eauto.
Qed.

(* [read_write_borrow] allows the array to be read and updated by
   the function [body]. This function must return a pair of its
   main result and the updated array. The unoccupied space has
   unspecified length and therefore cannot be accessed. *)

Definition read_write_borrow {B} v (body : array A → B * array A)
: B * vector A :=
  let (_n, a) := v in
  do (b, a) ← body a ;
  let v := (_n, a) in
  (b, v).

(* The public specification of [read_write_borrow]. *)

Lemma wp_read_write_borrow {B} v xs body (Q  : B * vector A → Prop) :
  isVector v xs →
  ( ∀ a unoccupied,
    isArray a (xs ++ unoccupied) →
    wp (body a) (λ '(b, a),
      ∃ xs' unoccupied',
      isArray a (xs' ++ unoccupied') ∧
      len xs = len xs' ∧
      (∀ v, isVector v xs' → Q (b, v))
    )
  ) →
  wp (read_write_borrow v body) Q.
Proof.
  intros ? Hbody.
  destructIsVector. destructIsVectorCap. unfold read_write_borrow.
  wp_op_intro Hbody ba. wp_last Hpost.
  clear dependent a. destruct ba as [ b a ].
  destruct Hpost as (xs' & unoccupied' & Hpost). unpack in Hpost.
  wp_ret.
  eapply Hpost1. introIsVector.
  introIsVectorCap; eauto. congruence.
Qed.

(* -------------------------------------------------------------------------- *)

End Operations.

Ltac wp_steal_array :=
  match goal with |- context[steal_array ?a] =>
    wp_op_shadow wp_steal_array a
  end.

Ltac wp_of_array b :=
  wp_op_intro wp_of_array b.

(* -------------------------------------------------------------------------- *)

Section OfList.
Context `{Inhabited A}.
Implicit Types xs : list A.

(* Converting a list to a vector: [of_list]. *)

Definition of_list xs :=
  do a ← array.of_list xs ;
  steal_array a.

(* The public specification of [of_list]. *)

Lemma wp_of_list xs :
  len xs ≤ max_array_length →
  wp (of_list xs) (λ v, isVector v xs).
Proof.
  intros. unfold of_list.
  wp_op_intro @array.wp_of_list a.
  wp_steal_array.
  eauto.
Qed.

End OfList.

Ltac wp_of_list v :=
  wp_op_intro wp_of_list v.
