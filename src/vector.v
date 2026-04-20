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
  list in Hx; unpack in Hx; wp_ret_hook.

(* -------------------------------------------------------------------------- *)

(* A (boxed) vector is a pair of a logical length [_n] and an array [a]. *)

(* Further down in this file, we also offer an unboxed-vector API. *)

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

Local Ltac introIsVectorLayers :=
  introIsVector; introIsVectorCap.

Local Ltac introIsVectorLayersWithWitness xs :=
  introIsVector; introIsVectorCapWithWitness xs.

Local Ltac destructIsVectorLayers :=
  destructIsVector; destructIsVectorCap.

Lemma isVector_bounded_length `{Inhabited A} (a : vector A) xs :
  isVector a xs →
  0 ≤ len xs ≤ max_array_length.
Proof.
  intros. destructIsVectorLayers.
  arrays. lengths. ulength in *. lia.
Qed.

(* Sometimes the fact that a vector has bounded length must be
   established a priori, at function definition time, as opposed to a
   posteriori, while verifying a function. However, with our current
   definition of the type [vector A], this is impossible: we would
   need to record a proof of [(length v ≤? max_length)%uint63 = true]. *)

(* -------------------------------------------------------------------------- *)

(* The tactic [vectors] looks for hypotheses of the form [isArray a xs]
   and introduces the fact [0 ≤ len xs ≤ max_array_length]. *)

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

(* The tactic [isVector] is applicable when the goal is [isVector v ys]
   and there is a hypothesis [isVector v xs]. The goal is then reduced
   to the equation [xs = ys], and this equation is simplified. If the
   equation is trivial then the goal is solved. *)

Ltac isVector :=
  match goal with
  | h: isVector ?v ?xs |- isVector ?v ?ys =>
    cut (xs = ys); [
      let Heq := fresh in intro Heq; try rewrite <- Heq; exact h
    | clear h;
      try subst; (* this can help *)
      lego
    ]
  end.

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
  introIsVectorLayers; tc.
Qed.

(* -------------------------------------------------------------------------- *)

(* Reading a vector's logical length: [length]. *)

Definition length (v : vector A) : int :=
  let '(_n, _) := v in
  _n.

Lemma wp_length v xs :
  isVector v xs →
  wp (length v) (λ _n, isInt _n (len xs)).
Proof.
  intros. destructIsVectorLayers. unfold length. wp_ret.
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
  intros. unfold get. destructIsVectorLayers. wp_get x.
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
  intros. unfold set. destructIsVectorLayers.
  wp_set. wp_ret.
  introIsVectorLayers; eauto.
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

(* A specification of [pop]. *)

Lemma wp_pop v xs :
  isVector v xs →
  0 < len xs →
  wp (pop v) (λ '(x, v),
    x = xs !!! (len xs - 1) ∧
    isVector v (initial_seg (len xs - 1) xs)
  ).
Proof.
  intros. unfold pop.
  destructIsVectorLayers.
  wp_get x. wp_ret. split; [ eauto |].
  introIsVectorLayersWithWitness ({[x]} ++ unoccupied); tc.
  subst x. isArray.
Qed.

(* An alternate specification of [pop]. *)

Lemma wp_pop' v xs :
  isVector v xs →
  0 < len xs →
  wp (pop v) (λ '(x, v),
    ∃ xs',
    isVector v xs' ∧
    xs = xs' ++ {[x]}
  ).
Proof.
  intros.
  wp_op wp_pop introducing: (x & v').
  eexists. split; [ eauto | lego ].
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
  destructIsVectorLayers.
  wp_make b. wp_blit. wp_ret.
  introIsVectorCap; tc.
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
  wp_ret. pack; tc7.
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
  wp_op wp_next_capacity introducing: _c'.
  wp_bind_eq.
  wp_op wp_grow shadowing: a.
Qed.

(* -------------------------------------------------------------------------- *)

(* Pushing an element onto the end of a vector: [push]. *)

Section Code.
Open Scope uint63.

Definition push v x : vector A :=
  let (_n, a) := v in
  (* Ensure that sufficient space exists. *)
  let _n' := _n + 1 in
  do _c ← PArray.length a ;
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
    + wp_ret.
    (* Case: the array must be grown. *)
    + wp_op wp_really_ensure_capacity shadowing: a. }
  clear dependent a unoccupied. intros a (c' & ? & ?).
  destructIsVectorCap.
  (* Write; return. *)
  wp_set. wp_ret.
  introIsVectorLayersWithWitness (final_seg 1 unoccupied); tc.
  isArray.
Qed.

(* -------------------------------------------------------------------------- *)

(* Reserving an element onto the end of a vector: [reserve]. *)

(* This is analogous to [push], but does not initialize the new slot. *)

Section Code.
Open Scope uint63.

Definition reserve v : vector A :=
  let (_n, a) := v in
  (* Ensure that sufficient space exists. *)
  let _n' := _n + 1 in
  do _c ← PArray.length a ;
  do a ← (
    if _n' ≤? _c then a
    else really_ensure_capacity v _n'
  ) ;
  (* A free slot now exists. *)
  (_n', a).

End Code.

Lemma wp_reserve v xs :
  isVector v xs →
  len xs + 1 ≤ max_array_length →
  wp (reserve v) (λ v, ∃ x, isVector v (xs ++ {[x]})).
Proof.
  intros. unfold reserve.
  destructIsVector. destructAndKeepIsVectorCap.
  wp_length _c.
  eapply wp_bind with (P := λ a,
    isVectorCapLe (_n, a) xs (len xs + 1)
  ).
  { wp_if.
    + wp_ret.
    + wp_op wp_really_ensure_capacity shadowing: a. }
  clear dependent a unoccupied. intros a (c' & ? & ?).
  destructIsVectorCap.
  wp_ret.
  set (x := unoccupied !!! 0). exists x.
  introIsVectorLayersWithWitness (final_seg 1 unoccupied); tc.
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
  destructIsVectorLayers.
  wp_op array.wp_segment_iteri introducing: ?.
  (* The loop body. *)
  { clear dependent s. wp_segment_iteri_body _j j x s. }
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
  destructIsVectorLayers.
  wp_op array.wp_segment_iteri introducing: ?.
  (* The loop body. *)
  { clear dependent s. wp_iteri_body _j j x s. }
Qed.

End Iteri.

(* We do not provide tactics [wp_segment_iteri_body]
   and [wp_iteri_body]; the ones in array.v should work. *)

(* -------------------------------------------------------------------------- *)

(* Converting an array to a vector: [steal_array] and [of_array]. *)

(* In [steal_array], the array is not copied; it becomes part of the
   representation of the vector. In [of_array], it is copied. *)

Definition steal_array a : vector A :=
  do _n ← PArray.length a ;
  (_n, a).

Definition of_array a : vector A :=
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
  introIsVectorLayersWithWitness ([] : list A); tc.
Qed.

(* The public specification of [of_array]. *)

Lemma wp_of_array a xs :
  isArray a xs →
  wp (of_array a) (λ v, isVector v xs).
Proof.
  intros. unfold of_array.
  wp_op wp_copy introducing: b.
  eapply wp_steal_array.
  eauto.
Qed.

(* -------------------------------------------------------------------------- *)

End Operations.

(* The tactic [wp_pop x] reasons about a call [pop v]. It assumes that
   [v] is a variable and that we want to shadow this variable, so the
   user introduces just [x]. *)

Tactic Notation "wp_pop" simple_intropattern(x) :=
  match goal with |- context[pop ?v] =>
    wp_op wp_pop'; last (
      let xs' := fresh "xs'" in
      clear dependent v; intros (x & v) (xs' & ? & ?);
      generalize (length_nonneg xs'); intro
    )
  end.

(* The tactic [subst_pop] looks for a hypothesis [xs = xs' ++ {[x]}],
   substitutes [xs] away, and renames [xs'] into [xs]. It can be used
   immediately after [wp_pop x]. *)

Ltac subst_pop :=
  match goal with
  h: ?xs = ?xs' ++ {[_]} |- _ =>
    subst xs; rename xs' into xs; ulength in *
  end.

Ltac wp_steal_array :=
  match goal with |- context[steal_array ?a] =>
    wp_op wp_steal_array shadowing: a
  end.

Ltac wp_of_array v :=
  wp_op wp_of_array introducing: v.

(* -------------------------------------------------------------------------- *)

Section OfList.
Context `{Inhabited A}.
Implicit Types xs : list A.

(* Converting a list to a vector: [of_list]. *)

Definition of_list xs : vector A :=
  do a ← array.of_list xs ;
  steal_array a.

(* The public specification of [of_list]. *)

Lemma wp_of_list xs :
  len xs ≤ max_array_length →
  wp (of_list xs) (λ v, isVector v xs).
Proof.
  intros. unfold of_list.
  wp_op array.wp_of_list introducing: a.
  wp_steal_array.
Qed.

End OfList.

Ltac wp_of_list v :=
  wp_op wp_of_list introducing: v.

(* -------------------------------------------------------------------------- *)

(* The unboxed-vector API. *)

(* In this API, the two components of a vector, namely [_n] and [a],
   are not necessarily stored together in a pair. It is up to the user
   to decide whether and where they are stored. This API allows
   updating a vector via a primitive array [set] operation, as opposed
   to a [vector.set] operation, which allocates a new pair. *)

(* The assertion [isUnboxedVector _n a xs] means that [_n] and [a]
   together form an unboxed vector. *)

Notation isUnboxedVector _n a xs :=
  (isVector (_n, a) xs).

Module unboxed.
Section U.
Context `{Inhabited A}.
Implicit Types a : array A.

(* The length of an unboxed vector is represented by [_n]. *)

Lemma wp_length _n a xs :
  isUnboxedVector _n a xs →
  isInt _n (len xs).
Proof.
  intros. destructIsVectorLayers. eauto.
Qed.

Lemma wp_length' _n a xs :
  isUnboxedVector _n a xs →
  ∀ n, isInt _n n → unsigned n →
  n = len xs.
Proof.
  intros. destructIsVectorLayers. eapply isInt_inj_2; tc.
Qed.

(* An unboxed vector can be converted (at no cost) to an array,
   and back. This can be understood as "borrowing" the array
   from the vector and returning it. *)

Lemma wp_borrow_begin :
  ∀Int _n n,
  ∀ a xs,
  isUnboxedVector _n a xs →
  ∃ unoccupied,
  isArray a (xs ++ unoccupied).
Proof.
  intros. destructIsVectorLayers. eauto.
Qed.

Lemma wp_borrow_end :
  ∀Int _n n,
  ∀ a xs unoccupied,
  n = len xs →
  isArray a (xs ++ unoccupied) →
  isUnboxedVector _n a xs.
Proof.
  intros. subst. introIsVectorLayers; eauto.
Qed.

Lemma wp_get _n a xs :
  isUnboxedVector _n a xs →
  ∀Int _i i,
  valid i xs →
  wp a.[_i] (λ x, x = xs !!! i).
Proof.
  intros. destructIsVectorLayers. wp_get x.
Qed.

Lemma wp_set _n a xs x :
  isUnboxedVector _n a xs →
  ∀Int _i i,
  valid i xs →
  wp (a.[_i <- x]) (λ a, isUnboxedVector _n a (<[i := x]>xs)).
Proof.
  intros. destructIsVectorLayers. wp_set. introIsVectorLayers; eauto.
Qed.

Lemma wp_truncate _n a xs :
  isUnboxedVector _n a xs →
  ∀Int _i i ,
  0 ≤ i ≤ len xs →
  isUnboxedVector _i a (initial_seg i xs).
Proof.
  intros. destructIsVectorLayers.
  introIsVectorLayersWithWitness (final_seg i xs ++ unoccupied); tc.
  isArray.
Qed.

Lemma wp_pop _n a xs x :
  isUnboxedVector _n a (xs ++ {[x]}) →
  isUnboxedVector (_n - 1)%uint63 a xs.
Proof.
  intros.
  replace xs with (initial_seg (len xs) (xs ++ {[x]})) by lego.
  eapply wp_truncate; tc.
  { assert (isInt _n (len (xs ++ {[x]}))) by eauto using wp_length.
    length in *. replace (len xs) with (len xs + 1 - 1) by lia. tc. }
Qed.

End U.
End unboxed.
