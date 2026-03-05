From stdpp Require Import numbers list.
Local Notation len := List.length.
From Stdlib Require Import Uint63.
From Stdlib Require Import Array.PArray.
From array Require Import tactics list_extra bool int wp array.
Implicit Types _i _j _k _n : int.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

Open Scope nat_scope.

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

Definition create (_ : unit) : vector A :=
  let _n := 0%uint63 in
  do a ← make _n inhabitant ;
  (_n, a).

Lemma wp_create :
  wp (create ()) (λ v, isVector v []).
Proof.
  unfold create. wp_make a. wp_ret.
  introIsVector. introIsVectorCap; eauto with int.
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

Definition pop v : A * vector A :=
  let (_n, a) := v in
  let _i := (_n - 1)%uint63 in
  do x ← a.[_i] ;
  (x, (_i, a)).

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
  introIsVectorCapWithWitness ({[x]} ++ unoccupied); eauto with int.
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
  introIsVectorCap; eauto with int.
  list. lia.
Qed.

(* -------------------------------------------------------------------------- *)

(* [next_capacity _c] returns a new capacity that is at most equal to
   [max_array_length] and (in practice) at least as great as [_c], but
   this fact is not used in the proof.  *)

Local Definition next_capacity _c : int :=
  (* If the current capacity [_c] is small, multiply it by 2;
     otherwise multiply it by 3/2.  *)
  do _c ← (
    if (_c ≤? 512)%uint63 then (_c * 2)%uint63
    else (_c + _c / 2)%uint63
  ) ;
  (* Clip it, so that it is at least 8 and at most [max_array_length]. *)
  _min max_length (_max 8%uint63 _c).

Lemma wp_next_capacity _c c :
  isInt _c c →
  c ≤ max_array_length →
  wp (next_capacity _c) (λ _c', ∃ c',
    isInt _c' c' ∧ (* c ≤ *) c' ≤ max_array_length
  ).
Proof.
  intros. unfold next_capacity.
  (* First, reason about the [if] construct. *)
  eapply wp_bind with (P := λ _c', ∃ c',
    isInt _c' c' ∧ (* c ≤ c' ∧ *) representable c').
  {
    (* Lots of preliminary remarks about machine integers. *)
    assert (isInt 2 2) by eauto with int. (* TODO *)
    assert (isInt 512 512) by eauto with int. (* TODO *)

    generalize representable_twice_max_array_length; intro.
    assert (representable (c * 2)).
    { rewrite representable_iff_nat in *. lia. }
    assert (representable (c + c `div` 2)).
    { assert (c `div` 2 ≤ c) by eauto with lia.
      rewrite representable_iff_nat in *. lia. }
    (* Now conclude. *)
     wp_if; wp_ret; eauto 7 with int lia typeclass_instances.
  }
  intros _c' (c'&?). unpack.
  wp_ret.
  (* Another remark. *)
  assert (isInt 8 8) by eauto with int. (* TODO *)
  (* (* Now conclude. *) *)
  (* This proof is not as concise as I would like.
     TODO once [isInt] is a type class, clean up? *)
  eexists. split.
  { eapply isInt_min.
    + eauto using max_length_spec.
    + eauto with int typeclass_instances.
    + eauto with typeclass_instances.
    + eauto with typeclass_instances. }
  { lia. }
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

Lemma wp_really_ensure_capacity _n a xs c _n' n' :
  isVectorCap (_n, a) xs c →
  isInt _n' n' →
  representable n' →
  c < n' ≤ max_array_length →
  wp (really_ensure_capacity (_n, a) _n') (λ a ,
    isVectorCapLe (_n, a) xs n'
  ).
Proof.
  intros. unfold really_ensure_capacity, capacity.
  assert (isVector (_n, a) xs). { introIsVector. eauto. }
  destructIsVectorCap.
  wp_length _c.
  (* TODO define tactic for [wp_next_capacity]? *)
  eapply wp_bind.
  { eapply wp_next_capacity; eauto with lia. }
  cbv beta. intros _c' (c'&?). unpack.
  wp_bind_eq.
  (* TODO define tactic for [wp_grow]? *)
  eapply wp_conseq.
  { eapply wp_grow; eauto with int typeclass_instances lia. }
  cbv beta. clear dependent a. intros a ?.
  (* Conclude. *)
  eauto with lia.
Qed.

(* -------------------------------------------------------------------------- *)

(* Pushing an element onto the end of a vector: [push]. *)

Definition push v x : vector A :=
  let (_n, a) := v in
  (* Ensure that sufficient space exists. *)
  let _n' := (_n + 1)%uint63 in
  do _c ← length a ;
  do a ← (
    if (_n' ≤? _c)%uint63 then a
    else really_ensure_capacity v _n'
  ) ;
  (* A free slot now exists. *)
  do a ← a.[_n <- x] ;
  (_n', a).

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
    + eauto using wp_really_ensure_capacity with int typeclass_instances lia.
  }
  clear dependent a unoccupied. (* TODO automate *)
  intros a (c' & ? & ?).
  destructIsVectorCap.
  (* Write; return. *)
  wp_set. wp_ret.
  introIsVector.
  introIsVectorCapWithWitness (final_seg 1 unoccupied); eauto with int.
  isArray.
  rewrite (seg_intro unoccupied) at 1. list. eauto.
Qed.

(* -------------------------------------------------------------------------- *)

End Operations.
