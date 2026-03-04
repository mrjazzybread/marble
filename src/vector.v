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

(* -------------------------------------------------------------------------- *)

Section Operations.
Context `{Inhabited A}.
Implicit Types v : vector A.
Implicit Types xs : list A.
Implicit Types a b : array A.

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

(* [grow] is an internal function. It returns just the new array,
   not a vector. The logical length of the vector is unchanged. *)

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

(* TODO WIP here *)

Definition capacity v : int :=
  let '(_, a) := v in
  length a.

Local Definition next_capacity _c : int :=
  do _k ← (
    if (_c ≤? 512)%uint63 then (_c * 2)%uint63
    else (_c + _c / 2)%uint63
  ) ;
  _min max_length (_max 8%uint63 _k).

(* TODO *
Hint Extern 1 (isInt _ _) =>
  match goal with
  | |- isInt ?_i ?i =>
    is_evar _i
  | |- isInt ?_i ?i =>
    eapply introIsInt'
  end;
  fail "evar"
: int.
 *)

Lemma isInt_next_capacity _c c :
  isInt _c c →
  c ≤ max_array_length →
  wp (next_capacity _c) (λ _c', ∃ c',
    isInt _c' c' ∧ c ≤ c' ∧ c' ≤ max_array_length
  ).
Proof.
  intros. unfold next_capacity.
  eapply wp_bind with (P := λ _c', ∃ c',
    isInt _c' c' ∧ c ≤ c' ∧ representable c').
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
     wp_if; wp_ret; eauto 7 with int lia representable.
  }
  intros _k (c'&?&?&?).
  wp_ret.
  (* Another remark. *)
  assert (isInt 8 8) by eauto with int. (* TODO *)
  (* (* Now conclude. *) *)
  (* This proof is not as concise as I would like.
     [eauto] with hints does not work as expected. *)
  eexists. split.
  { eapply isInt_min.
    + eauto using max_length_spec.
    + eauto with int representable.
    + eauto with representable.
    + eauto using max_representable with representable. }
  { lia. }
Qed.

(* TODO *)
(* _r : request *)
(* _c : capacity *)
Definition really_ensure_capacity v _r : array A :=
  do _c ← capacity v ;
  do _c' ← (
    if (_r ≤? _c)%uint63 then _c
    else _max (next_capacity _c) _r
  ) ;
  grow v _c'.

Lemma wp_really_ensure_capacity v xs _n' n' :
  isInt _n' n' →
  representable n' →
  n' ≤ max_array_length →
  wp (really_ensure_capacity v _n') (λ a ,
    ∃ unoccupied,
    isArray a (xs ++ unoccupied) ∧
    n' ≤ len xs + len unoccupied
  ).
Proof.
Admitted.

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
  destructIsVector. destructIsVectorCap.
  wp_length _c.
  (* We are looking at the [if] construct. At the join point,
     at least one free slot exists in the array. *)
  eapply wp_bind with (P := λ a,
    ∃ unoccupied',
    isArray a (xs ++ unoccupied') ∧
    len xs + 1 ≤ len xs + len unoccupied'
      (* equivalent to: 0 < len unoccupied' *)
  ).
  { wp_if.
    (* Case: there is still room. *)
    + wp_ret. eauto with lia.
    (* Case: the array must be grown. *)
    + eauto using wp_really_ensure_capacity with int representable. }
  clear dependent a unoccupied. intros a (unoccupied & ? & ?).
  (* Write; return. *)
  wp_set. wp_ret.
  introIsVector.
  introIsVectorCapWithWitness (final_seg 1 unoccupied); eauto with int.
  isArray.
  rewrite (seg_intro unoccupied) at 1. list. eauto.
Qed.

(* -------------------------------------------------------------------------- *)

End Operations.
