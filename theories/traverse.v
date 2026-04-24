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
From Stdlib Require Export ZifyNat ZifyUint63.
From marble Require Import tactics bool int iteration loop wp array.
From marble.logic Require Import olt.
From marble Require Import listz_buffer. (* TODO *)
Implicit Type _i _j _k _n : int.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

(* This file defines depth-first search algorithms. *)

(* -------------------------------------------------------------------------- *)

(* We assume that the vertices of the graph are numbered from 0 to [n-1].
   This assumption allows us to mark vertices by maintaining an array of
   Boolean marks. This is simple and efficient. *)

Local Notation vertex := int.
Local Notation marks  := (array bool).

Implicit Type v w : vertex.
Implicit Type vs ws : list vertex.
Implicit Type m : marks.

(* -------------------------------------------------------------------------- *)

(* The weight of an array [m] is defined as the number of unmarked
   vertices in this array. It is a natural number. This number is
   used to establish the termination of the algorithm. *)

Local Definition unmarked (b : bool) : nat :=
  if b then 0 else 1.

(* We wish to record the invariant [default m = true]. That is, outside of
   the bounds of the marks array, every vertex is considered marked.
   Therefore, if an out-of-bounds vertex is encountered, then the
   algorithm ignores it. This lets us prove termination without imposing
   any conditions on the vertices that the algorithm receives as
   parameters. Of course, later on (a posteriori), we can use [wp]-style
   specifications to ensure that every vertex lies within the desired
   bounds. *)

(* To record this invariant, we use a partial measure. That is, instead
   of [mweight : marks → nat], we define [mweight : marks → option nat],
   with the convention that if [m] does not satisfy the invariant then
   [mweight m] is [None]. *)

(* Because [None] is not an accessible element of the ordering that we
   impose on the type [option nat], a witness of accessibility of
   [mweight m] implies that [mweight m] is not [None], therefore implies
   that [m] satisfies the invariant. *)

Definition mweight m : option nat :=
  if default m then Some (sum_with unmarked m) else None.

Local Notation olt :=
  (@olt nat Nat.lt).

Local Notation ole :=
  (@ole nat Nat.lt).

(* -------------------------------------------------------------------------- *)

(* The state of the depth-first search algorithm is a pair [(m, u)] where
   [m] is the marks array and [u] is a user state of arbitrary type [U]. *)

Section S.

(* The user state. *)

Variable U : Type.
Implicit Type u : U.

(* A state [s] is a pair [(m, u)]. *)

Definition S : Type := marks * U.
Implicit Type s : S.

(* The notion of weight is extended to states. *)

Definition weight s :=
  let (m, _) := s in mweight m.

(* We write [safe s] for the type of an accessibility witness. *)

Definition safe s :=
  Acc olt (weight s).

(* The notations [s' ≤ s] and [s' < s] help reason about the weight
   of a state without visual overhead. *)

Definition slt s' s := olt (weight s') (weight s).
Definition sle s' s := ole (weight s') (weight s).
Declare Scope state_scope.
Infix "≤" := sle (at level 70) : state_scope.
Infix "<" := slt (at level 70) : state_scope.
Open Scope state_scope.

(* [beyond s] is the type of a state [s'] such that [s' ≤ s] holds. *)

Definition beyond s :=
  { s' | s' ≤ s }.

(* [below s] is the type of a state [s'] such that [s' < s] holds. *)

Definition below s :=
  { s' | s' < s }.

(* [pack_beyond s] wraps the state [s] so that it has type [beyond s]. *)

Definition pack_beyond s : beyond s :=
  Specif.exist _ s (ole_refl (weight s)).

(* [pack_below s ow] packages the state [s'] and the witness [ow : s' < s]
   so that they have type [beyond s]. *)

Definition pack_below {s} s' (ow : s' < s) : below s :=
  Specif.exist _ s' ow.

(* [step], an identity function on states, proves that if a state [s0]
   is beyond [s1], and if [s1 < s2] holds, then [s0] is below [s2]. *)

Local Definition step {s1 s2} : s1 < s2 → beyond s1 → below s2.
Proof.
  intros ow12 (s0 & ow01). exists s0.
  unfold sle, slt in *.
  eauto using ole_olt_trans with typeclass_instances.
Defined.

(* [decay], an identity function on states, proves that if a state [s']
   is below [s] then it is also beyond [s]. (Information is lost.) *)

Local Definition decay {s} : below s → beyond s.
Proof.
  intros (s' & ow). exists s'.
  unfold slt, sle in *.
  eauto using olt_ole with typeclass_instances.
Defined.

(* [decrease] constructs a strict ordering witness, expressing the idea
   that if the vertex [v] is unmarked in the state [s], which is the pair
   [(m, u)], then marking [v] produces a new state of smaller weight. *)

Lemma decrease s m v u u' :
  s = (m, u) →
  safe s →
  get m v = false →
  (set m v true, u') < s.
Proof.
  intros ? Hsafe Hget. subst.
  (* The beautiful hack: from [safe (m, u)],
     we deduce [default m = true]. *)
  assert (Hm: default m = true).
  { unfold safe, weight, mweight in *.
    (* By way of contradiction, assume [default m] is [false]. *)
    destruct (default m) eqn:Hm; [ reflexivity | exfalso ].
    (* Then we get that [None] is accessible. Contradiction. *)
    eapply (@Acc_None nat Nat.lt). tauto. }
  (* Because [default m] is [true], and because this remains true
     after [m] is updated, the goal can be simplified and becomes
     a comparison of two natural numbers. *)
  unfold slt, weight, mweight.
  rewrite default_set.
  rewrite Hm.
  simpl.
  (* Furthermore, because [default m] is [true] and [get m v] is [false],
     the vertex [v] must lie within the bounds of the array [m]. *)
  assert ((v <? length m)%uint63 = true).
  { destruct ((v <? length m)%uint63) eqn:Hv; [ reflexivity | exfalso ].
    apply get_out_of_bounds in Hv.
    congruence. }
  (* There remains to work. This is a bit ugly. *)
  set (i := (φ v)%uint63).
  assert (unsigned i). { unfold i. lia. }
  assert (isInt v i).  { eapply introIsInt. reflexivity. }
  assert (Hvalid: valid i (to_list m))
    by eauto using ltb_length_spec with typeclass_instances.
  rewrite !sum_with_spec.
  erewrite set_spec by eauto.
  generalize (sum_list_with_insert unmarked i (to_list m) true Hvalid).
  erewrite <- get_spec by eauto.
  rewrite Hget.
  simpl unmarked.
  lia. (* ouf *)
Qed.

(* -------------------------------------------------------------------------- *)

(* The main recursive function of the depth-first search algorithm: [visit].  *)

Section Visit.

(* [foreach_successor v] must iterate on the successors of the vertex [v]. *)

(* Fortunately, no properties of this function are needed in the proof of
   termination of [visit]. *)

Variable foreach_successor : ∀ {A}, A → vertex → (A → vertex → A) → A.

(* The user function [body v u] is invoked when a vertex [v] is discovered.
   It updates the user state [u]. *)

Variable body : vertex → U → U.

(* [visit] expects a state [s], a vertex [v], and a proof that this state
   is safe. The fact that [s] is safe (accessible) is used to justify
   termination; the function is defined by structural recursion on [ACC]. *)

(* Thanks to the beautiful hack, there is no need to separately keep track
   of an invariant about the state [s]. A state that does not satisfy the
   invariant is deemed inaccessible (unsafe). *)

(* [visit s v ACC] produces a result of type [beyond s], that is, a new
   state [s'] such that [s' ≤ s] holds. This information is required,
   while iterating on the successors of a state, to prove that every call
   to [visit] in this sequence is permitted. *)

(* To iterate on the successors, we use a normal (simply-typed) iteration
   function. This requires us to package [visit] as a function whose
   argument state and result state have the same type, and which does not
   require an accessibility witness as an argument. Fortunately, this is
   possible! *)

Fixpoint visit s v (ACC : safe s) : beyond s :=
  (* Destruct [s] as a pair [(m, u)] while keeping track of the equation. *)
  match s as b return s = b → _ with (m, u) => λ Hsmu,
  (* Test whether the vertex [v] is marked. *)
  let marked := get m v in
  IFC marked THEN λ _,
    (* It is marked: do nothing. *)
    pack_beyond s
  ELSE λ Hunmarked,
    (* Mark this vertex. *)
    let m' := set m v true in
    (* Invoke the user function [body]. *)
    do u' ← body v u ;
    (* Construct an updated state. *)
    let s' := (m', u') in
    (* Construct a witness of the assertion [s' < s]. *)
    let ow : s' < s := decrease s m v u u' Hsmu ACC Hunmarked in
    (* Package them together. *)
    let s' := pack_below s' ow in
    (* Package [visit] as a function of type [below s → vertex → below s],
       which can be passed to [foldl]. Because we have [ACC] at hand, any
       call to [visit] on a state that is smaller than [s] is permitted.
       Therefore we are able to package [visit] as a function that does
       not require an accessibility witness. *)
    (* This construction has just [visit] and [ACC] as free variables. *)
    let visit (sow' : below s) (w : vertex) : below s :=
      let (s', ow) := sow' in
      step ow (visit s' w (Acc_inv ACC ow))
    in
    (* Visit the successors of [v], *)
    (* Visit them, then use [decay] to forget that we went below [s]. *)
    decay (foreach_successor s' v visit)
  end eq_refl.

End Visit.

End S.
