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

From Stdlib Require Import Program.Equality. (* [dependent induction] *)
From stdpp Require Import numbers list.
From listz Require Import listz.
Notation len := length.
From Stdlib Require Import Uint63.
From Stdlib Require Import Array.PArray.
From marble Require Import tactics bool int iteration loop wp array.
Implicit Type _i _j _k _n : int.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

(* This file defines depth-first search algorithms. *)

(* -------------------------------------------------------------------------- *)

(* TODO list of successors, cascade of successors, or foreach function? *)
(* TODO recursive DFS or CPS-style DFS or loop with explicit stack? *)

(* TODO need generic [reduce] function on arrays, with monoid *)

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

Local Definition sum {A} (f : A → nat) (a : array A) : nat :=
  array.iteri a 0%nat (λ _i x s, f x + s)%nat.

(* The natural numbers augmented with infinity, equipped with the strict
   ordering [<], and extended with a self-loop at [infinity], form a
   structure where every element except [infinity] is accessible. *)

(* We use this structure to keep track of an invariant. If the array
   [m] does NOT satisfy the invariant then its weight is [infinity]. In
   other words, if [m] is accessible then [m] satisfies the invariant.
   This hack removes the need to separately carry an invariant. *)

Module Nat'.

Inductive nat' :=
| N : nat → nat'
| infinity : nat'.

Definition lt (n1 n2 : nat') :=
  match n1, n2 with
  | _, infinity =>
      True (* loop! *)
  | infinity, N _ =>
      False
  | N n1, N n2 =>
      (n1 < n2)%nat
  end.

Definition le (n1 n2 : nat') :=
  match n1, n2 with
  | _, infinity =>
      True
  | infinity, _ =>
      False
  | N n1, N n2 =>
      (n1 ≤ n2)%nat
  end.

Lemma le_refl n : le n n.
Proof. destruct n; simpl; eauto. Qed.

Lemma le_trans n0 n1 n2 : le n0 n1 → le n1 n2 → le n0 n2.
Proof.
  destruct n0 as [n0|]; destruct n1 as [n1|]; destruct n2 as [n2|];
  simpl; eauto with lia.
Qed.

Lemma le_lt_trans n0 n1 n2 : le n0 n1 → lt n1 n2 → lt n0 n2.
Proof.
  destruct n0 as [n0|]; destruct n1 as [n1|]; destruct n2 as [n2|];
  simpl; eauto with lia.
Qed.

Lemma lt_le_trans n0 n1 n2 : lt n0 n1 → le n1 n2 → lt n0 n2.
Proof.
  destruct n0 as [n0|]; destruct n1 as [n1|]; destruct n2 as [n2|];
  simpl; eauto with lia.
Qed.

Lemma lt_le n0 n1 : lt n0 n1 → le n0 n1.
Proof.
  destruct n0 as [n0|]; destruct n1 as [n1|]; simpl; eauto with lia.
Qed.

(* Every finite number is accessible. *)

Local Lemma Acc_N_aux n : ∀ n', (n' < n)%nat → Acc lt (N n').
Proof.
  induction n as [|n]; intros.
  { lia. }
  { constructor. intros n'' Hlt.
    destruct n''; simpl in Hlt.
    + eauto with lia.
    + tauto. }
Qed.

Lemma Acc_N n : Acc lt (N n).
Proof. apply Acc_N_aux with (n := S n). lia. Qed.

(* Infinity is not accessible. *)

Lemma Acc_infinity : ¬ Acc lt infinity.
Proof.
  unfold not. intros H. dependent induction H.
  clear H. rename H0 into IH.
  eapply IH; [| reflexivity ].
  (* [lt infinity infinity] is true. *)
  reflexivity.
Qed.

End Nat'.

(* The invariant that we record is [default m = true]. That is, outside
   of the bounds of the marks array, every vertex is considered marked.
   Therefore, if an out-of-bounds vertex is encountered (which could
   happen, as we do not impose any condition on the vertices that we
   receive as parameters!) then the algorithm ignores it. *)

(* This trick can be considered a dirty hack, but it is convenient and
   helps us in the termination proof. Of course, a posteriori, we can
   use [wp]-style specifications to ensure that every vertex is within
   the desired bounds. *)

Definition mweight m : Nat'.nat' :=
  if default m then
    Nat'.N (sum unmarked m)
  else
    Nat'.infinity.

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
  Acc Nat'.lt (weight s).

(* The notations [s' ≤ s] and [s' < s] help reason about the weight
   of a state without visual overhead. *)

Definition le s' s := Nat'.le (weight s') (weight s).
Definition lt s' s := Nat'.lt (weight s') (weight s).
Declare Scope state_scope.
Infix "≤" := le (at level 70) : state_scope.
Infix "<" := lt (at level 70) : state_scope.
Open Scope state_scope.

(* [beyond s] is the type of a state [s'] such that [s' ≤ s] holds. *)

Definition beyond s :=
  { s' | s' ≤ s }.

(* [below s] is the type of a state [s'] such that [s' < s] holds. *)

Definition below s :=
  { s' | s' < s }.

(* [return_ s] wraps the state [s] so that it has type [beyond s]. *)

Definition return_ s : beyond s :=
  Specif.exist _ s (Nat'.le_refl (weight s)).

(* [step], an identity function on states, proves that if a state [s0]
   is beyond [s1], and if [s1 < s2] holds, then [s0] is below [s2]. *)

Local Definition step {s1 s2} : s1 < s2 → beyond s1 → below s2.
Proof.
  intros ow12 (s0 & ow01). exists s0.
  unfold le, lt in *. eauto using Nat'.le_lt_trans.
Defined.

(* [decay], an identity function on states, proves that if a state [s']
   is below [s] then it is also beyond [s]. (Information is lost.) *)

Local Definition decay {s} : below s → beyond s.
Proof.
  intros (s' & ow). exists s'.
  unfold lt, le in *. eauto using Nat'.lt_le.
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
  intros. subst.
  (* The beautiful hack: from [safe (m, u)],
     we deduce [default m = true]. *)
  assert (Hm: default m = true).
  { unfold safe, weight, mweight in *.
    (* By way of contradiction, assume [default m] is [false]. *)
    destruct (default m) eqn:Hm; [ reflexivity | exfalso ].
    (* Then we get that [infinity] is accessible. Contradiction. *)
    generalize Nat'.Acc_infinity. tauto. }
  (* Because [default m] is [true], and because this remains true
     after [m] is updated, the goal can be simplified. *)
  unfold lt, weight, mweight.
  rewrite default_set.
  rewrite Hm.
  simpl.
  (* Furthermore, because [default m] is [true] and [get m v] is [false],
     the vertex [v] must lie within the bounds of the array [m]. *)
  assert ((v <? length m)%uint63 = true).
  { destruct ((v <? length m)%uint63) eqn:Hv; [ reflexivity | exfalso ].
    apply get_out_of_bounds in Hv.
    congruence. }
Admitted. (* TODO *)

(* -------------------------------------------------------------------------- *)

(* The main recursive function of the depth-first search algorithm: [visit].  *)

Section Visit.

(* The user function [body v u] is invoked when a vertex [v] is discovered.
   It updates the user state [u]. *)

Variable body : vertex → U → U.

(* [successors v] must be a list of the successors of the vertex [v]. *)

(* Fortunately, no properties of this function are needed in the proof
   of termination of [visit]. *)

(* TODO can now use [foreach_successors] *)

Variable successors : vertex → list vertex.

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
   function. This requires us to package [visit] as a function that does
   whose argument state and result state have the same type, and which
   does not require an accessibility witness as an argument. Fortunately,
   this is possible! *)

Fixpoint visit s v (ACC : safe s) : beyond s :=
  (* Destruct [s] as a pair [(m, u)] while keeping track of the equation. *)
  match s as b return s = b → _ with (m, u) => λ Hsmu,
  (* Test whether the vertex [v] is marked. *)
  let marked := get m v in
  IFC marked THEN λ _,
    (* It is marked: do nothing. *)
    return_ s
  ELSE λ Hunmarked,
    (* Mark this vertex. *)
    let m' := set m v true in
    (* Invoke the user function [body]. *)
    do u' ← body v u ;
    (* Construct an updated state. *)
    let s' := (m', u') in
    (* Construct a witness of the assertion [s' < s]. *)
    let ow : s' < s := decrease s m v u u' Hsmu ACC Hunmarked in
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
    (* Get ahold of the successors of [v]. *)
    do ws ← successors v ;
    (* Visit them, then use [decay] to forget that we went below [s]. *)
    decay (fold_left visit ws (Specif.exist _ s' ow))
  end eq_refl.

End Visit.

End S.
