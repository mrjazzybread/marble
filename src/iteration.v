From stdpp Require Import list.
From array Require Import tactics wp wp_tactics.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

(* -------------------------------------------------------------------------- *)

(* A generic specification for a loop. *)

Section Iter.

(* We distinguish the producer state and the user state.

   For example, the state of the producer could be an integer index, a list
   of elements that have been enumerated, or a list of elements that remain
   to be enumerated.

   The type of the user state is whatever the user chooses. The user state
   is also known as the accumulator, or the loop-carried state. *)

(* [P] is the type of the producer state. *)
Context {P : Type}.
Implicit Types i j k : P.

(* [O] is the type of the observations delivered by the producer to the
   user. For example, in a loop over machine integers, this type could be
   [int]. In a loop over a collection, it could be the type of elements. *)
Context {O : Type}.
Implicit Type o : O.

(* The relation [step] describes the evolution of the producer's state and
   the manner in which this evolution is observed by the user. The
   proposition [step j0 o j j1] means that, in one loop iteration, the
   producer's state can evolve from [j0] to [j1], while the user (that is,
   the loop body) observes the observation [o] and producer state [j].

   The current producer state [j] is typically either [j0] or [j1].
   Parameterizing [step] and [body] (below) with [o] and [j] rather than
   just [o] seems convenient. *)
Variable step : P → O → P → P → Prop.

(* [S] is the type of the user's state. *)
Context {S : Type}.
Implicit Types s : S.

(* The behavior of the loop body is represented by [body], a [wp]-like
   judgement. The proposition [body o j s Q] means that the loop body, with
   observation [o], current producer state [j], and current user state [s],
   establishes the postcondition [Q]. *)
Variable body : O → P → S → WP S.

(* The behavior of the whole loop is represented by [loop], a [wp]-like
   judgement. The proposition [loop s Q] means that the loop, applied to the
   initial state [s], establishes the postcondition [Q]. *)
Variable loop : S → WP S.

(* The user's loop invariant takes the form [inv i s], where [i] is the
   current logical producer state and [s] is the current user state. *)

Implicit Types inv : P → S → Prop.

(* [i] and [k] are the initial and final producer states. *)

(* Then, the specification of a loop takes the following form. *)

Definition ITER i k :=
  ∀ inv s ,
  (* Initially, the producer state is [i] and the user state is [s].
     The invariant must hold. *)
  inv i s →
  (* If the producer can step from [j0] to [j1] while revealing the
     observation [o] and current state [j], then the loop body,
     applied to [o] and [j], must transform [inv j0 s] into
     [inv j1 s']. *)
  (∀ j0 o j j1 s ,
    inv j0 s →
    step j0 o j j1 →
    body o j s (λ s', inv j1 s')
  ) →
  (* Once the loop ends, the producer state is [k] and the user state is
     some state [s]. Then, the invariant is guaranteed to hold. *)
  ∀ Q ,
  (∀ s, inv k s → Q s) →
  loop s Q.

(* In summary, [ITER body loop step i k] means that, provided the loop body
   respects the calling convention [body], it is safe to use the loop with
   the calling convention [loop], and it will move from producer state [i]
   to producer state [k] along the relation [step]. *)

End Iter.

Ltac ITER :=
  unfold ITER; (* optional *)
  intros ? ? Hinit Hstep ? Hfinish.

(* -------------------------------------------------------------------------- *)

(* A specification of a loop over a list. *)

(* [ITER_LIST_TAIL] is an instance of [ITER] where the [step] relation is
   fixed and the remaining four parameters remain unspecified. *)

(* By convention, the producer state is the history, that is, the list of
   elements produced so far. The [step] relation extends the history with
   one element [x]. By convention, the loop invariant is parameterized
   with [history0], that is, the history before it is extended with [x]. *)

(* [ITER_LIST_TAIL body loop future xs] means that, provided the loop body
   respects the calling convention [body], it is safe to use the loop with
   the calling convention [loop], and it will move from producer state
   [future] to producer state [xs] along the relation [step]. In practice,
   the list [future] should be a suffix of the list [xs]; it is the list
   of elements that remain to be enumerated. *)

Definition ITER_LIST_TAIL {S A}
  (body : A → list A → S → WP S)
  (loop : S → WP S)
  (future xs : list A)
:=
  let step history0 x history history1 :=
    history = history0 ∧
    history0 ++ {[x]} = history1 ∧
    history1 `prefix_of` xs
  in
  ITER step body loop future xs.

(* [ITER_LIST] is an instance of [ITER_LIST_TAIL] where the starting state
   [future] is fixed: it is the empty list. *)

(* [ITER_LIST body loop xs] means that, provided the loop body respects the
   calling convention [body], it is safe to use the loop with the calling
   convention [loop], and it will move from producer state <empty list> to
   producer state [xs] along the relation [step]. *)

Definition ITER_LIST {S A}
  (body : A → list A → S → WP S)
  (loop : S → WP S)
  (xs : list A)
:=
  ITER_LIST_TAIL body loop [] xs.
