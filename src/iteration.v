From stdpp Require Import base.
From array Require Import tactics wp wp_tactics.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

(* -------------------------------------------------------------------------- *)

(* A generic specification for a loop. *)

Section Iter.

(* We distinguish the state of the producer and the state of the user.

   For example, the state of the producer could be an integer index,
   a list of elements that have been enumerated, or a list of
   elements that remain to be enumerated.

   The type of the user state is whatever the user chooses.
   The user state is also known as the accumulator,
   or the loop-carried state. *)

(* [I] and [N] are the physical and logical types of the producer's
   state. In a loop over machine integers, the producer's state is
   the loop index, so these types are [int] and [nat]. *)
Context {I N : Type}.

(* [S] is the type of the user's state. *)
Context {S : Type}.

(* The relation [step] describes the evolution of the producer's state
   and the manner in which this evolution is observed by the user.
   The proposition [step j0 _j j j1] means that, in one loop iteration,
   the producer's state can evolve from [j0] to [j1], while the user
   (that is, the loop body) observes the current physical index [_j]
   and logical index [j]. *)
Variable step : N → I → N → N → Prop.

(* The body of the loop is abstracted as a [wp] judgement. The proposition
   [body _j j s Q] means that the loop body, with current physical index
   [_j], current logical index [j], and current state [s], establishes the
   postcondition [Q]. *)
Variable body : I → N → S → (S → Prop) → Prop.

(* In [step] and [body], one could package up [_j] and [j] as a pair of type
   [I * N] and, abstract this type as a type [O] of user observations. That
   would be perhaps more pleasing in principle; in practice, the curried
   form seems more convenient. *)

(* The loop is abstracted as a [wp] judgement. The proposition [loop s Q]
   means that the loop, applied to the initial state [s], establishes the
   postcondition [Q]. *)
Variable loop : S → (S → Prop) → Prop.

(* The user's loop invariant takes the form [inv i s], where [i] is the
   current logical producer state and [s] is the current user state. *)

(* In the specification [ITER i k],
   [i] and [k] are the initial and final producer states. *)

Definition ITER i k :=
  ∀ (inv : N → S → Prop) (s : S),
  (* The invariant must hold of the initial producer state [i] and
     initial user state [s]. *)
  inv i s →
  (* If the producer can step from [j0] to [j1] while producing the
     observable data [_j] and [j], then the loop body, applied to
     [_j] and [j], must transform [inv j0 s] into [inv j1 s']. *)
  (∀ j0 _j j j1 s ,
    step j0 _j j j1 →
    inv j0 s →
    body _j j s (λ s', inv j1 s')
  ) →
  (* Once the loop ends, the invariant holds of the final producer state [k]
     and of the final user state [s]. *)
  ∀ Q,
  (∀ s, inv k s → Q s) →
  loop s Q.

End Iter.
