From stdpp Require Import list.
From array Require Import tactics wp wp_tactics.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

(* Notation for interruptible loops. *)

Global Notation break    := Some.
Global Notation continue := None.

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

(* [init] is the initial producer state. *)
Variable init : P.

(* The predicate [complete] identifies the final producer states,
   that is, the producer states where the producer may stop. *)
Variable complete : P → Prop.

Section UserState.

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

(* Then, the specification of a loop takes the following form. *)

Definition ITER :=
  ∀ inv s ,
  (* Initially, the producer state is [init] and the user state is [s].
     The invariant must hold. *)
  inv init s →
  (* If the producer can step from [j0] to [j1] while revealing the
     observation [o] and current state [j], then the loop body,
     applied to [o] and [j], must transform [inv j0 s] into
     [inv j1 s']. *)
  (∀ j0 o j j1 s ,
    inv j0 s →
    step j0 o j j1 →
    body o j s (λ s', inv j1 s')
  ) →
  (* Once the loop ends, the producer state is a certain state [k] such
     that [complete k] holds and the user state is some state [s]. Then,
     the invariant is guaranteed to hold. *)
  ∀ Q ,
  (∀ k s, complete k → inv k s → Q s) →
  loop s Q.

(* In summary, [ITER body loop step init complete] means that, provided
   the loop body respects the calling convention [body], it is safe to use
   the loop with the calling convention [loop], and it will move from
   producer state [init] to some final producer state [k] along the
   relation [step]. *)

End UserState.

(* -------------------------------------------------------------------------- *)

(* A generic specification for an interruptible loop. *)

(* An interruptible loop lets the loop body return an instruction
   to either continue or stop (break). We write [out] for such an
   instruction, because it is an option, and it is the outcome of
   the loop body. *)

(* An interruptible loop is in fact a normal loop where the user state
   is a pair [(s, out)]. When [out] is [break _], the loop stops. In
   the contrapositive form, if the loop body is invoked, then [out]
   must be [continue]. Thus the loop body may assume [out = continue]. *)

(* We could adopt an even more abstract point of view, where the user
   state is not necessarily a pair, and a predicate of type [S → Prop]
   determines whether the user state allows or forbids continuing. But
   adopting a more specific convention is more comfortable. *)

Section UserState.

(* The first component of the user's state has type [S]. *)
Context {S : Type}.
Implicit Types s : S.

(* The second component of the user state has type [option A].
   In other words, [A] is the type of [x] in [break x]. *)
Context {A : Type}.
Implicit Types out : option A.
Implicit Types x : A.

(* The complete user state has type [S * option A]. *)
Local Notation U := (S * option A)%type.

(* In the type of the loop body, we use [S → WP U] instead of [U → WP U]
   because when the loop body is invoked, the the second component of
   the user state is known; it must be [continue]. *)
Variable body : O → P → S → WP U.

(* Same convention here *)
Variable loop : S → WP U.

(* The user's loop invariant takes the form [inv i (s, out)] where [i] is
   the current logical producer state and [(s, out)] is the current user
   state. *)

Definition ITERX :=
  ITER
    (λ o i '(s, out) Q, out = continue → body o i s Q)
    (λ '(s, out) Q, loop s Q).

End UserState.

(* -------------------------------------------------------------------------- *)

End Iter.

Ltac ITER :=
  unfold ITER; (* optional *)
  intros ? ? Hinit Hstep ? Hfinish.

(* -------------------------------------------------------------------------- *)

(* A specification of a loop over a list. *)

(* [ITER_LIST_TAIL] is an instance of [ITER] where the [step] relation is
   fixed and the remaining parameters remain unspecified. *)

(* By convention, the producer state is the history, that is, the list of
   elements produced so far. The [step] relation extends the history with
   one element [x]. By convention, the loop invariant is parameterized
   with [history0], that is, the history before it is extended with [x]. *)

(* [ITER_LIST_TAIL body loop init xs] means that, provided the loop body
   respects the calling convention [body], it is safe to use the loop with
   the calling convention [loop], and it will move from producer state
   [init] to producer state [xs] along the relation [step]. In practice,
   the list [init] should be a suffix of the list [xs]; it is the list
   of elements that remain to be enumerated. *)

Definition ITER_LIST_TAIL {S A}
  (init xs : list A)
  (body : A → list A → S → WP S)
  (loop : S → WP S)
:=
  let step history0 x history history1 :=
    history = history0 ∧
    history0 ++ {[x]} = history1 ∧
    history1 `prefix_of` xs
  in
  let complete history :=
    history = xs
  in
  ITER step  init complete body loop.

(* [ITER_LIST] is an instance of [ITER_LIST_TAIL] where the starting state
   [init] is fixed: it is the empty list. *)

(* [ITER_LIST body loop xs] means that, provided the loop body respects the
   calling convention [body], it is safe to use the loop with the calling
   convention [loop], and it will move from producer state <empty list> to
   producer state [xs] along the relation [step]. *)

Definition ITER_LIST {S A}
  (xs : list A)
  (body : A → list A → S → WP S)
  (loop : S → WP S)
:=
  ITER_LIST_TAIL [] xs body loop.
