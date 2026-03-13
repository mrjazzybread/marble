From stdpp Require Import list.
From array Require Import tactics wp wp_tactics.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

(* -------------------------------------------------------------------------- *)

(* An exitable loop lets the loop body return an instruction to either
   continue or stop (break). We write [out] for such an instruction:
   its type is [option A]. *)

(* TODO use a dedicated type instead of abusing [option] *)

Global Notation break      := Some.
Global Notation continue   := None.

Global Notation broken out := (out ≠ continue).

(* -------------------------------------------------------------------------- *)

(* Generic specifications for loops. *)

Section Loops.

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

Section ITER.

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
  loop s (λ s, ∃ k, complete k ∧ inv k s).

(* In summary, [ITER body loop step init complete] means that, provided
   the loop body respects the calling convention [body], it is safe to use
   the loop with the calling convention [loop], and it will move from
   producer state [init] to some final producer state [k] along the
   relation [step]. *)

End ITER.

(* -------------------------------------------------------------------------- *)

(* Generic specifications for exitable (interruptible) loops. *)

(* At an abstract level, an exitable loop can be viewed essentially as a
   normal loop where the user state is a pair [(s, out)]. When [out] is
   [break _], the loop stops. In the contrapositive form, if the loop
   body is invoked, then [out] must be [continue]. Thus the loop body
   may assume [out = continue]. Furthermore, once the loop terminates,
   one cannot assume [complete k], as in a normal loop; instead one must
   assume [complete k ∨ broken out]. *)

(* At runtime, an exitable loop can be implemented in several ways. One
   approach is to ask the loop body to return a pair [(s, out)], and to
   then inspect [out] to determine whether to continue or to stop. This
   produces fairly bad code: an option and a pair are allocated at each
   iteration. This code seems fairly difficult to optimize a posteriori:
   this seems to require [match/match] commutations and other magic.
   A better approach is to provide the loop body with two continuations:
   the loop body invokes one or the other to indicate how to proceed.
   (In other words, the loop body returns a Church-encoded option.)
   The fact that the user state involves two components [s] and [out] is
   still visible in the specification, where the loop invariant takes
   the form [inv j s out]. *)

Section XITER.

(* The first component of the user's state has type [S]. *)
Context {S : Type}.
Implicit Types s : S.

(* The second component of the user state has type [option A].
   In other words, [A] is the type of [x] in [break x]. *)
Context {A : Type}.
Implicit Types out : option A.
Implicit Types x : A.

(* The loop body expects two continuations, which we name [normal] and
   [exit] here, although in client code it may be desirable to name
   them [continue] and [break], at the cost of a potential confusion
   with the two constructors of the [option] type. *)
Variable body : ∀ {W}, O → P → S → (S → W) → (S → A → W) → WP W.

(* The loop returns a pair [(s, out)]. *)
Variable loop : S → WP (S * option A).

(* The user's loop invariant takes the form [inv i s out] where [i] is
   the current logical producer state and [(s, out)] is the current user
   state. We use a curried form for increased comfort. *)
Implicit Types inv : P → S → option A → Prop.

(* The specification of an exitable loop takes the following form. *)

Definition XITER :=
  ∀ inv s,
  (* Initially, [out] is continue. *)
  inv init s continue →
  (* When the loop body is invoked,
     it can assume that [out] is [continue]. *)
  ( ∀ j0 o j j1 s ,
    inv j0 s continue →
    step j0 o j j1 →
    ∀ {W} (Q : W → Prop) normal exit,
    (* Invoking [normal s] is like returning [continue]. *)
    (∀ s  , inv j1 s continue  → wp (normal s) Q) →
    (* Invoking [exit s x] is like returning [break x]. *)
    (∀ s x, inv j1 s (break x) → wp (exit s x) Q) →
    body o j s normal exit Q
  ) →
  (* Once the loop ends, we have either [complete k] or [broken out]. *)
  loop s (λ '(s, out), ∃ k, (complete k ∨ broken out) ∧ inv k s out).

(* We propose a variant where the user state [s] has type [unit]. Then
   the loop body, the continuations, and the loop have slightly simpler
   types. The loop invariant is [inv j out] instead of [inv j s out]. *)

Variable ubody : O → P → ∀ {W}, (unit → W) → (A → W) → WP W.

Variable uloop : WP (option A).

Definition UXITER :=
  ∀ (inv : P → option A → Prop) ,
  inv init continue →
  ( ∀ j0 o j j1 ,
    inv j0 continue →
    step j0 o j j1 →
    ∀ {W} (Q : W → Prop) normal exit,
    (     inv j1 continue  → wp (normal()) Q) →
    (∀ x, inv j1 (break x) → wp (exit x  ) Q) →
    ubody o j normal exit Q
  ) →
  uloop (λ out, ∃ k, (complete k ∨ broken out) ∧ inv k out).

End XITER.

(* -------------------------------------------------------------------------- *)

End Loops.

(* The tactic [ITER] should be used when the goal is [ITER ...]. *)

Ltac ITER :=
  intros ? ? Hinit Hstep.

Ltac XITER :=
  intros ? ? Hinit Hbody.

Ltac UXITER :=
  intros ? Hinit Hbody.

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
