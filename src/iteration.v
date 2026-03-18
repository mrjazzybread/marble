From stdpp Require Import list.
From marble Require Import tactics wp wp_tactics.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

(* -------------------------------------------------------------------------- *)

(* An exitable loop lets the loop body return an instruction to either
   continue or stop (break). We write [out] for such an instruction. *)

(* This type is isomorphic to [option A]. We prefer to use a distinct
   type so as to avoid confusion. *)

Inductive outcome (A : Type) : Type :=
| Break : A → outcome A
| Continue : outcome A.

Arguments Break {A} x.
Arguments Continue {A}.

(* [broken out] means that [out] is [Break _]. *)

Global Notation broken out := (out ≠ Continue).

(* These conversion functions can be useful. *)

Definition did_break {A} (out : outcome A) :=
  match out with
  | Continue => false
  | Break _  => true
  end.

Definition did_not_break {A} (out : outcome A) :=
  match out with
  | Continue => true
  | Break _  => false
  end.

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
   judgement. The proposition [body j0 j1 s Q] means that the loop body,
   in a step of producer state [j0] to producer state [j1], with current
   user state [s], establishes the postcondition [Q]. *)
(* TODO note that [body] describes at the same time the evolution of the producer and the calling convention of the loop body. *)
Variable body : P → P → S → WP S.

(* The behavior of the whole loop is represented by [loop], a [wp]-like
   judgement. The proposition [loop s Q] means that the loop, applied to
   the initial state [s], establishes the postcondition [Q]. *)
Variable loop : S → WP S.

(* The user's loop invariant takes the form [inv j s], where [j] is the
   current producer state and [s] is the current user state. *)
Implicit Types inv : P → S → Prop.

(* Then, the specification of a loop takes the following form. *)

Definition ITER :=
  ∀ inv s ,
  (* Initially, the producer state is [init] and the user state is [s].
     The invariant must hold. *)
  inv init s →
  (* If the producer can step from [j0] to [j1], then the loop body
     must transform [inv j0 s] into [inv j1 s']. *)
  (∀ j0 j1 s ,
    inv j0 s →
    body j0 j1 s (λ s', inv j1 s')
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
   [Break _], the loop stops. In the contrapositive form, if the loop
   body is invoked, then [out] must be [Continue]. Thus the loop body
   may assume [out = Continue]. Furthermore, once the loop terminates,
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
   (In other words, the loop body returns a Church-encoded outcome.)
   The fact that the user state involves two components [s] and [out] is
   still visible in the specification, where the loop invariant takes
   the form [inv j s out]. *)

Section XITER.

(* The first component of the user's state has type [S]. *)
Context {S : Type}.
Implicit Types s : S.

(* The second component of the user state has type [outcome A].
   In other words, [A] is the type of [x] in [break x]. *)
Context {A : Type}.
Implicit Types out : outcome A.
Implicit Types x : A.

(* The loop body expects two continuations [continue] and [break]. *)
Variable body : ∀ {W}, P → P → S → (S → W) → (S → A → W) → WP W.

(* The loop returns a pair [(s, out)]. *)
Variable loop : S → WP (S * outcome A).

(* The user's loop invariant takes the form [inv j s out] where [j] is
   the current producer state and [(s, out)] is the current user state.
   We use a curried form for increased comfort. *)
Implicit Types inv : P → S → outcome A → Prop.

(* The specification of an exitable loop takes the following form. *)

Definition XITER :=
  ∀ inv s,
  (* Initially, [out] is [Continue]. *)
  inv init s Continue →
  (* When the loop body is invoked,
     it can assume that [out] is [Continue]. *)
  ( ∀ j0 j1 s ,
    inv j0 s Continue →
    ∀ {W} (Q : W → Prop) (continue : S → W) (break : S → A → W),
    (* Invoking [continue s] is like returning [(s, Continue)]. *)
    (∀ s  , inv j1 s Continue  → wp (continue s) Q) →
    (* Invoking [break s x] is like returning [(s, Break x)]. *)
    (∀ s x, inv j1 s (Break x) → wp (break s x) Q) →
    body j0 j1 s continue break Q
  ) →
  (* Once the loop ends, we have either [complete k] or [broken out]. *)
  loop s (λ '(s, out), ∃ k, (complete k ∨ broken out) ∧ inv k s out).

(* We propose a variant where the user state [s] has type [unit]. Then
   the loop body, the continuations, and the loop have slightly simpler
   types. The loop invariant is [inv j out] instead of [inv j s out]. *)

Variable ubody : ∀ {W}, P → P → (unit → W) → (A → W) → WP W.
Variable uloop : WP (outcome A).

Definition UXITER :=
  ∀ (inv : P → outcome A → Prop) ,
  inv init Continue →
  ( ∀ j0 j1 ,
    inv j0 Continue →
    ∀ {W} (Q : W → Prop) continue break,
    (     inv j1 Continue  → wp (continue()) Q) →
    (∀ x, inv j1 (Break x) → wp (break x   ) Q) →
    ubody j0 j1 continue break Q
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

(* The following tactics help reason about invocations of [continue]
   and [break]. *)

Ltac wp_continue :=
  match goal with
  Hcontinue: ∀ s, _ → wp (?continue s) _,
  Hbreak: ∀ s x, _ → wp (?break s x) _
  |- wp (?continue _) _ =>
    simple eapply Hcontinue; clear Hcontinue Hbreak
  end.
Ltac wp_break :=
  match goal with
  Hcontinue: ∀ s, _ → wp (?continue s) _,
  Hbreak: ∀ s x, _ → wp (?break s x) _
  |- wp (?break _ _) _ =>
    simple eapply Hbreak; clear Hcontinue Hbreak
  end.

(* -------------------------------------------------------------------------- *)

(* Iteration on a list. *)

(* The producer state is the history, that is, the list of elements
   produced so far. Each step extends the history with one element [x].
   The list [init] is the initial producer state; the list [xs] is the
   final producer state. *)

(* We first define a variant where the loop body is parameterized with
   the current element [x] and its index [i] in the history. *)

(* Then, as a degenerate case, we obtain a variant where the loop body
   is parameterized with just [x]. *)

(* One could also define a more general variant where the loop body is
   parameterized with the full history. *)

Definition ITERI_LIST {S A}
  (init xs : list A)
  (body : A → nat → S → WP S)
  (loop : S → WP S)
:=
  ITER
    init
    ( λ history, history = xs )
    ( λ history0 history1 s Q,
      ∀ x i,
      init `prefix_of` history0 →
      history0 ++ {[x]} = history1 →
      history1 `prefix_of` xs →
      i = length history0 →
      body x i s Q
    )
    loop.

Definition ITER_LIST {S A}
  (init xs : list A)
  (body : A → S → WP S)
  (loop : S → WP S)
:=
  ITERI_LIST
    init xs
    ( λ x i s Q, body x s Q )
    loop.

(* TODO could we define [XITER_LIST] and [UXITER_LIST] without duplication?   *)

(* -------------------------------------------------------------------------- *)

(* Iteration on a semi-open interval [i, k), in [nat], going up. *)

(* The producer state [j] is the loop index. *)

(* The fact that [body] is applied to [j0] means that the consumer
   observes the previous state [j0], as opposed to the new state [j1].
   Thus, the assertion [inv j s] means that the loop has run up to
   index [j] excluded and the next iteration will concern [j]. *)

(* Once the loop ends, the producer state is [i `max` k]. This accounts
   for the special case where [k < i] and the loop is not executed. *)

Definition ITER_NAT_UP {S}
  (i k : nat)
  (body : nat → S → WP S)
  (loop : S → WP S)
:=
  ITER
    i
    ( λ j, j = i `max` k )
    ( λ j0 j1 s Q,
      j1 = j0 + 1 →
      i ≤ j0 < k →
      body j0 s Q
    )
    loop.

(* TODO how can I reduce this redundancy? *)

Definition XITER_NAT_UP {S A}
  (i k : nat)
  (body : ∀ {W}, nat → S → (S → W) → (S → A → W) → WP W)
  (loop : S → WP (S * outcome A))
:=
  XITER
    i
    ( λ j, j = i `max` k )
    ( λ _ j0 j1 s continue break Q,
      j1 = j0 + 1 →
      i ≤ j0 < k →
      body j0 s continue break Q
    )
    loop.

Definition UXITER_NAT_UP {A}
  (i k : nat)
  (body : ∀ {W}, nat → (unit → W) → (A → W) → WP W)
  (loop : WP (outcome A))
:=
  UXITER
    i
    ( λ j, j = i `max` k )
    ( λ _ j0 j1 continue break Q,
      j1 = j0 + 1 →
      i ≤ j0 < k →
      body j0 continue break Q
    )
    loop.

(* -------------------------------------------------------------------------- *)

(* Iteration on a semi-open interval [i, k), in [nat], going down. *)

(* The producer state [j] is the loop index. *)

(* The fact that [body] is applied to [j1] means that the consumer
   observes the new state [j1], as opposed to the previous state [j0].
   Thus, the loop invariant [inv j s] means that the loop has run down
   to index [j] included and that the next iteration will concern the
   index [j - 1]. *)

(* Once the loop ends, the producer state is [i `min` k]. This accounts
   for the special case where [k < i] and the loop is not executed. *)

Definition ITER_NAT_DOWN {S}
  (i k : nat)
  (body : nat → S → WP S)
  (loop : S → WP S)
:=
  ITER
    k
    ( λ j, j = i `min` k )
    ( λ j0 j1 s Q,
      j0 = j1 + 1 →
      i ≤ j1 < k →
      body j1 s Q
    )
    loop.

(* TODO how can I reduce this redundancy? *)

Definition XITER_NAT_DOWN {S A}
  (i k : nat)
  (body : ∀ {W}, nat → S → (S → W) → (S → A → W) → WP W)
  (loop : S → WP (S * outcome A))
:=
  XITER
    k
    ( λ j, j = i `min` k )
    ( λ _ j0 j1 s continue break Q,
      j0 = j1 + 1 →
      i ≤ j1 < k →
      body j1 s continue break Q
    )
    loop.

Definition UXITER_NAT_DOWN {A}
  (i k : nat)
  (body : ∀ {W}, nat → (unit → W) → (A → W) → WP W)
  (loop : WP (outcome A))
:=
  UXITER
    k
    ( λ j, j = i `min` k )
    ( λ _ j0 j1 continue break Q,
      j0 = j1 + 1 →
      i ≤ j1 < k →
      body j1 continue break Q
    )
    loop.
