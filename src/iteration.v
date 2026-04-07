From stdpp Require Import list.
From listz Require Import listz.
From marble Require Import tactics wp.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

(* -------------------------------------------------------------------------- *)

(* This little type class lets us define an implication [⇝] connective
   whose right-hand side is not necessarily a proposition, but can be
   a function of arbitrarily many arguments to a proposition. *)

Class PropLike (A : Type) :=
  { implication : Prop → A → A }.

Global Instance PropLike_Prop : PropLike Prop :=
  { implication := λ A B, A → B }.

Global Instance PropLike_forall {A} `{∀ a, PropLike (B a)} : PropLike (∀ a : A, B a) :=
  { implication := λ (P : Prop) (f : ∀ a : A, B a) (a : A), implication P (f a) }.

Global Infix "⇝" := implication
  (right associativity, at level 90).

(* Expanding this connective can require using [simpl implication]. *)

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

(* The evolution of the producer's state AND the calling convention of
   the loop body are represented by [body], a [wp]-like judgement. The
   proposition [body j0 j1 s Q] means that, under the assumption that
   the producer can step from state [j0] to state [j1], the loop body,
   with current user state [s], establishes the postcondition [Q]. *)
Variable body : P → P → S → WP S.
  (* If one would like to have separate descriptions of the evolution
     of the producer and of the calling convention of the loop body,
     this is possible, by instantating [body] in a suitable way. See
     our definition of [ITER_NAT] below. *)

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
  loop s (λ s, ∃ k, inv k s ∧ complete k).

(* In summary, [ITER init complete body loop] means that, provided the
   loop body respects the calling convention [body], it is safe to use
   the loop with the calling convention [loop], and it will move from
   producer state [init] to some producer state that satisfies
   [complete]. *)

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
Variable body : P → P → ∀ {W}, S → (S → W) → (S → A → W) → WP W.

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
  loop s (λ '(s, out), ∃ k, inv k s out ∧ (complete k ∨ broken out)).

(* We propose a variant where the user state [s] has type [unit]. Then
   the loop body, the continuations, and the loop have slightly simpler
   types. The loop invariant is [inv j out] instead of [inv j s out]. *)

Variable ubody : P → P → ∀ {W}, (unit → W) → (A → W) → WP W.
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
  uloop (λ out, ∃ k, inv k out ∧ (complete k ∨ broken out)).

End XITER.

End Loops.

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
  (body : A → Z → S → WP S)
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

(* TODO define [XITER_LIST] and [UXITER_LIST] *)

(* -------------------------------------------------------------------------- *)

(* Iteration on a semi-open interval [i, k) of the integers in [nat]. *)

(* To avoid duplication, we parameterize these definitions with
   a direction, which is [Up] or [Down]. *)

Inductive direction := Up | Down.

Section Nat.
Open Scope nat_scope.

(* The producer state [j] is the loop index. *)

(* The function [nat_init i k dir] defines the initial producer state. *)

Definition nat_init i k dir : nat :=
  match dir with Up => i | Down => k end.

(* The predicate [nat_complete i k dir : nat → Prop] defines which producer
   states are final; in other words, it specifies when it is permitted for
   iteration to finish. *)

(* Because iteration is deterministic, there is only one final state. *)

(* When going up, the final state is [i `max` k]. When going down, the
   final state is [i `min` k]. These `max` and `min` operators account
   for the special case where [k < i] and the loop is not executed. *)

(* We make this a notation, as opposed to a definition, because it appears
   in the postcondition of a loop (see [ITER]). This implies that (in the
   case where a rigid postcondition is not known beforehand) it can leak
   (through unification of metavariables) into the precondition of the code
   that follows the loop. *)

Notation nat_complete i k dir  :=
  ( λ j,
    match dir with
    | Up   => j = i `max` k
    | Down => j = i `min` k
    end
  ).

(* The predicate transformer [nat_step i k dir] transforms a judgement
   [body : nat → A] that is indexed by the current state into a judgement
   [nat_step i k dir body : nat → nat → A] that is indexed by two states,
   namely the previous producer state and the new producer state. *)

(* Upon first reading, one can think that the type [A] is [Prop], and
   the squiggly arrow [⇝] is implication [→]. In the general case, the
   type [A] must be PropLike; this allows [nat_step] to work also in the
   case where [body] has extra parameters beyond the current state [j]. *)

(* In either direction, [j0] represents the previous state and [j1]
   represents the new state. When going up, we have [j1 = j0 + 1];
   when going down, we have [j0 = j1 + 1]. *)

(* The argument that is passed to [body] represents the state that the
   consumer observes. When going up, [body] is applied to [j0]. This means
   that the consumer observes the previous state [j0], as opposed to the
   new state [j1]. Thus, the assertion [inv j s] means that the loop has
   run up to index [j] excluded and that the next iteration will concern
   index [j]. When going down, [body] is applied to [j1]. This means that
   the consumer observes the new state [j1], as opposed to the previous
   state [j0]. Thus, the loop invariant [inv j s] means that the loop
   has run down to index [j] included and that the next iteration will
   concern index [j - 1]. *)

(* In either direction, the state [j] that is observed by the consumer
   satisfies [i ≤ j < k]. It lies inside the semi-open interval that is
   being enumerated. *)

(* These are just conventions. They seem natural to me, but they could
   be changed, if desired. *)

Definition nat_step i k dir `{PropLike A}
  (body : nat → A)
: nat → nat → A :=
  λ j0 j1 ,
  match dir with
  | Up =>
      j1 = j0 + 1 ⇝
      i ≤ j0 < k ⇝
      body j0
  | Down =>
      j0 = j1 + 1 ⇝
      i ≤ j1 < k ⇝
      body j1
  end.

Definition ITER_NAT {S}
  i k dir
  (body : nat → S → WP S)
  (loop : S → WP S)
:=
  ITER
    (nat_init i k dir)
    (nat_complete i k dir)
    (nat_step i k dir body)
    loop.

Definition XITER_NAT {S A}
  i k dir
  (body : nat → ∀ {W}, S → (S → W) → (S → A → W) → WP W)
  (loop : S → WP (S * outcome A))
:=
  XITER
    (nat_init i k dir)
    (nat_complete i k dir)
    (nat_step i k dir body)
    loop.

Definition UXITER_NAT {A}
  i k dir
  (body : nat → ∀ {W}, (unit → W) → (A → W) → WP W)
  (loop : WP (outcome A))
:=
  UXITER
    (nat_init i k dir)
    (nat_complete i k dir)
    (nat_step i k dir body)
    loop.

End Nat.

(* -------------------------------------------------------------------------- *)

(* Iteration on a semi-open interval [i, k) of the integers in [Z]. *)

(* The producer state [j] is the loop index. *)

(* The function [z_init i k dir] defines the initial producer state. *)

Definition z_init i k dir : Z :=
  match dir with Up => i | Down => k end.

(* The predicate [z_complete i k dir : z → Prop] defines which producer
   states are final; in other words, it specifies when it is permitted for
   iteration to finish. *)

Notation z_complete i k dir  :=
  ( λ j,
    match dir with
    | Up   => j = i `max` k
    | Down => j = i `min` k
    end
  ).

(* The predicate transformer [z_step i k dir] transforms a judgement
   [body : Z → A] that is indexed by the current state into a judgement
   [nat_step i k dir body : Z → Z → A] that is indexed by two states,
   namely the previous producer state and the new producer state. *)

Definition z_step i k dir `{PropLike A}
  (body : Z → A)
: Z → Z → A :=
  λ j0 j1 ,
  match dir with
  | Up =>
      j1 = j0 + 1 ⇝
      i ≤ j0 < k ⇝
      body j0
  | Down =>
      j0 = j1 + 1 ⇝
      i ≤ j1 < k ⇝
      body j1
  end.

Definition ITER_Z {S}
  i k dir
  (body : Z → S → WP S)
  (loop : S → WP S)
:=
  ITER
    (z_init i k dir)
    (z_complete i k dir)
    (z_step i k dir body)
    loop.

Definition XITER_Z {S A}
  i k dir
  (body : Z → ∀ {W}, S → (S → W) → (S → A → W) → WP W)
  (loop : S → WP (S * outcome A))
:=
  XITER
    (z_init i k dir)
    (z_complete i k dir)
    (z_step i k dir body)
    loop.

Definition UXITER_Z {A}
  i k dir
  (body : Z → ∀ {W}, (unit → W) → (A → W) → WP W)
  (loop : WP (outcome A))
:=
  UXITER
    (z_init i k dir)
    (z_complete i k dir)
    (z_step i k dir body)
    loop.

(* -------------------------------------------------------------------------- *)

(* Tactics. *)

(* [expand_ITER] expands all of the definitions made above, so that they
   do not get in the way. It is automatically invoked by [ITER], below. In
   a proof by induction, it is necessary to explicitly use [expand_ITER]
   before beginning the induction, so that the definitions are expanded
   not only in the goal but also in the induction hypothesis. *)

Ltac expand_ITER :=
  unfold
    ITER_NAT, XITER_NAT, UXITER_NAT, nat_init, nat_step,
    ITER_Z, XITER_Z, UXITER_Z, z_init, z_step,
    ITER_LIST, ITERI_LIST,
    ITER, XITER, UXITER;
    simpl implication.

(* Updating this hook (which is defined in wp.v) lets us to call [expand_ITER]
   in every precondition of a loop, before [wp_precondition_hook] is called. *)

Global Ltac wp_loop_precondition_hook ::=
  expand_ITER.

(* The tactic [ITER] should be used when the goal is [ITER ...]. *)

Ltac ITER :=
  expand_ITER;
  intros ? ? Hinit Hstep.

Ltac XITER :=
  expand_ITER;
  intros ? ? Hinit Hbody.

Ltac UXITER :=
  expand_ITER;
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

(* TODO clean up *)

Ltac wp_loop_intros j0 j1 s :=
  let h := fresh "Hinv" in
  intros j0 j1 s h;
  unpack in h.

(* TODO improve / comment *)

Ltac wp_up_intros j s :=
  let j1 := fresh "j1" in
  wp_loop_intros j j1 s;
  intros -> ?.

(* TODO improve / comment *)

Ltac wp_down_intros j s :=
  let j0 := fresh "j0" in
  wp_loop_intros j0 j s;
  intros -> ?.
