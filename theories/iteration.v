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

From stdpp Require Import list sets fin_sets.
From listz Require Import listz.
From marble Require Import stdpp_buffer. (* TODO *)
From marble Require Import tactics wp.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

Local Infix "≃" := (Permutation)
  (at level 70, no associativity).

(* -------------------------------------------------------------------------- *)

(* This little type class lets us define an implication [⇝] connective
   whose right-hand side is not necessarily a proposition, but can be
   a function of arbitrarily many arguments to a proposition. *)

Class PropLike (A : Type) :=
  { implication : Prop → A → A }.

Global Instance PropLike_Prop : PropLike Prop :=
  { implication := λ A B, A → B }.

Global Instance PropLike_forall {A} {B : A → Type} `{∀ a, PropLike (B a)}
  : PropLike (∀ a : A, B a) :=
  { implication :=
      λ (P : Prop) (f : ∀ a : A, B a) (a : A), implication P (f a) }.

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

(* We distinguish the producer state and the user (consumer) state.

   For example, the state of the producer could be an integer index, a list
   of elements that have been enumerated, or a list of elements that remain
   to be enumerated. The producer state serves as an index of the consumer's
   loop invariant, so it can be viewed as auxiliary state (that is, ghost
   state) that is exposed to the consumer.

   The type of the user state is whatever the user chooses. The user state
   is also known as the accumulator, or the loop-carried state. *)

(* [P] is the type of the producer state. *)
Context {P : Type}.
Implicit Types i j k : P.

(* We assume that the type [P] is equipped with an equivalence [≡].
   For example, [P] could be a type of sets, equipped with extensional
   equality. Then, we require the user invariant [inv] to respect this
   equality; otherwise, some producers could not be verified. *)
(* In cases where [≡] is just Leibniz equality, this machinery is
   unnecessary; nevertheless we make it mandatory, for simplicity. *)
Context `{Equiv P}.

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
  (* The loop invariant must be compatible with [≡]. *)
  Proper (equiv ==> eq ==> iff) inv →
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
  Proper (equiv ==> eq ==> eq ==> iff) inv →
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
  Proper (equiv ==> eq ==> iff) inv →
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

(* A specialization of [ITER] where the producer state is a history (a list). *)

Section L.

Context {A : Type}.

(* A producer state is a history: a list of elements produced so far. *)
Implicit Type history future : list A.

(* [init] is the initial state. *)
Variable init : list A.

(* A list that satisfies the predicate [complete] is a final state. *)
Variable complete : list A → Prop.

(* Each step extends the history with one element [x]. Not every step is
   permitted, though: extending [history] with [x] is permitted only if
   the extended history [history ++ {[x]}] is a prefix of some complete
   list. *)
Definition permitted : list A → Prop :=
  λ history, ∃ future, complete (history ++ future).

(* If [complete] is nonempty, then the empty history is permitted. *)

Lemma permitted_nil : (∃ history, complete history) → permitted [].
Proof. intros (history & ?). unfold permitted. eauto. Qed.

(* A partial history is permitted if and only if it is a prefix of a
   complete history. *)

Lemma permitted_iff history :
  permitted history ↔
  ∃ history', history `prefix_of` history' ∧ complete history'.
Proof.
  unfold permitted, prefix. split.
  + intros (future & ?). eauto.
  + intros (history' & (future & ?) & ?). subst. eauto.
Qed.

(* The predicate [permitted] is prefix-closed. *)

Lemma permitted_prefix history1 history2 :
  permitted (history1 ++ history2) → permitted history1.
Proof.
  unfold permitted. intros (future' & ?). list in *. eauto.
Qed.

Lemma permitted_prefix_of history history' :
  permitted history' → history `prefix_of` history' → permitted history.
Proof.
  unfold prefix. intros ? (future & ?). subst.
  eauto using permitted_prefix.
Qed.

(* The definition of [≡] on lists in stdpp is extensional equality of the
   underlying sets. This is NOT what we want: equality of histories should
   be equality of lists, up to equivalence of the list elements. Therefore
   we use a local instance of [≡] here. *)

(* At this time, we cut corners and use just Leibniz equality, because it
   is suitable for our current use cases. *)

(* In [HITERI], the body is parameterized with the current element [x] and
   with its index [i] in the history. *)

Definition HITERI {S}
  (body : A → Z → S → WP S)
  (loop : S → WP S)
: Prop :=
  @ITER (list A) (eq)
    init complete S
    ( λ history0 history1 s Q,
      ∀ x i,
      init `prefix_of` history0 →
      history0 ++ {[x]} = history1 →
      permitted history1 →
      i = length history0 →
      body x i s Q
    )
    loop.

(* In [HITER], the body is parameterized with the current element [x]. *)

Definition HITER {S}
  (body : A → S → WP S)
  (loop : S → WP S)
: Prop :=
  HITERI
    (λ x i s Q, body x s Q)
    loop.

(* -------------------------------------------------------------------------- *)

(* A collection of common definitions of [complete]. *)

(* Iteration on a sequence, in order. *)

Definition complete_sequence (xs : list A) :=
  λ history, history = xs.

(* Iteration on a sequence, in an unspecified order. *)

(* This can also be understood as iteration on a multiset. *)

Definition complete_multiset (xs : list A) :=
  λ history, history ≃ xs.

(* The constraint [SemiSet A C] means that [C] is a type of sets of
   elements of type [A], which supports empty set, union, inclusion,
   and equivalence. *)

Context `{SemiSet A C}.

(* Iteration on a set, in an unspecified order. *)

(* [complete_set] allows repetitions: an element can be produced several
   times. [complete_set_unique] forbids repetitions. *)

Definition complete_set (xs : C) :=
  λ history, list_to_set history ≡ xs.

Definition complete_set_unique (xs : C) :=
  λ history, list_to_set history ≡ xs ∧ NoDup history.

End L.

(* A characterization of [permitted (complete_sequence xs)]. *)

(* When iterating on a sequence [xs], a history is permitted
   if and only if it is a prefix of [xs]. *)

Lemma permitted_sequence {A} (history xs : list A) :
  permitted (complete_sequence xs) history ↔
  history `prefix_of` xs.
Proof.
  rewrite permitted_iff. unfold complete_sequence. split.
  + intros (? & ? & ->). eauto.
  + eauto.
Qed.

(* A characterization of [permitted (complete_multiset xs)]. *)

(* When iterating on a multiset [xs], a history is permitted
   if and only if it is a submultiset of [xs]. *)

(* The relation [⊆+] is defined in stdpp/list_relations.v.
   Its full name is [submseteq]. *)

Lemma submseteq_insert_r {A} (history future : list A) :
  history ⊆+ history ++ future.
Proof.
  apply submseteq_inserts_r. eauto.
Qed.

Lemma permitted_multiset {A} (history xs : list A) :
  permitted (complete_multiset xs) history ↔
  history ⊆+ xs.
Proof.
  rewrite permitted_iff. unfold complete_multiset. split.
  + intros (? & (future & ->) & Hcomplete).
    apply Permutation_submseteq in Hcomplete.
    transitivity (history ++ future); [| exact Hcomplete ].
    apply submseteq_insert_r.
  + intros (future & ?)%submseteq_Permutation.
    exists (history ++ future). split.
    - eauto using prefix_app_l.
    - symmetry. eauto.
Qed.

Section F.

(* The constraint [FinSet A C] means that [C] is a type of finite sets of
   elements of type [A]. It requires the existence of a function
   [elements : C → list A] such that the list [elements xs] has no
   duplicate elements and membership in [xs] is equivalent to membership
   in [elements xs]. *)

Context `{FinSet A C}.

(* This instance exists in [stdpp/fin_sets.v] but is declared Local,
   so we have to copy it here. *)

Local Instance elem_of_dec_slow : RelDecision (∈@{C}).
Proof.
  refine (λ x X, cast_if (decide_rel (∈) x (elements X)));
    by rewrite <-(elem_of_elements _).
Qed.

(* A characterization of [permitted (complete_set xs)]. *)

(* When iterating on a finite set [xs], a history is permitted
   if and only if it is a subset of [xs]. *)

Lemma permitted_set (history : list A) (xs : C) :
  permitted (complete_set xs) history ↔
  list_to_set history ⊆ xs.
Proof.
  rewrite permitted_iff. unfold complete_set. split.
  + intros (? & (future & ->) & Hcomplete). set_solver.
  + intro.
    exists (history ++ elements xs). split.
    - eauto using prefix_app_l.
    - rewrite list_to_set_app, list_to_set_elements. set_solver.
Qed.

(* A characterization of [permitted (complete_set_unique xs)]. *)

(* When iterating without repetition on a finite set [xs],
   a history is permitted if and only if it is a subset of [xs]
   and it has no duplicate elements. *)

Lemma permitted_set_unique (history : list A) (xs : C) :
  permitted (complete_set_unique xs) history ↔
  list_to_set history ⊆ xs ∧ NoDup history.
Proof.
  rewrite permitted_iff. unfold complete_set_unique. split.
  + intros (? & (future & ->) & (? & ?)). split.
    - set_solver.
    - rewrite NoDup_app in *. tauto.
  + intros (? & ?).
    exists (history ++ elements (xs ∖ list_to_set history)). split.
    - eauto using prefix_app_l.
    - rewrite list_to_set_app, list_to_set_elements. split.
      { symmetry. apply union_difference. assumption. }
      { rewrite NoDup_app. split; eauto. split.
        + set_solver.
        + apply NoDup_elements. }
Qed.

Lemma NoDup_snoc (history : list A) (x : A) :
  NoDup (history ++ {[x]}) ↔
  NoDup history ∧ x ∉ history.
Proof.
  apply NoDup_snoc.
Qed.

End F.

Hint Rewrite
  @permitted_sequence
  @permitted_multiset
  @permitted_set
  @permitted_set_unique
  using eauto with typeclass_instances
: permitted.

Tactic Notation "permitted" :=
  autorewrite with permitted.

Tactic Notation "permitted" "in" hyp(h) :=
  autorewrite with permitted in h.

Tactic Notation "permitted" "in" "*" :=
  autorewrite with permitted in *.

Tactic Notation "complete" :=
  unfold
    complete_sequence, complete_multiset,
    complete_set, complete_set_unique.

Tactic Notation "complete" "in" hyp(h) :=
  unfold
    complete_sequence, complete_multiset,
    complete_set, complete_set_unique
  in h.

Tactic Notation "complete" "in" "*" :=
  unfold
    complete_sequence, complete_multiset,
    complete_set, complete_set_unique
  in *.

(* The tactic [hiteri_step x i] is meant to be used after [wp_body ...].
   Then the goal is [∀ x i,
                     init `prefix_of` history0 →
                     history0 ++ {[x]} = history1 →
                     permitted history1 →
                     i = length history0 → ...].
   The tactic introduces these hypotheses
   and uses the equation to substitute away [history1]. *)

Tactic Notation "hiteri_step" simple_intropattern(x) simple_intropattern(i) :=
  let Hpermitted := fresh "Hpermitted" in
  intros x i ? <- Hpermitted ?;
  permitted in Hpermitted.

(* -------------------------------------------------------------------------- *)

(* Hints. *)

Lemma prefix_refl {A} (xs : list A) : xs `prefix_of` xs.
Proof. eauto. Qed.

Hint Resolve
  prefix_nil
  prefix_refl
  prefix_app_l
: marble.

(* When the goal is [permitted _ _], use the tactic [permitted] to
   simplify the goal, then conclude using [tc]. *)

Hint Extern 1 (permitted _ _) => (progress permitted; tc) : marble.

(* At the end of a loop, the last subgoal should have the form
   [∀ s, (∃ k, inv k s ∧ complete k) → ...]. The tactic
   [wp_loop_postcondition_hook] is applied to this subgoal. *)

Ltac wp_loop_postcondition_hook ::=
  complete.

(* -------------------------------------------------------------------------- *)

(* Iteration on a list. *)

Definition ITERI_LIST {S A}
  (init xs : list A)
  (body : A → Z → S → WP S)
  (loop : S → WP S)
: Prop :=
  HITERI init (complete_sequence xs) body loop.

(* In [ITER_LIST], the loop body is parameterized with just [x]. *)

Definition ITER_LIST {S A}
  (init xs : list A)
  (body : A → S → WP S)
  (loop : S → WP S)
: Prop
:=
  HITER init (complete_sequence xs) body loop.

(* -------------------------------------------------------------------------- *)

(* Iteration on a list, in an unspecified (unpredictable) order. *)

(* This can be understood as iteration on a multiset. *)

(* The producer state is the history, that is, the list of elements
   produced so far. Each step extends the history with one element [x].
   The list [init] is the initial producer state; a history that is a
   submultiset of the list [xs] is a valid history; a history that is
   equal (as a multiset) to the list [xs] is final. *)

(* The relation [⊆+] is defined in stdpp/list_relations.v.
   Its full name is [submseteq]. *)

Local Infix "≃" := (Permutation)
  (at level 70, no associativity).

Definition ITERI_MULTISET {S A}
  (init xs : list A)
  (body : A → Z → S → WP S)
  (loop : S → WP S)
: Prop
:=
  @ITER (list A) (eq)
    init
    ( λ history, history ≃ xs )
    S
    ( λ history0 history1 s Q,
      ∀ x i,
      init `prefix_of` history0 →
      history0 ++ {[x]} = history1 →
      history1 ⊆+ xs →
      i = length history0 →
      body x i s Q
    )
    loop.

Definition ITER_MULTISET {S A}
  (init xs : list A)
  (body : A → S → WP S)
  (loop : S → WP S)
: Prop
:=
  ITERI_MULTISET
    init xs
    ( λ x i s Q, body x s Q )
    loop.

(* -------------------------------------------------------------------------- *)

(* Iteration on a set, in an unspecified order. *)

(* The constraint [SemiSet A C] means that [C] is a type of sets of
   elements of type [A], which supports empty set, union, inclusion,
   and equivalence. *)

(* The specification [ITER_SET] allows repetitions: an element can be
   produced several times. The specification [ITER_SET_UNIQUE] forbids
   repetitions. *)

(* Should the producer state be a set, or a list? It can be either. We
   propose both variants, and prove (in misc.v) that (up to covariance
   hypotheses on [body] and [loop]) they are equivalent. *)

(* In the first variant, the producer state is the set of elements produced
   so far. The user invariant [inv] must be compatible with the extensional
   equality of sets [≡]. *)

Definition ITER_SET {S A} `{SemiSet A C}
  (init xs : C)
  (body : A → S → WP S)
  (loop : S → WP S)
: Prop
:=
  ITER
    init
    ( λ history, history ≡ xs )
    ( λ history0 history1 s Q,
      ∀ x,
      init ⊆ history0 →
      history0 ∪ {[x]} ≡ history1 →
      history1 ⊆ xs →
      body x s Q
    )
    loop.

Tactic Notation "set_step" simple_intropattern(x) :=
  intros x ? ? ?.

Definition ITER_SET_UNIQUE {S A} `{SemiSet A C}
  (init xs : C)
  (body : A → S → WP S)
  (loop : S → WP S)
: Prop
:=
  ITER
    init
    ( λ history, history ≡ xs )
    ( λ history0 history1 s Q,
      ∀ x,
      init ⊆ history0 →
      x ∉ history0 → (* no repetitions *)
      history0 ∪ {[x]} ≡ history1 →
      history1 ⊆ xs →
      body x s Q
    )
    loop.

(* In the second variant, the producer state is the list of elements produced
   so far. *)

Definition ITER_SET' {S A} `{SemiSet A C}
  (init : list A) (xs : C)
  (body : A → S → WP S)
  (loop : S → WP S)
: Prop
:=
  @ITER (list A) (eq)
    init
    ( λ history, xs ≡ list_to_set history)
    S
    ( λ history0 history1 s Q,
      ∀ x,
      init `prefix_of` history0 →
      history0 ++ {[x]} = history1 →
      list_to_set history1 ⊆ xs →
      body x s Q
    )
    loop.

Definition ITER_SET_UNIQUE' {S A} `{SemiSet A C}
  (init : list A) (xs : C)
  (body : A → S → WP S)
  (loop : S → WP S)
: Prop
:=
  @ITER (list A) (eq)
    init
    ( λ history, xs ≡ list_to_set history)
    S
    ( λ history0 history1 s Q,
      ∀ x,
      init `prefix_of` history0 →
      x ∉ history0 → (* no repetitions *)
      history0 ++ {[x]} = history1 →
      list_to_set history1 ⊆ xs →
      body x s Q
    )
    loop.

(* -------------------------------------------------------------------------- *)

(* Iteration on a semi-open interval [i, k) of the integers in [nat]. *)

(* To avoid duplication, we parameterize these definitions with
   a direction, which is [Up] or [Down]. *)

Inductive direction := Up | Down.

Section Nat.
Open Scope nat_scope.

(* The producer state [j] is the loop index. *)

Local Instance equiv_nat : Equiv nat := (=).

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
: Prop
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
: Prop
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
: Prop
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

Local Instance equiv_Z : Equiv Z := (=).

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

(* The tactic [z_step] is meant to be used after [wp_body ...],
   while iterating on an interval of the integers.
   Then, the goal is [j1 = j0 + 1 → i ≤ j0 < k → ...]
                  or [j0 = j1 + 1 → i ≤ j1 < k → ...].
   The tactic introduces these hypotheses
   and uses the equation to substitute away [j0] or [j1]. *)

Ltac z_step :=
  intros -> ?.

Definition ITER_Z {S}
  i k dir
  (body : Z → S → WP S)
  (loop : S → WP S)
: Prop
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
: Prop
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
: Prop
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

(* [expand_ITER] has an empty definition in wp.v, and is invoked by
   [wp_loop_precondition_hook]. We redefine it here. *)

Ltac expand_ITER ::=
  unfold
    ITER_NAT, XITER_NAT, UXITER_NAT, nat_init, nat_step,
    ITER_Z, XITER_Z, UXITER_Z, z_init, z_step,
    ITER_LIST, ITERI_LIST,
    ITER_MULTISET, ITERI_MULTISET,
    ITER_SET, ITER_SET_UNIQUE,
    ITER_SET', ITER_SET_UNIQUE',
    HITER, HITERI,
    ITER, XITER, UXITER
  ;
  simpl implication.

Tactic Notation "expand_ITER" "in" hyp(h) :=
  unfold
    ITER_NAT, XITER_NAT, UXITER_NAT, nat_init, nat_step,
    ITER_Z, XITER_Z, UXITER_Z, z_init, z_step,
    ITER_LIST, ITERI_LIST,
    ITER_MULTISET, ITERI_MULTISET,
    ITER_SET, ITER_SET_UNIQUE,
    ITER_SET', ITER_SET_UNIQUE',
    HITER, HITERI,
    ITER, XITER, UXITER
  in h;
  simpl implication in h.

(* The tactic [ITER] should be used when the goal is [ITER ...]. *)

Ltac ITER :=
  expand_ITER;
  intros ? ? Hcompatible Hinit Hbody;
  complete.

Ltac XITER :=
  expand_ITER;
  intros ? ? Hcompatible Hinit Hbody;
  complete.

Ltac UXITER :=
  expand_ITER;
  intros ? Hcompatible Hinit Hbody;
  complete.

(* The tactics [wp_continue] and [wp_break] help reason about invocations
   of [continue] and [break]. They recognize a suitable hypothesis and
   apply it. *)

Ltac wp_continue :=
  match goal with
  | Hcontinue: ∀ s, _ → wp (?continue s) _,
    Hbreak: ∀ s x, _ → wp (?break s x) _
    |- wp (?continue _) _ =>
      simple eapply Hcontinue; clear Hcontinue Hbreak
  | Hcontinue: _ → wp (?continue ()) _,
    Hbreak: ∀ x, _ → wp (?break x) _
    |- wp (?continue ()) _ =>
      simple eapply Hcontinue; clear Hcontinue Hbreak
  end.

Ltac wp_break :=
  match goal with
  | Hcontinue: ∀ s, _ → wp (?continue s) _,
    Hbreak: ∀ s x, _ → wp (?break s x) _
    |- wp (?break _ _) _ =>
      simple eapply Hbreak; clear Hcontinue Hbreak
  | Hcontinue: _ → wp (?continue ()) _,
    Hbreak: ∀ x, _ → wp (?break x) _
    |- wp (?break _) _ =>
      simple eapply Hbreak; clear Hcontinue Hbreak
  end.

(* The tactic [wp_body] helps introduce variables at the beginning
   of the body of a loop. *)

(* The goal typically is [∀ j0 j1 s, inv ... → ...] or
                         [∀ j0 j1,   inv ... → ...].
   (See [ITER], [XITER], [UXITER].)

   The parameters of [wp_body] should be [j0 j1] or [j0 j1 s],
   followed with a tactic [more_intros].

   After introducing [j0], [j1], and possibly [s],
   [wp_body] introduces the invariant [Hinv],
   executes the tactic [more_intros],
   then applies [wp_body_hook] to [Hinv],
   so as to perform simplification.

   Things would be simpler if we could perform simplification before
   executing [more_intros]; then there would be no need to pass
   [more_intros] as a parameter to [wp_body]. However, it is important
   to introduce all of the variables before calling [wp_body_hook]. *)

(* After using [wp_body ...], one should typically use [z_step] or
   [hiteri_step] or a similar tactic to introduce the hypotheses that
   express the fact that one step has been made. *)

Ltac wp_body_hook Hinv :=
  z in Hinv;
  unpack in Hinv.

Tactic Notation "wp_body" simple_intropattern_list(ps)
                "introducing:" tactic1(more_intros) :=
  intros ps;
  let Hinv := fresh "Hinv" in
  intro Hinv;
  more_intros ();
  wp_body_hook Hinv.
