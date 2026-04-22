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

From stdpp Require Import numbers well_founded.
From Stdlib Require Export ZifyNat.
  (* [ZifyNat] magically makes [lia] more powerful,
     including on goals that involve division in Z *)
From Stdlib Require Import Uint63 ZifyUint63.
  (* [ZifyUint63] magically makes [lia] more powerful *)
From Stdlib Require Import Wellfounded.Wellfounded.
Notation Succ := S. (* avoid name clash *)
From listz Require Import listz.
From marble Require Import tactics bool wp iteration int.
From marble Require Import equations.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

(* This file defines several higher-order functions that implement loops and
   exitable loops. *)

(* -------------------------------------------------------------------------- *)

(* We first define two higher-order functions, [simple_loop] and [loop],
   which implement an exitable infinite loop. *)

(* In an infinite loop, there is no producer state; one could say that
   the producer state has type [unit] and the predicate [complete] is
   [λ _, false]. The producer never terminates: the loop must be ended
   by the consumer. Therefore the obligation of proving that the loop
   terminates falls entirely onto the consumer. The consumer must
   prove that the consumer state evolves along a well-founded relation
   [R]. We write [s' ≺ s] for [R s' s]. *)

(* -------------------------------------------------------------------------- *)

(* We begin with a simple loop, where the termination argument cannot exploit
   a loop invariant. This loop combinator expects the loop body to be written
   in double-continuation-passing style: that is, the loop body receives two
   continuations [continue] and [break]. *)

(* When calling [continue s'], the loop body must supply a proof of [s' ≺ s]. *)

Section SimpleLoop.

(* [S] is the type of the consumer's state. *)

(* [A] is the type of the final result that the consumer returns,
   in addition to the state, once the loop ends. In other words,
   it is the type of [x] in [break s x]. *)

Context {S A : Type}.
Implicit Types s : S.

(* [R] is a well-founded relation on the consumer state. *)

Variable R : relation S.
Context `{WellFounded S R}.
Infix "≺" := R (at level 70, no associativity).

Section Body.

(* The calling convention of the loop body is [body s continue break].
   The body can choose to either call [continue s' pf], where [pf] is
   a proof of [s' ≺ s], or call [break s' x]. *)

Variable body :
  ∀ {W},
  ∀ s : S,
  (∀ s' : S, s' ≺ s → W) →
  (S → A → W) →
  W.

(* The code. *)

Fixpoint simple_loop_aux s (ACC : Acc R s) : S * outcome A :=
  let continue s' (pf : s' ≺ s) := simple_loop_aux s' (Acc_inv ACC pf) in
  let break s x := (s, Break x) in
  body s continue break.

End Body.

Definition simple_loop s body :=
  simple_loop_aux body s ltac:(tc).

(* A specification of this infinite exitable loop. *)

(* This can be viewed as a variant of [XITER] in iteration.v, where the
   producer state has type [unit], the predicate [complete] is [false], and
   the continuation [continue] expects a proof that the state decreases. *)

Definition SIMPLE_LOOP
  (body : ∀ {W} s, (∀ s' : S, s' ≺ s → W) → (S → A → W) → W)
  (loop : S * outcome A)
  (s : S)
:=
  ∀ inv ,
  (* Initially, [out] is [Continue]. *)
  inv s Continue →
  (* When the loop body is invoked,
     it can assume that [out] is [Continue]. *)
  ( ∀ s,
    inv s Continue →
    ∀ {W} (Q : W → Prop) (continue : ∀ s', s' ≺ s → W) (break : S → A → W),
    (* Invoking [continue s pf] is like returning [(s, Continue)]. *)
    (∀ s' (pf : s' ≺ s), inv s' Continue  → wp (continue s' pf) Q) →
    (* Invoking [break s x] is like returning [(s, Break x)]. *)
    (∀ s' x, inv s' (Break x) → wp (break s' x) Q) →
    wp (body s continue break) Q
  ) →
  (* Once the loop ends, we must have [broken out]. *)
  wp loop (λ '(s, out), inv s out ∧ broken out).

(* [simple_loop_aux] is correct. *)

Lemma wp_simple_loop_aux
  (body : ∀ {W} s, (∀ s' : S, s' ≺ s → W) → (S → A → W) → W)
  s ACC :
  SIMPLE_LOOP (@body) (simple_loop_aux (@body) s ACC) s.
Proof.
  unfold SIMPLE_LOOP.
  by dependent induction on s ACC. intros s Achild IH.
  intros inv Hinit Hbody.
  simpl simple_loop_aux.
  wp_apply Hbody.
  (* Exit continuation. *)
  { intros. wp_ret. eauto. }
Qed.

(* [simple_loop] is correct. *)

Lemma wp_simple_loop
  (body : ∀ {W} s, (∀ s' : S, s' ≺ s → W) → (S → A → W) → W)
  s :
  SIMPLE_LOOP (@body) (simple_loop s (@body)) s.
Proof.
  eapply wp_simple_loop_aux.
Qed.

End SimpleLoop.

(* -------------------------------------------------------------------------- *)

(* In the definition of our second infinite exitable loop, we need
   this sum type, as well as a rich conditional on this sum type. *)

(* We do not introduce sugared syntax here, though perhaps we could. *)

Inductive message S A :=
| MContinue:  S → message S A
| MBreak: S → A → message S A.

Arguments MContinue {S A} s.
Arguments MBreak {S A} s x.

Lemma MATCH_match_message {S A W} (m : message S A)
  (continue' : ∀ s', m = MContinue s' → W)
  (continue : S → W)
  (break : S → A → W)
:
  (∀ s' Heq, continue' s' Heq = continue s') →
  match m as m' return m = m' → _ with
  | MContinue s' => λ Heq, continue' s' Heq
  | MBreak s' x => λ _, break s' x
  end eq_refl
  =
  match m with
  | MContinue s' => continue s'
  | MBreak s' x => break s' x
  end.
Proof.
  intros. destruct m; eauto.
Qed.

Lemma wp_MATCH_message {S A W} (m : message S A)
  (continue : ∀ s', m = MContinue s' → W)
  (break : S → A → W) (Q : W → Prop) :
  (∀ s',   ∀ Heq : m = MContinue s', wp (continue s' Heq) Q) →
  (∀ s' x, ∀ Heq : m = MBreak s' x , wp (break s' x) Q) →
  wp (
    match m as m' return m = m' → _ with
    | MContinue s' => λ Heq, continue s' Heq
    | MBreak s' x => λ _, break s' x
    end eq_refl
  ) Q.
Proof.
  intros. destruct m; eauto.
Qed.

Ltac wp_match_message :=
  simple eapply wp_MATCH_message; intros.

(* -------------------------------------------------------------------------- *)

(* We continue with a more complex loop, where the termination argument can
   exploit a loop invariant. Furthermore, we allow the proofs of preservation
   and termination to be performed together, a posteriori, and in [wp] style.
   The only proof that still must be provided a priori is the proof that the
   invariant holds initially. *)

(* We DO NOT expect the loop body to be written in continuation-passing style,
   because this seems to make things more difficult. Instead, we require the
   loop body to return a value of type [message], a sum type. Therefore it is
   clear that the loop body can terminate only once. If the loop body were
   written in CPS style then it could potentially invoke several continuations
   (and throw away their results, except one) and it would be unclear how to
   extract the witnesses that we need out of a [wp] judgement about the body. *)

(* The loop invariant that is supplied at function definition time, [inv],
   need not be very rich. It should be just strong enough to argue that the
   loop terminates. If needed, later on, it is possible to propose a richer
   loop invariant, [inv']. See the reasoning rules [wp_loop] and [wp_loop']. *)

Section Loop.

Context {S A : Type}.
Implicit Types s : S.

Variable R : relation S.
Context `{WellFounded S R}.
Infix "≺" := R (at level 70, no associativity).

Section Body.

(* The calling convention of the loop body is [body s]. The body can
   return either [MContinue s'] or [MBreak s' x]. While defining the
   loop body, there is no need to argue about invariant preservation
   or about termination. *)

Variable body : S → message S A.

(* The loop invariant takes the form [inv s out]. *)

Variable inv : S → outcome A → Prop.

(* The invariant preservation argument must be provided as follows: *)

Variable preservation :
  ∀ {s s'}, inv s Continue → body s = MContinue s' → inv s' Continue.

(* The termination argument must be provided in the following form.
   The termination argument may exploit the loop invariant. *)

Variable decrease :
  ∀ {s s'}, inv s Continue → body s = MContinue s' → s' ≺ s.

(* The code of the auxiliary function [loop_aux]. *)

Fixpoint loop_aux s (ACC : Acc R s) (Hinv : inv s Continue)
: S * outcome A :=
  match body s as m return (body s = m → _) with
  | MBreak s' x => λ _,
      (s', Break x)
  | MContinue s' => λ Heq,
      loop_aux s'
        (Acc_inv ACC (decrease Hinv Heq))
        (preservation Hinv Heq)
  end eq_refl.

End Body.

Implicit Types body : S → message S A.
Implicit Types inv : S → outcome A → Prop.

(* A specification of the loop body. *)

(* When the loop body is invoked, it can assume that [out] is [Continue]. *)

(* The loop body must prove that it preserves the invariant. Furthermore,
   if it wishes to continue with state [s'] then it must prove [s' ≺ s].  *)

(* [BODY'] is a variant of [BODY] where there is no need to prove [s' ≺ s]. *)

Definition BODY body inv :=
  ∀ s,
  inv s Continue →
  wp (body s) (λ m,
    match m with
    | MContinue s' => s' ≺ s ∧ inv s' Continue
    | MBreak s' x  =>          inv s' (Break x)
    end).

Definition BODY' body inv :=
  ∀ s,
  inv s Continue →
  wp (body s) (λ m,
    match m with
    | MContinue s' =>          inv s' Continue
    | MBreak s' x  =>          inv s' (Break x)
    end).

(* A specification of this infinite exitable loop. *)

(* [LOOP'] is a variant of [LOOP] where the loop body does not have to prove
   [s' ≺ s]. *)

Definition LOOP body inv (loop : S * outcome A) (s : S) :=
  (* Under the assumption that the body is correct, *)
  BODY body inv →
  (* once the loop ends, we must have [broken out]. *)
  wp loop (λ '(s, out), inv s out ∧ broken out).

Definition LOOP' body inv (loop : S * outcome A) (s : S) :=
  (* Under the assumption that the body is correct, *)
  BODY' body inv →
  (* once the loop ends, we must have [broken out]. *)
  wp loop (λ '(s, out), inv s out ∧ broken out).

(* We now prove a few technical lemmas that help us define [loop] below. *)

(* If the body satisfies its specification [BODY body inv] then, when the
   body returns [MContinue s'], both [s' ≺ s] and [inv s' Continue] hold.
   This lets us produce the proofs [preservation] and [decrease] that
   [loop_aux] expects. *)

Local Lemma decrease_and_preservation body inv :
  BODY body inv →
  ∀ s s',
  inv s Continue →
  body s = MContinue s' →
  s' ≺ s ∧ inv s' Continue.
Proof.
  intros Hbody ? ? Hinv Heq.
  unfold BODY, wp in Hbody.
  specialize (Hbody s Hinv).
  rewrite Heq in Hbody. (* ha! *)
  assumption.
Qed.

Local Lemma decrease body inv :
  BODY body inv →
  ∀ s s', inv s Continue → body s = MContinue s' → s' ≺ s.
Proof.
  intros. eapply decrease_and_preservation; eauto.
Qed.

Local Lemma preservation body inv :
  BODY body inv →
  ∀ s s', inv s Continue → body s = MContinue s' → inv s' Continue.
Proof.
  intros. eapply decrease_and_preservation; eauto.
Qed.

Local Lemma preservation' body inv :
  BODY' body inv →
  ∀ s s', inv s Continue → body s = MContinue s' → inv s' Continue.
Proof.
  intros Hbody ? ? Hinv Heq.
  unfold BODY, wp in Hbody.
  specialize (Hbody s Hinv).
  rewrite Heq in Hbody. (* ha! *)
  assumption.
Qed.

(* If the body satisfies its specification, a [wp] judgement, then, when the
   body returns [MBreak s' x], [inv s' (Break x)] holds. *)

Local Lemma exit body inv :
  BODY body inv →
  ∀ s s' x, inv s Continue → body s = MBreak s' x → inv s' (Break x).
Proof.
  intros Hbody ? ? ? Hinv Heq.
  unfold BODY, wp in Hbody.
  specialize (Hbody s Hinv).
  rewrite Heq in Hbody. (* ha! *)
  assumption.
Qed.

Local Lemma exit' body inv :
  BODY' body inv →
  ∀ s s' x, inv s Continue → body s = MBreak s' x → inv s' (Break x).
Proof.
  intros Hbody ? ? ? Hinv Heq.
  unfold BODY, wp in Hbody.
  specialize (Hbody s Hinv).
  rewrite Heq in Hbody. (* ha! *)
  assumption.
Qed.

(* [loop_aux] is correct. *)

Local Lemma wp_loop_aux body inv
  (preservation : ∀ s s', inv s Continue → body s = MContinue s' → inv s' Continue)
  (decrease : ∀ s s', inv s Continue → body s = MContinue s' → s' ≺ s)
  s ACC :
  ∀ Hinv,
  LOOP body inv (loop_aux body inv preservation decrease s ACC Hinv) s.
Proof.
  unfold LOOP, BODY.
  by dependent induction on s ACC. intros s Achild IH.
  intros Hinv Hbody.
  simpl loop_aux.
  wp_match_message.
  (* Normal continuation.
     Wow! [eauto] applies [IH], [preservation], and [decrease]. *)
  { eauto. }
  (* Exit continuation. *)
  { wp_ret. split; [| eauto ].
    eapply exit; eauto. }
Qed.

Local Lemma wp_loop_aux' body inv
  (preservation : ∀ s s', inv s Continue → body s = MContinue s' → inv s' Continue)
  (decrease : ∀ s s', inv s Continue → body s = MContinue s' → s' ≺ s)
  s ACC :
  ∀ Hinv,
  ∀ inv',
  inv' s Continue →
  LOOP' body inv' (loop_aux body inv preservation decrease s ACC Hinv) s.
Proof.
  unfold LOOP', BODY'.
  by dependent induction on s ACC. intros s Achild IH.
  intros Hinv inv' Hinv' Hbody.
  simpl loop_aux.
  wp_match_message.
  (* Normal continuation. *)
  { eapply IH; eauto.
    eapply preservation'; eauto. }
  (* Exit continuation. *)
  { wp_ret. split; [| eauto ].
    eapply exit'; eauto. }
Qed.

Section ProofRules.

Context {inv : S → outcome A → Prop}.
Variable body : S → message S A.
Variable Hbody : BODY body inv.

(* The high-level combinator [loop]. *)

(* Outside of this section, the type of [loop] is
   [∀ inv body, BODY body inv → ∀ s, inv s Continue → S * outcome A]. *)

(* [loop body Hbody s Hinv] requires [Hbody], a proof of correctness of the
   loop body. So, an end user should first define [body] and prove that it
   is correct before constructing [loop body Hbody s Hinv]. *)

Definition loop s (Hinv : inv s Continue) :=
  loop_aux body inv
    (preservation body inv Hbody)
    (decrease body inv Hbody)
    s ltac:(tc) Hinv.

(* [loop] is correct. We offer two specifications. [wp_loop] uses a single
   invariant, [inv], to prove termination and functional correctness.
   [wp_loop'] distinguishes two invariants, [inv] and [inv']. The former
   must be just strong enough to prove termination, and is used a priori in
   the definition of the loop; the latter can be stronger or weaker and is
   used a posteriori in the proof of functional correctness of the loop. *)

Lemma wp_loop s (Hinv : inv s Continue) :
  LOOP body inv (loop s Hinv) s.
Proof.
  eapply wp_loop_aux.
Qed.

Lemma wp_loop' s (Hinv : inv s Continue) :
  ∀ inv',
  inv' s Continue →
  LOOP' body inv' (loop s Hinv) s.
Proof.
  unfold loop. eauto using wp_loop_aux'.
Qed.

End ProofRules.
End Loop.

(* -------------------------------------------------------------------------- *)

(* In the remainder of this file, we define several higher-order functions
   that implement loops and exitable loops over semi-open intervals of the
   unsigned primitive integers. *)

Local Open Scope Z_scope.
Implicit Types _i _j _k : int.
Implicit Types  i : Z.
Implicit Types  z : Z.

Local Ltac wp_intro_hook Hx ::=
  z in Hx; unpack in Hx.

(* -------------------------------------------------------------------------- *)

(* This tactic uses [lia] to resolve comparisons among machine integers. *)

(* We do not need it when we reason in Hoare style, because the reasoning
   rule [wp_if] and the type class [isBool] do the job then. We do need it
   when we perform equational reasoning. We use this style of reasoning
   to prove that an unrolled loop is equal to an ordinary loop. *)

Local Ltac resolve_aux b :=
  first [
    replace b with true by lia
  | replace b with false by lia
  ].

Local Ltac resolve :=
  match goal with
  | |- context[(?lhs =? ?rhs)%uint63] =>
      resolve_aux (lhs =? rhs)%uint63
  | |- context[(?lhs ≤? ?rhs)%uint63] =>
      resolve_aux (lhs ≤? rhs)%uint63
  | |- context[(?lhs <? ?rhs)%uint63] =>
      resolve_aux (lhs <? rhs)%uint63
  end.

(* -------------------------------------------------------------------------- *)

(* [N] is the unrolling factor that we use in our unrolled loops. *)

Definition N  : nat := 8.
Definition NZ : Z   := Eval compute in Z.of_nat N.
Definition Ni : int := Eval compute in Uint63.of_nat N.

Lemma ilt_n_minus_N {_n} :
  (_n <? Ni)%uint63 = false →
  ilt (_n - Ni)%uint63 _n.
Proof. unfold Ni. eauto with marble. Qed.
Local Hint Resolve ilt_n_minus_N : marble.

(* -------------------------------------------------------------------------- *)

(* A loop, counting down, using machine integers. *)

(* [iter_down _i _k s body] applies the loop body [body] to every machine
   integer from [_k], excluded, down to [_i], included. A state of type [S]
   is carried, whose initial value is [s]. *)

Section IterDown.
Context {S : Type}.
Implicit Types s : S.
Open Scope uint63.

(* We make [body] a section variable so that it is lambda-abstracted above
   [Fixpoint iter_down_aux]. In other words, it is not a parameter of the
   fixed point itself. This allows us to later easily specialize the code
   for a specific loop body, just by inlining. *)

Section Body.
Variable body : int → S → S.

(* We are careful to test the condition [_k =? _i] before decrementing [_k].
   Because our semi-open intervals are closed at the bottom end, we cannot
   first decrement and then test the condition [_k <? _i]. If [_i] is zero
   then this would underflow. *)

(* We define [iter_down_aux] by well-founded recursion over the index [_k].
   In the second branch, the fact that [_k =? _i] is false is needed in
   order to prove that [_k - 1] is less than [_k], a fact which itself is
   required by the termination argument. *)

(* The termination argument does not need the hypothesis [φ _i ≤ φ _k].
   Even in the absence of this hypothesis, termination is guaranteed,
   thanks to underflow. This said, later on, when we give a specification
   of [iter_down_aux], we assume [i ≤ k]. It would be unnatural and
   inconvenient to propose a specification that allows underflow to take
   place. *)

Fixpoint iter_down_aux _i _k s (ACC : Acc (rilt _i) _k) :=
  IFC _k =? _i THEN λ _,
    s
  ELSE λ Hki,
    let _k' := _k - 1 in
    do s ← body _k' s ;
    iter_down_aux _i _k' s (Acc_inv ACC (rilt_n_minus_1 _k _i Hki)).

End Body.

(* This notation hides the accessibility witness [ACC]. *)

Notation iter_down_aux__ body _i _k s :=
  (iter_down_aux body _i _k s (Acc_rilt _i _k)).

(* This wrapper function handles the case where the interval is empty
   by returning immediately in that case. *)

Definition iter_down _i _k s body :=
  if _k ≤? _i then s
  else iter_down_aux__ body _i _k s.

(* A specification of [iter_down_aux]. *)

(* This specification requires [i ≤ k]: that is, the top index [k] must
   be greater than or equal to the bottom index [i]. This hypothesis is
   natural: it is required to guarantee that no underflow takes place. *)

Lemma wp_iter_down_aux (body : int → S → S) :
  ∀IntU _i i ,
  ∀IntU _k k ,
  i ≤ k →
  ∀ ACC,
  ITER_Z i k Down
    (λ j s Q, ∀ _j, isInt _j j → wp (body _j s) Q)
    (λ s Q, wp (iter_down_aux body _i _k s ACC) Q).
Proof.
  intros _i i ? ?.
  by well-founded induction on _k along (rilt _i).
  intros. ITER. expand_ITER in IH.
  intros; destruct ACC; simpl.
  wp_if; z.
  (* Case [k = i]. *)
  { wp_ret. }
  (* Case [k ≠ i]. *)
  { wp_op Hbody shadowing: s.
    wp_op IH shadowing: s.
    eauto. }
Qed.

(* A specification of [iter_down]. *)

(* Here, [i ≤ k] is not required. The interval may be empty. *)

Lemma wp_iter_down (body : int → S → S) :
  ∀IntU _i i ,
  ∀IntU _k k ,
  ITER_Z i k Down
    (λ j s Q, ∀ _j, isInt _j j → wp (body _j s) Q)
    (λ s Q, wp (iter_down _i _k s body) Q).
Proof.
  intros. ITER. unfold iter_down.
  wp_if; z.
  (* Case [k ≤ i]. *)
  { wp_ret. }
  (* Case [i < k]. *)
  { wp_op wp_iter_down_aux shadowing: s.
    eauto. }
Qed.

(* -------------------------------------------------------------------------- *)

(* A "static" variant of [iter_down], where the difference [k - i] is
   statically known and is represented by a natural number [n]. *)

(* We COULD prove Hoare-style specifications (that is, [wp] judgements)
   about the functions that we define below: [static_iter_down_aux],
   [iter_down_N], [iter_down_unrolled_aux], and [iter_down_unrolled]. In
   fact, we did so in an earlier version of this code. However, we now
   instead prove an equivalence result: an unrolled loop is equal to an
   ordinary loop. This result is more painful to prove, but more useful,
   as it lets us decide after the fact (possibly at a call site) whether
   we prefer to use an ordinary loop or an unrolled loop. *)

(* Perhaps we could have obtained equivalence via the Hoare-style rules,
   reasoning in Hoare style about the unrolled loop and stating (in its
   postcondition) that it returns the same result as an ordinary loop. *)

Section Body.
Variable body : int → S → S.

Fixpoint static_iter_down_aux _k s (n : nat) :=
  match n with
  | O =>
      s
  | Succ n =>
      do _k ← _k - 1 ;
      do s ← body _k s ;
      static_iter_down_aux _k s n
  end.

End Body.

(* Specialize [static_iter_down] for [N]. *)

Definition iter_down_N _k s body :=
  Eval compute -[bind] in static_iter_down_aux body _k s N.

(* Print iter_down_N. *)

(* -------------------------------------------------------------------------- *)

(* An unrolled variant of [iter_down]. *)

(* [iter_down_N] is used at each iteration, so the cost of the
   comparison and conditional jump is paid only once in [N]
   iterations. *)

Section Body.
Variable body : int → S → S.

Fixpoint iter_down_unrolled_aux _k _n s (ACC : Acc ilt _n) :=
  IFC _n <? Ni THEN λ _,
    iter_down (_k - _n) _k s body
  ELSE λ Hn,
    do s ← iter_down_N _k s body ;
    do _k ← _k - Ni ;
    let _n := _n - Ni in
    iter_down_unrolled_aux _k _n s (Acc_inv ACC (ilt_n_minus_N Hn)).

End Body.

Definition iter_down_unrolled _i _k s body :=
  if _k ≤? _i then s
  else iter_down_unrolled_aux body _k (_k - _i) s ltac:(tc).

(* -------------------------------------------------------------------------- *)

(* An unrolled loop is equal to an ordinary loop. *)

Section Eq.
Variable body : int → S → S.
Open Scope uint63.
Local Opaque Acc_ilt Acc_rilt.
Local Opaque bind.

(* First, we prove that [iter_down_aux] satisfies its fixed point equation.
   This is also a proof irrelevance result: [iter_down_aux] is a constant
   function with respect to [ACC]. *)

Lemma iter_down_aux_eq _i _k ACC : ∀ s,
  iter_down_aux body _i _k s ACC =
  if _k =? _i then
    s
  else
    do s ← body (_k - 1) s ;
    iter_down_aux__ body _i (_k - 1) s.
Proof.
  by dependent induction on _k ACC. intros _k. intros. simpl.
  eapply IFC_if; [ reflexivity | intro ].
  eapply bind_bind_eq; [ reflexivity | intro ]. (* optional *)
  (* [setoid_rewrite] rewrites both occurrences, thereby showing that
     [iter_down_aux ...] does not depend on its argument [ACC]. *)
  setoid_rewrite IH; tc.
Qed.

(* Then, we prove that [static_iter_down_aux _k s n] is equivalent to
   an ordinary loop over the interval [k - n, k). We must assume that
   the natural integer [n] lies in the interval of the machine integers. *)

Lemma static_iter_down_aux_eq n : ∀ _k s,
  unsigned (Z.of_nat n) →
  static_iter_down_aux body _k s n =
  iter_down_aux__ body (_k - of_nat n) _k s.
Proof.
  induction n as [| n ]; intros; simpl static_iter_down_aux.
  { rewrite iter_down_aux_eq. resolve. reflexivity. }
  { unfold bind at 1.
    setoid_rewrite IHn; [ clear IHn | lia ].
    rewrite iter_down_aux_eq. resolve.
    replace (_k - of_nat (Succ n)) with
            (_k - 1 - of_nat n) by lia.
    reflexivity. }
Qed.

(* Next, we check that [iter_down_unrolled_aux] satisfies its fixed point
   equation. In this equation, on the fly, we replace [iter_down_N] with
   an equivalent call to [iter_down_aux]. *)

Lemma iter_down_unrolled_aux_eq _n ACC : ∀ _k s,
  iter_down_unrolled_aux body _k _n s ACC =
  if _n <? Ni then
    iter_down (_k - _n) _k s body
  else
    do s ← iter_down_aux__ body (_k - Ni) _k s ;
    do _k ← _k - Ni ;
    let _n := _n - Ni in
    iter_down_unrolled_aux body _k _n s ltac:(tc).
Proof.
  by dependent induction on _n ACC. intros _n. intros.
  simpl iter_down_unrolled_aux.
  eapply IFC_if; [ reflexivity | intro ].
  change (iter_down_N _k s body)
    with (static_iter_down_aux body _k s N).
  rewrite static_iter_down_aux_eq by (unfold N; lia).
  setoid_rewrite IH; tc.
Qed.

(* This lemma expresses the key reason why unrolling a loop is possible:
   iterating first from [_c] down to [_b], then from [_b] down to [_a],
   is the same as iterating from [_c] down to [_a]. *)

Lemma iter_down_aux_glue _a _b _c : ∀ s ACC,
  (to_Z _a ≤ to_Z _b ≤ to_Z _c)%Z →
  (
    do s ← iter_down_aux body _b _c s ACC ;
    iter_down_aux__ body _a _b s
  )
  = iter_down_aux__ body _a _c s.
Proof.
  by well-founded induction on _c along (rilt _b).
  intros. rewrite iter_down_aux_eq.
  destruct (_c =? _b) eqn:?.
  (* Base case. *)
  { unfold bind at 1.
    assert (_c = _b) as -> by lia.
    reflexivity. }
  (* Step case. *)
  { rewrite bind_bind.
    rewrite iter_down_aux_eq. resolve.
    eapply bind_bind_eq; [ reflexivity | intro ].
    eapply IH; tc. }
Qed.

(* A first loop unrolling result: [iter_down_unrolled_aux] is equivalent
   to [iter_down_aux] with suitable parameters. *)

Lemma iter_down_unrolled_aux_equiv _n ACC : ∀ _k s,
  unsigned (to_Z _k - to_Z _n)%Z →
  iter_down_unrolled_aux body _k _n s ACC =
  iter_down_aux__ body (_k - _n) _k s.
Proof.
  by dependent induction on _n ACC. intros _n. intros.
  rewrite iter_down_unrolled_aux_eq.
  destruct (_n <? Ni) eqn:?.
  (* Base case. *)
  { destruct (_n =? 0) eqn:?.
    + unfold iter_down. resolve.
      rewrite iter_down_aux_eq. resolve.
      reflexivity.
    + unfold iter_down. resolve.
      reflexivity. }
  (* Step case. *)
  { unfold bind at 2.
    setoid_rewrite IH; tc.
    replace (_k - Ni - (_n - Ni)) with (_k - _n) by lia.
    eapply iter_down_aux_glue. lia. }
Qed.

(* The desired loop unrolling result: [iter_down_unrolled] is equivalent
   to [iter_down] with suitable parameters. *)

Lemma iter_down_unrolled_eq _i _k s :
  iter_down_unrolled _i _k s body =
  iter_down _i _k s body.
Proof.
  unfold iter_down_unrolled, iter_down.
  destruct (_k ≤? _i) eqn:?.
  { reflexivity. }
  { rewrite iter_down_unrolled_aux_equiv by lia.
    replace (_k - (_k - _i)) with _i by lia.
    reflexivity. }
Qed.

End Eq.
End IterDown.

(* -------------------------------------------------------------------------- *)

(* The tactic [wp_iter_down_body _j j s] should be used upon entry into
   the loop body. It introduces the index [_j] and its integer model [j]
   as well as the state [s]. *)

(* Prior to using this tactic, one can use [clear dependent] to clear any
   pre-existing variables by the same names. *)

Tactic Notation "wp_iter_down_body"
  simple_intropattern(_j) simple_intropattern(j) simple_intropattern(s) :=
  wp_body ? j s introducing: (fun _ => z_step; intros _j ?).

(* -------------------------------------------------------------------------- *)

(* An exitable loop, counting down. The loop can be broken via an early
   exit: the loop body receives two continuations [continue] and [break] and
   must invoke either [continue s] or [break s x]. An invocation of the loop
   body takes the form [body _j s continue break]. *)

Section XIterDown.
Context {S A : Type}.
Implicit Types s : S.
Open Scope uint63.

Section Body.
Variable body : ∀ {W}, int → S → (S → W) → (S → A → W) → W.

Fixpoint xiter_down_aux _i _k s
  (ACC : Acc (rilt _i) _k)
: S * outcome A :=
  IFC _k =? _i THEN λ _,
    (s, Continue)
  ELSE λ Hki,
    let _k' := _k - 1 in
    let continue s := xiter_down_aux _i _k' s
                        (Acc_inv ACC (rilt_n_minus_1 _k _i Hki)) in
    let break s x := (s, Break x) in
    body _k' s continue break.

End Body.

Definition xiter_down _i _k s body :=
  if _k ≤? _i then (s, Continue)
  else xiter_down_aux body _i _k s ltac:(tc).

End XIterDown.

(* A specification of [xiter_down_aux]. *)

Lemma wp_xiter_down_aux {S A}
  (body : ∀ {W}, int → S → (S → W) → (S → A → W) → W) :
  ∀IntU _i i ,
  ∀IntU _k k ,
  i ≤ k →
  ∀ ACC,
  XITER_Z i k Down
    (λ j _ s continue break Q, ∀ _j, isInt _j j → wp (body _j s continue break) Q)
    (λ s Q, wp (xiter_down_aux (@body) _i _k s ACC) Q).
Proof.
  intros _i i ? ?.
  by well-founded induction on _k along (rilt _i).
  intros. XITER. expand_ITER in IH.
  destruct ACC; simpl.
  wp_if; z.
  (* Case [k = i]. *)
  { wp_ret. }
  (* Case [k ≠ i]. *)
  { wp_apply Hbody; intros.
    (* Normal continuation. *)
    + wp_op IH introducing: (s' & out). eauto.
    (* Exit continuation. *)
    + wp_ret. eauto. }
Qed.

(* A specification of [xiter_down]. *)

Lemma wp_xiter_down {S A}
  (body : ∀ {W}, int → S → (S → W) → (S → A → W) → W) :
  ∀IntU _i i ,
  ∀IntU _k k ,
  XITER_Z i k Down
    (λ j _ s continue break Q, ∀ _j, isInt _j j → wp (body _j s continue break) Q)
    (λ s Q, wp (xiter_down _i _k s (@body)) Q).
Proof.
  intros. XITER. unfold xiter_down.
  wp_if; z.
  (* Case [k ≤ i]. *)
  { wp_ret. }
  (* Case [i < k]. *)
  { wp_op wp_xiter_down_aux.
    clear dependent s. wp_intro (s & out).
    eauto. }
Qed.

(* The tactic [wp_xiter_down_body _j j s] should be used upon entry into
   the loop body. It introduces the index [_j] and its integer model [j]
   as well as the state [s]. *)

(* Prior to using this tactic, one can use [clear dependent] to clear any
   pre-existing variables by the same names. *)

Tactic Notation "wp_xiter_down_body"
  simple_intropattern(_j) simple_intropattern(j) simple_intropattern(s) :=
  wp_body ? j s ?????? introducing: (fun _ => z_step; intros _j ?).

(* -------------------------------------------------------------------------- *)

(* A simplified exitable loop with a state of type [unit]. *)

(* The calling convention of the body is [body _i continue break]. *)

Section UXIterDown.
Context {A : Type}.
Open Scope uint63.

Section Body.
Variable body : ∀ {W}, int → (unit → W) → (A → W) → W.

Fixpoint uxiter_down_aux _i _k (ACC : Acc (rilt _i) _k) : outcome A :=
  IFC _k =? _i THEN λ _,
    Continue
  ELSE λ Hki,
    let _k' := _k - 1 in
    let continue '() := uxiter_down_aux _i _k'
                         (Acc_inv ACC (rilt_n_minus_1 _k _i Hki)) in
    let break x := Break x in
    body _k' continue break.

End Body.

Definition uxiter_down _i _k
  (body : ∀ {W}, int → (unit → W) → (A → W) → W) :=
  if _k ≤? _i then Continue
  else uxiter_down_aux (@body) _i _k ltac:(tc).

End UXIterDown.

(* A specification of [uxiter_down_aux]. *)

Lemma wp_uxiter_down_aux {A}
  (body : ∀ {W}, int → (unit → W) → (A → W) → W) :
  ∀IntU _i i ,
  ∀IntU _k k ,
  i ≤ k →
  ∀ ACC,
  UXITER_Z i k Down
    (λ j _ continue break Q, ∀ _j, isInt _j j → wp (body _j continue break) Q)
    (λ Q, wp (uxiter_down_aux (@body) _i _k ACC) Q).
Proof.
  intros _i i ? ?.
  by well-founded induction on _k along (rilt _i).
  intros. UXITER. expand_ITER in IH.
  destruct ACC; simpl.
  wp_if.
  (* Case [k = i]. *)
  { wp_ret. }
  (* Case [k ≠ i]. *)
  { wp_apply Hbody; intros.
    (* Normal continuation. *)
    + wp_op IH introducing: out. eauto.
    (* Exit continuation. *)
    + wp_ret. eauto. }
Qed.

(* A specification of [uxiter_down]. *)

Lemma wp_uxiter_down {A}
  (body : ∀ {W}, int → (unit → W) → (A → W) → W) :
  ∀IntU _i i ,
  ∀IntU _k k ,
  UXITER_Z i k Down
    (λ j _ continue break Q, ∀ _j, isInt _j j → wp (body _j continue break) Q)
    (λ Q, wp (uxiter_down _i _k (@body)) Q).
Proof.
  intros. UXITER. unfold uxiter_down.
  wp_if; z.
  (* Case [k ≤ i]. *)
  { wp_ret. }
  (* Case [i < k]. *)
  { wp_op wp_uxiter_down_aux; wp_intro out.
    eauto. }
Qed.

(* The tactic [wp_uxiter_down_body _j j] should be used upon entry into
   the loop body. It introduces the index [_j] and its integer model [j]. *)

(* Prior to using this tactic, one can use [clear dependent] to clear any
   pre-existing variables by the same names. *)

Tactic Notation "wp_uxiter_down_body"
  simple_intropattern(_j) simple_intropattern(j) :=
  wp_body ? j ?????? introducing: (fun _ => z_step; intros _j ?).

(* -------------------------------------------------------------------------- *)

(* A loop, counting up from [i] to [k], using machine integers. *)

(* Our intervals are semi-open on the right end: [i] is included,
   [k] is excluded. *)

(* [iter_up _i _k s body] applies the loop body [body] to every
   machine integer from [_i], included, up to [_k], excluded. A state
   of type [S] is carried, whose initial value is [s]. *)

Section IterUp.
Context {S : Type}.
Implicit Types s : S.
Open Scope uint63.

Section Body.
Variable body : int → S → S.

(* We define [iter_up_aux] by well-founded recursion over a proof of
   accessibility of the index [_i]. In the first branch, the fact that
   [_i <? _k] is true is needed in order to prove that [_i + 1] is
   less than [_i], a fact which itself is required by the termination
   argument. *)

Fixpoint iter_up_aux _i _k s (ACC : Acc igt _i) :=
  IFC _i <? _k THEN λ Hik,
    do s ← body _i s ;
    iter_up_aux (_i + 1) _k s
                (Acc_inv ACC (igt_n_plus_1 _i _k Hik))
  ELSE λ _,
    s.

End Body.

Notation iter_up_aux__ body _i _k s :=
  (iter_up_aux body _i _k s (Acc_igt _i)).

Definition iter_up _i _k s body :=
  iter_up_aux body _i _k s ltac:(tc).

(* A specification of [iter_up]. *)

Lemma wp_iter_up (body : int → S → S) :
  ∀IntU _i i ,
  ∀IntU _k k ,
  ITER_Z i k Up
    (λ j s Q, ∀ _j, isInt _j j → wp (body _j s) Q)
    (λ s Q, wp (iter_up _i _k s body) Q).
Proof.
  (* Transform this into a statement about [iter_up_aux]. *)
  unfold iter_up.
  intro _i. generalize (Acc_igt _i); intro ACC.
  (* Now prove it. *)
  by dependent induction on _i ACC.
  intros. ITER. expand_ITER in IH. simpl.
  wp_if.
  (* Case [i < k]. *)
  { wp_op Hbody shadowing: s.
    wp_op IH shadowing: s.
    wp_ret. }
  (* Case [¬ i < k]. *)
  { wp_ret. }
Qed.

(* -------------------------------------------------------------------------- *)

(* A "static" variant of [iter_up], where the difference [k - i] is
   statically known and is represented by a natural number [n]. *)

Section Body.
Variable body : int → S → S.

Fixpoint static_iter_up_aux _i s (n : nat) :=
  match n with
  | O =>
      s
  | Succ n =>
      do s ← body _i s ;
      do _i ← _i + 1 ;
      static_iter_up_aux _i s n
  end.

End Body.

(* Specialize [static_iter_up] for [N]. *)

Definition iter_up_N _i s body :=
  Eval compute -[bind] in static_iter_up_aux body _i s N.

(* Print iter_up_N. *)

(* -------------------------------------------------------------------------- *)

(* An unrolled variant of [iter_up]. *)

Section Body.
Variable body : int → S → S.

Fixpoint iter_up_unrolled_aux _i _n s (ACC : Acc ilt _n) :=
  IFC _n <? Ni THEN λ _,
    iter_up _i (_i + _n) s body
  ELSE λ Hn,
    do s ← iter_up_N _i s body ;
    do _i ← _i + Ni ;
    let _n := _n - Ni in
    iter_up_unrolled_aux _i _n s (Acc_inv ACC (ilt_n_minus_N Hn)).

End Body.

Definition iter_up_unrolled _i _k s body :=
  if _k ≤? _i then s
  else iter_up_unrolled_aux body _i (_k - _i) s ltac:(tc).

(* -------------------------------------------------------------------------- *)

(* An unrolled loop is equal to an ordinary loop. *)

Section Eq.
Variable body : int → S → S.
Open Scope uint63.
Local Opaque Acc_ilt Acc_igt.
Local Opaque bind.

(* [iter_up_aux] satisfies its fixed point equation. *)

Lemma iter_up_aux_eq _i ACC : ∀ _k s,
  iter_up_aux body _i _k s ACC =
  if _i <? _k then
    do s ← body _i s ;
    iter_up_aux__ body (_i + 1) _k s
  else
    s.
Proof.
  by dependent induction on _i ACC. intros _i. intros. simpl.
  eapply IFC_if; [ intro | reflexivity ].
  eapply bind_bind_eq; [ reflexivity | intro ]. (* optional *)
  setoid_rewrite IH; tc.
Qed.

(* [static_iter_up_aux _i s n] is equivalent to
   an ordinary loop over the interval [i, i + n). *)

(* In contrast with [static_iter_down_aux_eq], where we require
   just [unsigned (Z.of_nat n)], here, we must require
   [unsigned (to_Z _i + Z.of_nat n)]. This asymmetry appears because
   [iter_down] uses an equality test [=?] whereas [iter_up] uses
   a strict ordering test [<?]. *)

Lemma static_iter_up_aux_eq n : ∀ _i s,
  unsigned (to_Z _i + Z.of_nat n) →
  static_iter_up_aux body _i s n =
  iter_up_aux__ body _i (_i + of_nat n) s.
Proof.
  induction n as [| n ]; intros; simpl static_iter_up_aux.
  { rewrite iter_up_aux_eq. resolve. reflexivity. }
  { unfold bind at 2.
    setoid_rewrite IHn; [ clear IHn | lia ].
    rewrite iter_up_aux_eq. resolve.
    replace (_i + of_nat (Succ n)) with
            (_i + 1 + of_nat n) by lia.
    reflexivity. }
Qed.

(* [iter_up_unrolled_aux] satisfies its fixed point equation. *)

Lemma iter_up_unrolled_aux_eq _n ACC : ∀ _i s,
  unsigned (to_Z _i + to_Z _n) →
  iter_up_unrolled_aux body _i _n s ACC =
  if _n <? Ni then
    iter_up _i (_i + _n) s body
  else
    do s ← iter_up_aux__ body _i (_i + Ni) s ;
    do _i ← _i + Ni ;
    let _n := _n - Ni in
    iter_up_unrolled_aux body _i _n s ltac:(tc).
Proof.
  by dependent induction on _n ACC. intros _n. intros.
  simpl iter_up_unrolled_aux.
  eapply IFC_if; [ reflexivity | intro ].
  change (iter_up_N _i s body)
    with (static_iter_up_aux body _i s N).
  unfold Ni, N in *.
  rewrite static_iter_up_aux_eq by lia.
  unfold bind at 2 4.
  setoid_rewrite IH; tc.
Qed.

(* iterating first from [_a] up to [_b], then from [_b] up to [_c],
   is the same as iterating from [_a] up to [_c]. *)

Lemma iter_up_aux_glue _a : ∀ _b _c s ACC,
  (to_Z _a ≤ to_Z _b ≤ to_Z _c)%Z →
  (
    do s ← iter_up_aux body _a _b s ACC ;
    iter_up_aux__ body _b _c s
  )
  = iter_up_aux__ body _a _c s.
Proof.
  by well-founded induction on _a along igt.
  intros. rewrite iter_up_aux_eq.
  destruct (_a <? _b) eqn:?.
  (* Step case. *)
  { rewrite bind_bind.
    rewrite iter_up_aux_eq. resolve.
    eapply bind_bind_eq; [ reflexivity | intro ].
    eapply IH; tc. }
  (* Base case. *)
  { assert (_a = _b) as -> by lia.
    reflexivity. }
Qed.

(* [iter_up_unrolled_aux] is equivalent to [iter_up_aux]. *)

Lemma iter_up_unrolled_aux_equiv _n ACC : ∀ _i s,
  unsigned (to_Z _i + to_Z _n)%Z →
  iter_up_unrolled_aux body _i _n s ACC =
  iter_up_aux__ body _i (_i + _n) s.
Proof.
  by dependent induction on _n ACC. intros _n. intros.
  rewrite iter_up_unrolled_aux_eq by lia.
  destruct (_n <? Ni) eqn:?.
  (* Base case. *)
  { reflexivity. }
  (* Step case. *)
  { unfold bind at 2.
    setoid_rewrite IH; tc.
    replace (_i + Ni + (_n - Ni)) with (_i + _n) by lia.
    eapply iter_up_aux_glue. lia. }
Qed.

(* [iter_up_unrolled] is equivalent to [iter_up]. *)

Lemma iter_up_unrolled_eq _i _k s :
  iter_up_unrolled _i _k s body =
  iter_up _i _k s body.
Proof.
  unfold iter_up_unrolled, iter_up.
  destruct (_k ≤? _i) eqn:?.
  { rewrite iter_up_aux_eq. resolve. reflexivity. }
  { rewrite iter_up_unrolled_aux_equiv by lia.
    replace (_i + (_k - _i)) with _k by lia.
    reflexivity. }
Qed.

End Eq.
End IterUp.

(* -------------------------------------------------------------------------- *)

(* The tactic [wp_iter_up_body _j j s] should be used upon entry into the
   loop body. It introduces the index [_j] and its integer model [j] as well
   as the state [s]. *)

(* Prior to using this tactic, one can use [clear dependent] to clear any
   pre-existing variables by the same names. *)

Tactic Notation "wp_iter_up_body"
  simple_intropattern(_j) simple_intropattern(j) simple_intropattern(s) :=
  wp_body j ? s introducing: (fun _ => z_step; intros _j ?).

(* -------------------------------------------------------------------------- *)

(* An exitable loop, counting up from [i] to [k]. The loop can be broken
   via an early exit: the loop body receives two continuations [continue]
   and [break] and must invoke either [continue s] or [break s x]. An
   invocation of the loop body takes the form [body _i s continue break]. *)

Section XiterUp.
Context {S A : Type}.
Implicit Types s : S.
Open Scope uint63.

Section Body.
Variable body : ∀ {W}, int → S → (S → W) → (S → A → W) → W.

Fixpoint xiter_up_aux _i _k s (ACC : Acc igt _i) : S * outcome A :=
  IFC _i <? _k THEN λ Hik,
    let continue s := xiter_up_aux (_i + 1) _k s
                        (Acc_inv ACC (igt_n_plus_1 _i _k Hik)) in
    let break s x := (s, Break x) in
    body _i s continue break
  ELSE λ _,
    (s, Continue).

End Body.

Definition xiter_up _i _k s body :=
  xiter_up_aux body _i _k s ltac:(tc).

End XiterUp.

(* We do not establish a proof irrelevance / fixed point lemma here,
   because that would be difficult: we would need to either use the
   axiom of functional extensionality or make a hypothesis about
   [body]. The difficulty is that the recursive call appears nested
   inside the continuation [continue], that is, under a lambda. *)

(* Instead, we proceed directly to the proof of Hoare-style reasoning
   rules for [xiter_up_aux] and [xiter_up]. *)

(* The specification of [xiter_up_aux]. *)

Lemma wp_xiter_up_aux {S A}
  (body : ∀ {W}, int → S → (S → W) → (S → A → W) → W) :
  ∀IntU _i i ,
  ∀IntU _k k ,
  ∀ ACC,
  XITER_Z i k Up
    (λ j _ s continue break Q, ∀ _j, isInt _j j → wp (body _j s continue break) Q)
    (λ s Q, wp (xiter_up_aux (@body) _i _k s ACC) Q).
Proof.
  by well-founded induction on _i along igt.
  intros. XITER. expand_ITER in IH.
  destruct ACC; simpl.
  wp_if; z.
  (* Case [i < k]. *)
  { wp_apply Hbody; intros.
    (* Normal continuation. *)
    + wp_op IH introducing: (s' & out). eauto.
    (* Exit continuation. *)
    + wp_ret. eauto. }
  (* Case [k ≤ i]. *)
  { wp_ret. }
Qed.

(* The specification of [xiter_up]. *)

Lemma wp_xiter_up {S A}
  (body : ∀ {W}, int → S → (S → W) → (S → A → W) → W) :
  ∀IntU _i i ,
  ∀IntU _k k ,
  XITER_Z i k Up
    (λ j _ s continue break Q, ∀ _j, isInt _j j → wp (body _j s continue break) Q)
    (λ s Q, wp (xiter_up _i _k s (@body)) Q).
Proof.
  unfold xiter_up. eauto using wp_xiter_up_aux.
Qed.

Tactic Notation "wp_xiter_up_body"
  simple_intropattern(_j) simple_intropattern(j) simple_intropattern(s) :=
  wp_body j ? s ?????? introducing: (fun _ => z_step; intros _j ?).

(* -------------------------------------------------------------------------- *)

(* A simplified exitable loop with a state of type [unit]. *)

(* The calling convention of the body is [body _i continue break]. *)

Section UXIterUp.
Context {A : Type}.
Open Scope uint63.

Section Body.
Variable body : ∀ {W}, int → (unit → W) → (A → W) → W.

Fixpoint uxiter_up_aux _i _k (ACC : Acc igt _i) : outcome A :=
  IFC _i <? _k THEN λ Hik,
    let continue '() := uxiter_up_aux (_i + 1) _k
                         (Acc_inv ACC (igt_n_plus_1 _i _k Hik)) in
    let break x := Break x in
    body _i continue break
  ELSE λ _,
    Continue.

End Body.

Definition uxiter_up _i _k body :=
  uxiter_up_aux body _i _k ltac:(tc).

End UXIterUp.

(* The specification of [uxiter_up_aux]. *)

Lemma wp_uxiter_up_aux {A}
  (body : ∀ {W}, int → (unit → W) → (A → W) → W) :
  ∀IntU _i i ,
  ∀IntU _k k ,
  ∀ ACC,
  UXITER_Z i k Up
    (λ j _ continue break Q, ∀ _j, isInt _j j → wp (body _j continue break) Q)
    (λ Q, wp (uxiter_up_aux (@body) _i _k ACC) Q).
Proof.
  by well-founded induction on _i along igt.
  intros. UXITER. expand_ITER in IH.
  destruct ACC; simpl.
  wp_if; z.
  (* Case [i < k]. *)
  { wp_apply Hbody; intros.
    (* Normal continuation. *)
    + wp_op IH introducing: out. eauto.
    (* Exit continuation. *)
    + wp_ret. eauto. }
  (* Case [k ≤ i]. *)
  { wp_ret. }
Qed.

(* The specification of [uxiter_up]. *)

Lemma wp_uxiter_up {A} (body : ∀ {W}, int → (unit → W) → (A → W) → W) :
  ∀IntU _i i ,
  ∀IntU _k k ,
  UXITER_Z i k Up
    (λ j _ continue break Q, ∀ _j, isInt _j j → wp (body _j continue break) Q)
    (λ Q, wp (uxiter_up _i _k (@body)) Q).
Proof.
  unfold uxiter_up. eauto using wp_uxiter_up_aux.
Qed.

(* The tactic [wp_uxiter_up_body _j j] should be used upon entry into the
   loop body. It introduces the index [_j] and its integer model [j]. *)

(* Prior to using this tactic, one can use [clear dependent] to clear any
   pre-existing variables by the same names. *)

Tactic Notation "wp_uxiter_up_body"
  simple_intropattern(_j) simple_intropattern(j) :=
  wp_body j ? ?????? introducing: (fun _ => z_step; intros _j ?).
