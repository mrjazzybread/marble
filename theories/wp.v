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

From stdpp Require Import base.
From marble Require Import equations tactics bool.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

(* This file defines a trivial Hoare logic for (pure) computations. *)

(* The main judgement is [wp a Q]. It means that the computation [a]
   has the postcondition [Q]: that is, the result of [a] satisfies
   the property [Q]. *)

(* Naturally, Rocq does not distinguish between a computation and its
   result: they are considered equal. Thus, the definition of [wp a Q]
   is just [Q a]. Nevertheless, the judgement [wp] is useful: applying
   its reasoning rules lets us reason step by step about the behavior
   of a program. *)

(* The notation [do x ← a; b] is useful for a similar reason. It is
   really synonymous with native [let x := a in b]. Nevertheless it
   is more robust than a [let] binding; [let] bindings are unfolded
   by many tactics, whereas [do] is not unfolded. *)

(* -------------------------------------------------------------------------- *)

(* [exist x pf] constructs an inhabitant of a subset type. *)

(* Beware: potential confusion with the function [array.exist]. *)

Notation exist x pf :=
  (Specif.exist _ x pf).

(* The projection [proj1_sig e] is also written just [`e]. However,
   this notation appears to be fragile; in my experience, it works
   when [e] is just a variable, but is not accepted by Rocq when [e]
   is a complex term, even with parentheses. *)

(* -------------------------------------------------------------------------- *)

(* As in OCaml, [@@] is a function application operator. *)

(* [iter ... @@ λ _i s, ...] is a nice way of writing a loop. *)

Notation "f '@@' x" := (f x) (at level 61, only parsing).

(* -------------------------------------------------------------------------- *)

(* The [bind] operation of the identity monad and its [do] notation. *)

Definition bind {A B} (a : A) (b : A → B) : B :=
  let x := a in b x.

Global Notation "'do' x ← y ; z" := (bind y (λ x : _, z))
  (at level 20, x pattern, y at level 100, z at level 200).

(* Some equational properties of [bind]. *)

(* Equational reasoning is normally not used as part of Hoare logic,
   but can occasionally be useful. *)

(* [bind_bind] is an associative law. *)

Lemma bind_bind {A B C} (e : A) (f : A → B) (g : B → C) :
  bind (bind e f) g =
  bind e (λ x, bind (f x) g).
Proof.
  reflexivity.
Qed.

(* [bind_if] duplicates the continuation [k]. In situations where [k]
   is very small, this can be convenient, as it removes the need to
   provide a specification of the join point. *)

Lemma bind_if {A B} (c : bool) (e1 e2 : A) (k : A → B) :
  bind (if c then e1 else e2) k =
  if c then bind e1 k else bind e2 k.
Proof.
  destruct c; reflexivity.
Qed.

(* This lemma can be used to prove that a [bind] construct whose result
   type is a subset type { a : A | Q a } is equal (up to a projection)
   to a [bind] construct whose result type is just A. *)

Lemma bind_eq_dep {A B} {Q : B → Prop}
  (a1 : A) (b1 : A → sig Q)
  (a2 : A) (b2 : A → B) :
  a1 = a2 →
  (∀ a, proj1_sig (b1 a) = b2 a) →
  proj1_sig (bind a1 b1) = bind a2 b2.
Proof.
  intros. subst. eauto.
Qed.

Lemma bind_eq_dep_dep {A B} {Q' : A → Prop} {Q : B → Prop}
  (a1 : sig Q') (b1 : sig Q' → sig Q)
  (a2 : A) (b2 : A → B) :
  (`a1 = a2) →
  (∀ a pf, proj1_sig (b1 (Specif.exist _ a pf)) = b2 a) →
  proj1_sig (bind a1 b1) = bind a2 b2.
Proof.
  intros. destruct a1. subst. eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* [wp] has type [A → WP A]. *)

Definition WP A :=
  (A → Prop) → Prop.

Definition wp {A} (a : A) (Q : A → Prop) :=
  Q a.

(* This paraphrase of the definition can occasionally be useful. It is not
   a reasoning rule of Hoare logic; it is a way of entering or escaping
   Hoare logic. *)

Lemma wp_iff {A} (a : A) (Q : A → Prop) :
  wp a Q ↔
  Q a.
Proof.
  eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Reasoning rules. *)

(* The return rule. *)

Lemma wp_ret {A} (a : A) (Q : A → Prop) :
  Q a →
  wp a Q.
Proof.
  eauto.
Qed.

(* The bind rule. *)

(* [wp_bind] is a binary formulation of this rule. The assertion [P]
   serves as the postcondition of [a] and as the precondition of [b]. *)

Lemma wp_bind {A B} (a : A) (b : A → B) (P : A → Prop) (Q : B → Prop) :
  wp a P →
  (∀ x, P x → wp (b x) Q) →
  wp (bind a b) Q.
Proof.
  eauto.
Qed.

(* [wp_bind_unary] is a unary formulation of this rule. There is no need
   to provide an assertion [P]: the proposition [λ x, wp (b x) Q] is used
   as the postcondition of [a]. This can be handy, but can also lead to
   a duplication of the proposition [λ x, wp (b x) Q], requiring [b] to
   be verified several times. It should typically NOT be used when [a]
   is a conditional expression (with multiple exit points), unless one
   is willing to verify [b] several times. *)

Lemma wp_bind_unary {A B} (a : A) (b : A → B) (Q : B → Prop) :
  wp a (λ x, wp (b x) Q) →
  wp (bind a b) Q.
Proof.
  eauto.
Qed.

(* [wp_bind_eq] is a formulation where one does not reason in Hoare
   style about the expression [a]. Instead one considers that the
   postcondition of [a] is [λ x, x = a]. This can be useful when one
   wishes to view [a] as a "pure" expression. *)

Lemma wp_bind_eq {A B} (a : A) (b : A → B) (Q : B → Prop) :
  (∀ x, x = a → wp (b x) Q) →
  wp (bind a b) Q.
Proof.
  eauto.
Qed.

(* Reasoning rules for conditional expressions. *)

(* [wp_if] does not make the equations [b = true] and [b = false]
   accessible to the user while verifying [e1] and [e2]. If desired,
   one could make them accessible; but they are usually not useful,
   because the judgement [isBool b P1 P2] does the work of turning
   these equations into more palatable propositions. *)

(* [wp_IF] does make these equations accessible to the user because
   they are typically useful. Indeed, we use [IF/THEN/ELSE] when we
   wish to define a recursive function whose termination argument
   relies on the equations [b = true] and [b = false]. If one reasons
   about such a function using well-founded recursion then one must
   repeat the termination argument; then these equations are needed. *)

(* [wp_IFC] is analagous to [wp_IF] but allows the branches [e1] and
   [e2] to be parameterized with a proof of [b = true] or [b = false]. *)

Lemma wp_if {A} (b : bool) (e1 e2 : A) (Q : A → Prop) {P1 P2 : Prop} :
  isBool b P1 P2 →
  (P1 → wp e1 Q) →
  (P2 → wp e2 Q) →
  wp (if b then e1 else e2) Q.
Proof.
  unfold isBool. intros. destruct b; eauto.
Qed.

Lemma wp_IF {A} (b : bool) (e1 e2 : A) (Q : A → Prop) {P1 P2 : Prop} :
  isBool b P1 P2 →
  (b =  true → P1 → wp e1 Q) →
  (b = false → P2 → wp e2 Q) →
  wp (IF b THEN e1 ELSE e2) Q.
Proof.
  unfold isBool. intros. destruct b; eauto.
Qed.

Lemma wp_IFC {A} (b : bool) e1 e2 (Q : A → Prop) {P1 P2 : Prop} :
  isBool b P1 P2 →
  (∀ pf1 : b =  true, P1 → wp (e1 pf1) Q) →
  (∀ pf2 : b = false, P2 → wp (e2 pf2) Q) →
  wp (IFC b THEN e1 ELSE e2) Q.
Proof.
  unfold isBool. intros. destruct b; eauto.
Qed.

(* The consequence rule. *)

Lemma wp_conseq {A} (a : A) (Q Q' : A → Prop) :
  wp a Q →
  (∀ x, Q x → Q' x) →
  wp a Q'.
Proof.
  unfold wp. eauto.
Qed.

(* This rule is occasionally useful. *)

Lemma wp_exist {A} {P : A → Prop} (e : A) (pf : P e) (Q : sig P → Prop) :
  wp e (λ x, ∀ pf, Q (exist x pf)) →
  wp (exist e pf) Q.
Proof.
  rewrite !wp_iff. eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Sometimes we write code in continuation-passing style (CPS), that is, code
   that expects a continuation [k : A → R] as an argument and returns a value
   [a : A] via the function application [k a]. It is also possible to abort by
   returning a reply [r : R] directly, without invoking [k]. *)

(* [CPS R A] is the type of a computation whose result type is [A] and whose
   reply type is [R]. That is, [A] is the type of results (the domain of the
   continuation) whereas [R] is the type of replies (the codomain of the
   continuation). *)

Definition CPS R A :=
  (A → R) → R.

(* To help specify and verify code in CPS style, we define the judgement
   [wp_cps e Q ψ]. The ordinary postcondition [Q] describes results; the
   exceptional postcondition [ψ] describes replies. *)

(* The definition of [wp_cps] (below) requires the call [e k] to establish an
   abstract postcondition [ψ'], and it is given two means of establishing [ψ']:
   - by applying [k] to a result [a] that satisfies [Q], or
   - by aborting with a reply [r] that satisfies [ψ]. *)

Definition wp_cps {R A} (e : CPS R A) (Q : A → Prop) (ψ : R → Prop) :=
  ∀ (k : A → R) (ψ' : R → Prop),
  (∀ a, Q a → wp (k a) ψ') →
  (∀ r, ψ r → wp r ψ') →
  wp (e k) ψ'.

Ltac wp_cps_intro :=
  let k := fresh "k" in
  let ψ' := fresh "ψ'" in
  let Hk := fresh "Hk" in
  let Habort := fresh "Habort" in
  intros k ψ' Hk Habort.

(* This judgement enjoys the following reasoning rule. *)

(* Returning a result [a]. *)

Lemma wp_cps_ret {R A} (a : A) (Q : A → Prop) (ψ : R → Prop) :
  Q a →
  wp_cps (λ k, k a) Q ψ.
Proof.
  unfold wp_cps, wp. eauto.
Qed.

(* Aborting with a reply [r]. *)

Lemma wp_cps_abort {R A} (r : R) (Q : A → Prop) (ψ : R → Prop) :
  ψ r →
  wp_cps (λ k, r) Q ψ.
Proof.
  unfold wp_cps, wp. eauto.
Qed.

(* The consequence rule. *)

Lemma wp_cps_conseq {R A} (e : CPS R A) Q Q' ψ ψ':
  wp_cps e Q ψ →
  (∀ a, Q a → Q' a) →
  (∀ r, ψ r → ψ' r) →
  wp_cps e Q' ψ'.
Proof.
  unfold wp_cps. eauto 6.
Qed.

(* The bind rule. *)

Lemma wp_cps_bind {R A B} (e1 : CPS R A) (e2 : A → CPS R B) P Q ψ :
  wp_cps e1 P ψ →
  (∀ a, P a → wp_cps (e2 a) Q ψ) →
  wp_cps (λ k, e1 (λ a, e2 a k)) Q ψ.
Proof.
  unfold wp_cps. eauto 6.
Qed.

(* The functional extensionality rule. *)

Lemma wp_cps_ext {R A} (e e' : CPS R A) Q ψ :
  wp_cps e Q ψ →
  (∀ k, e k = e' k) →
  wp_cps e' Q ψ.
Proof.
  intros He Heq. unfold wp_cps. intros. rewrite <- Heq. eauto.
Qed.

(* A special case of the previous rule. *)

Lemma wp_cps_eta {R A} (e : CPS R A) Q ψ :
  wp_cps e Q ψ →
  wp_cps (λ a, e a) Q ψ.
Proof.
  eauto.
Qed.

(* A rule for switching into and out of CPS style. *)

(* Applying the CPS-style computation [e] to the identity continuation
   lets one switch from direct style to CPS style and back. If [e]
   returns a result [a] to its continuation then [a] becomes the final
   result of the computation. If [e] aborts with a reply [r] then [r]
   becomes the final result of the computation. Thus types [A] and [R]
   must coincide, and [e] must admit [Q] as its normal postcondition
   and as its exceptional postcondition. *)

(* This lemma is a special case of the next one. *)

Lemma wp_cps_id {A} (e : CPS A A) Q :
  wp_cps e Q Q →
  wp (e (λ a, a)) Q.
Proof.
  unfold wp_cps. eauto.
Qed.

(* Applying the CPS-style computation [e] to a non-trivial continuation
   is equivalent to sequencing a CPS-style computation and a direct-style
   computation. *)

Lemma wp_cps_enter {R A} (e : CPS R A) (k : A → R) Q ψ :
  wp_cps e Q ψ →
  (∀ a, Q a → wp (k a) ψ) →
  wp (e k) ψ.
Proof.
  unfold wp_cps. eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* When the type of a program is a subset type { a : A | Q a }, writing a
   postcondition becomes difficult, as it is necessary to deconstruct [a],
   or to wrap it in the projection [proj1_sig]. *)

(* To remove this difficulty, we offer a new judgement, [wpd a Q]. *)

Definition wpd {A} {Q'} (a : sig Q') (Q : A → Prop) :=
  Q (`a).

(* Through rewriting (from left to right), this lemma transforms a [wpd]
   judgement into a [wp] judgement. *)

Lemma wpd_wp {A} {Q'} (a : sig Q') (Q : A → Prop) :
  wpd a Q ↔ wp a (λ a, Q (`a)).
Proof.
  tauto.
Qed.

(* Conversely, if the goal is a [wp] judgement, then, by applying the
   following lemma, it can be turned back into a [wp] judgement . *)

Lemma wp_wpd {A} {Q' : A → Prop} (a : sig Q') (Q1 : A → Prop) (Q2 : sig Q' → Prop) :
  wpd a Q1 →
  (∀ a, Q1 (`a) → Q2 a) →
  wp a Q2.
Proof.
  unfold wp, wpd. eauto.
Qed.

(* The return rule. *)

Lemma wpd_ret {A} {Q'} (a : sig Q') (Q : A → Prop) :
  Q (`a) →
  wpd a Q.
Proof.
  eauto.
Qed.

(* A stronger version of the return rule, where [Q'] can be exploited. *)

Lemma wpd_ret' {A} {Q'} (a : sig Q') (Q : A → Prop) :
  (Q' (`a) → Q (`a)) →
  wpd a Q.
Proof.
  intros h. unfold wpd. eapply h.
  destruct a. simpl. tauto.
Qed.

(* The bind rule (with a [wp] judgement on the left-hand side). *)

Lemma wpd_bind {A B} {Q'} a (b : A → sig Q') P (Q : B → Prop) :
  wp a P →
  (∀ x, P x → wpd (b x) Q) →
  wpd (bind a b) Q.
Proof.
  eauto.
Qed.

(* The bind rule (with a [wpd] judgement on the left-hand side). *)

Lemma wpd_wpd_bind {A B} {Q1 Q2} (a : sig Q1) (b : sig Q1 → sig Q2)
  (P : A → Prop) (Q : B → Prop) :
  wpd a P →
  (∀ x pf, P x → wpd (b ((exist x pf))) Q) →
  wpd (bind a b) Q.
Proof.
  destruct a. eauto.
Qed.

Lemma wpd_wpd_bind_unary {A B} {Q1 : A → Prop} {Q2}
  (a : sig Q1) (b : sig Q1 → sig Q2) (Q : B → Prop) :
  wpd a (λ x, ∀ pf, wpd (b ((exist x pf))) Q) →
  wpd (bind a b) Q.
Proof.
  destruct a. eauto.
Qed.

(* Reasoning rules for conditionals. *)

Lemma wpd_if {A} {Q'} b (e1 e2 : sig Q') (Q : A → Prop) {P1 P2 : Prop} :
  isBool b P1 P2 →
  (P1 → wpd e1 Q) →
  (P2 → wpd e2 Q) →
  wpd (if b then e1 else e2) Q.
Proof.
  unfold isBool. intros. destruct b; eauto.
Qed.

Lemma wpd_IFC {A} {Q'} b
  (e1 : b = true → sig Q')
  (e2 : b = false → sig Q')
  (Q : A → Prop) {P1 P2 : Prop} :
  isBool b P1 P2 →
  (∀ pf1 : b =  true, P1 → wpd (e1 pf1) Q) →
  (∀ pf2 : b = false, P2 → wpd (e2 pf2) Q) →
  wpd (IFC b THEN e1 ELSE e2) Q.
Proof.
  unfold isBool. intros. destruct b; eauto.
Qed.

(* The consequence rule. *)

Lemma wpd_conseq {A} {Q'} (a : sig Q') (Q1 Q2 : A → Prop) :
  wpd a Q1 →
  (∀ x, Q1 x → Q2 x) →
  wpd a Q2.
Proof.
  unfold wpd. eauto.
Qed.

(* This rule is occasionally useful. *)

Lemma wpd_exist {A} {P : A → Prop} (e : A) (pf : P e) (Q : A → Prop) :
  wp e Q →
  wpd (exist e pf) Q.
Proof.
  unfold wp, wpd. simpl. eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* We make [wp] opaque, so as to discourage unfolding it. *)

Opaque wp.

(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)

(* Sometimes we wish to prove that two pieces of code are equal. *)

(* This is often not a good idea and not easy, but sometimes necessary
   in order to optimize a piece of code and prove that the optimized
   code is equal to the unoptimized code that has been verified. *)

(* Equality of two conditionals. *)

Lemma if_if_eq {B} (a0 a0' : bool) (b1 b2 b1' b2' : B) :
  a0 = a0' →
  (a0 = true  → b1 = b1') →
  (a0 = false → b2 = b2') →
  (if a0 then b1 else b2) = (if a0' then b1' else b2').
Proof.
  intros. subst a0'. destruct a0; eauto.
Qed.

(* For simplicity, for now, this lemma is limited to the case where
   the two conditionals have exactly the same condition. *)

Lemma IFC_IFC_eq {B} (a0 : bool)
  (b1 b1' : a0 = true →  B)
  (b2 b2' : a0 = false → B) :
  (∀ pf : a0 = true , b1 pf = b1' pf) →
  (∀ pf : a0 = false, b2 pf = b2' pf) →
  (IFC a0 THEN b1 ELSE b2) = (IFC a0 THEN b1' ELSE b2').
Proof.
  intros. destruct a0; eauto.
Qed.

(* Equality of sequences. *)

Lemma bind_bind_eq {A B} (a1 a2 : A) (k1 k2 : A → B) :
  a1 = a2 →
  (∀ a, k1 a = k2 a) →
  bind a1 k1 = bind a2 k2.
Proof.
  intros. unfold bind. congruence.
Qed.

(* Rewriting using [setoid_rewrite] inside [bind] is permitted. *)

Instance Proper_bind A B :
  Proper (eq ==> (pointwise_relation _ eq) ==> eq) (@bind A B).
Proof.
  repeat intro. unfold bind. congruence.
Qed.

(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)

(* Tactics. *)

(* The tactic [wp_ret_hook] attempts to prove the goal that remains after
   the lemma [wp_ret] has been applied. It is invoked by [wp_ret] below. *)

(* The default definition of this tactic is cheap. We expect users to
   redefine it if they need more expensive / aggressive simplification. *)

Ltac wp_ret_hook :=
  try solve [ subst; tc3 ].

(* Reasoning about a trivial computation (return). *)

Ltac wp_ret :=
  eapply wp_ret;
  wp_ret_hook.

(* Reasoning about a conditional construct. *)

(* The first subgoal, [isBool _ _ _], should be solved by [tc]. *)

(* Strangely enough, [simple eapply wp_if] can succeed when the goal is an
   [IF/THEN/ELSE] construct that contains an [if/then/else] construct
   nested inside it. (Rocq seems to exchange the conditionals.) By trying
   [simple eapply wp_IF] first, we seem to avoid this problem. *)

Ltac wp_if :=
  first [
    simple eapply wp_IF
  | simple eapply wp_IFC
  | simple eapply wp_if
  ]; [ tc | intros | intros ].

(* Reasoning about a [bind] construct whose left-hand side is pure. *)

Ltac wp_bind_eq :=
  eapply wp_bind_eq; intros ? ->.

(* To reason about a [bind] construct whose left-hand side is non-trivial,
   use [wp_op]. (See below.) *)

(* -------------------------------------------------------------------------- *)

(* The tactic [wp_intro_hook] simplifies a hypothesis that has just been
   introduced. It is invoked by [wp_intro] below. *)

(* The default definition of this tactic is cheap. We expect users to
   redefine it if they need more expensive / aggressive simplification. *)

Ltac wp_intro_hook Hx :=
  unpack in Hx.

(* -------------------------------------------------------------------------- *)

(* [wp_intro x] first introduces a variable [x] and a hypothesis [Hx], then
   simplifies this hypothesis by invoking [wp_intro_hook Hx]. It is
   typically used in the second subgoal of [wp_bind] and [wp_conseq]. *)

Tactic Notation "wp_intro" simple_intropattern(x) :=
  (* Eliminate beta redexes. (There is often one.) *)
  cbv beta;
  let Hx := fresh in
  intros x Hx;
  (* Perform simplification. *)
  wp_intro_hook Hx.

(* -------------------------------------------------------------------------- *)

(* [wp_shadow x] forgets everything about [x] before invoking [wp_intro x].
   Thus, the newly introduced [x] shadows the earlier [x]. *)

(* This tactic should be used when a new array is obtained by updating an
   existing array, or more generally, when a new mutable data structure is
   obtained by updating an existing mutable data structure [x]. This helps
   keep the goal readable and ensures that mutable data structures are used
   linearly. *)

Ltac wp_shadow x :=
  clear dependent x;
  wp_intro x.

(* -------------------------------------------------------------------------- *)

(* [wp_precondition_primary_hook] and [wp_precondition_secondary_hook] attempt
   to prove a precondition. These tactics do not fail: if they are unable to
   prove the goal, they leave it open. *)

(* These tactics are applied in two rounds: first, the primary hook is applied
   to all preconditions; then the secondary hook is applied to all remaining
   preconditions. The primary hook can instantiate metavariables (e.g., in
   goals of the form [isInt _i ?i]). This information can be exploited in the
   secondary hook, e.g., by applying rewriting tactics, such as [length] or
   [list], before attempting to solve a goal. *)

(* Ideally, these tactics should be cheap; otherwise, there is a risk of
   wasting time trying to solve goals that need human intervention anyway. On
   the other hand, they should not be too cheap: if a tactic fails to solve a
   goal then it may leave some metavariables uninstantiated, and in the next
   goal, these metavariables risk being instantiated in an incorrect manner.

   Indeed, one cannot prevent [eauto] from instantiating metavariables in the
   wrong way: if it recognizes that the goal is [0 ≤ ?j] and there is an
   assumption [0 ≤ i], then it will instantiate [j] with [i], even though this
   is possibly not desirable. *)

Ltac wp_precondition_primary_hook :=
  (* Attempt to solve the goal. *)
  tc3.

Ltac wp_precondition_secondary_hook :=
  (* 1. Rewrite the goal. *)
  (* Arithmetic simplification is cheap and can be useful in loops,
     e.g., when we have [inv j s] and the goal is [inv (j - 1 + 1) s]. *)
  (* [length] is more expensive but is also useful, e.g., when an
     arithmetic side condition involves applications of the [length]
     function. *)
  (* [app_assoc] is cheap and increases our chances of success. *)
  autorewrite with z clength app_assoc;
  (* 2. Attempt to solve the goal. *)
  tc3.

(* The tactic [wp_loop_precondition_hook] prepares a precondition before
   [wp_precondition_secondary_hook] is invoked. It is invoked only by
   [wp_apply ... with invariant: ...], that is, only when reasoning about a
   loop. *)

Ltac expand_ITER :=
  idtac. (* to be redefined in iteration.v *)

Ltac wp_loop_precondition_hook :=
  try solve [ prove_Proper ];
  expand_ITER.

(* The tactic [wp_loop_postcondition_hook] is invoked by [wp_apply ...
   with invariant: ...] in the last subgoal, where one reasons about
   the situation at the end of the loop. *)

Ltac wp_loop_postcondition_hook :=
  idtac. (* to be redefined in iteration.v *)

(* -------------------------------------------------------------------------- *)

(* [wp_apply lemma] applies the lemma [lemma], which is typically a
   reasoning rule for some operation [op], then attempts to solve its
   preconditions. The goal should have the form [wp (op ...) ?Q] where
   [?Q] is a metavariable. *)

Tactic Notation "wp_apply" uconstr(lemma) :=
  (* Apply the reasoning rule for this operation. *)
  simple eapply lemma;
  (* Attempt to solve the preconditions. Because the semi-colon in Ltac is
     left-associative, each tactic in the sequence below is applied to ALL
     preconditions before the next tactic in the sequence is applied. *)
  (* [tc3] can solve many preconditions cheaply, e.g., [isInt _ _]. This
     instantiates many metavariables, which (in the next round) allows
     [lia] to prove arithmetic side conditions. *)
  wp_precondition_primary_hook;
  (* This tactic is user-configurable. *)
  wp_precondition_secondary_hook.

(* [wp_apply lemma with invariant: I] is analogous to [wp_apply lemma],
   but specifies that the lemma [lemma] should be instantiated with
   [inv := I]. This is typically exploited to provide a loop invariant. *)

Tactic Notation "wp_apply" uconstr(lemma) "with" "invariant:" constr(I) :=
  simple eapply lemma with (inv := I);
  wp_loop_precondition_hook;
  wp_precondition_primary_hook;
  wp_precondition_secondary_hook.

(* -------------------------------------------------------------------------- *)

(* [wp_op lemma] applies either [wp_bind] or [wp_conseq], then applies
   the lemma [lemma] in the first subgoal and leaves the second subgoal
   untouched. *)

(* The goal should have the form [wp (op ...) Q] or
   [wp (do x ← op ... ; ...) Q]. *)

(* The first subgoal is changed by [wp_apply lemma] into an arbitrary
   number of subgoals (preconditions). *)

(* One may think that [wp_op lemma] should first try [wp_apply lemma],
   as this could succeed directly, without introducing an unnecessary
   application of the consequence rule. However, [wp_apply lemma] can
   also lead to a dead end: when [lemma] is a universally quantified
   statement, [wp_apply lemma] can instantiate the quantifiers in an
   incorrect way and create unsatisfiable goals. *)

Tactic Notation "wp_op" uconstr(lemma) :=
  first [ simple eapply wp_bind | simple eapply wp_conseq ];
    [ wp_apply lemma | ].

(* [wp_op lemma with invariant: I] is analogous to [wp_op lemma],
   but specifies that the lemma [lemma] should be instantiated with
   [inv := I]. This is typically exploited to provide a loop invariant. *)

Tactic Notation "wp_op" uconstr(lemma) "with" "invariant:" constr(I) :=
  first [ simple eapply wp_bind | simple eapply wp_conseq ];
    [ wp_apply lemma with invariant: I | wp_loop_postcondition_hook ].

(* In the last subgoal of [wp_op], one should typically use [wp_intro x] or
   [wp_shadow x]. The following tactics are abbreviations for these common
   practices. *)

Tactic Notation "wp_op" uconstr(lemma)
                "introducing:" simple_intropattern(x) :=
  wp_op lemma; last wp_intro x.

Tactic Notation "wp_op" uconstr(lemma)
                "shadowing:" simple_intropattern(x) :=
  wp_op lemma; last wp_shadow x.

(* -------------------------------------------------------------------------- *)

(* [wp_last H] renames the most recently introduced hypothesis [H]. *)

(* The tactics [wp_intro] and [wp_shadow] do not allow naming the
   hypotheses that they introduce. In case there is only one such
   hypothesis, [wp_last] allows renaming it after the fact. *)

Ltac wp_last H :=
  match goal with h: _ |- _ =>
    rename h into H
  end.

(* [wp_destruct_post p] destructs the most recently introduced
   hypothesis using the pattern [p]. *)

Tactic Notation "wp_destruct_post" simple_intropattern(p) :=
  match goal with h: _ |- _ =>
    destruct h as p
  end.
