From stdpp Require Import base.
From marble Require Import equations tactics bool.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

(* This file defines a trivial Hoare logic for (pure) computations. *)

(* The main judgement is [wp a Q]. It means that the computation [a]
   admits the postcondition [Q]: that is, the result of [a] satisfies
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

(* Rewriting using [setoid_rewrite] inside [bind] is permitted. *)

Instance Proper_bind A B :
  Proper (eq ==> (pointwise_relation _ eq) ==> eq) (@bind A B).
Proof.
  repeat intro. unfold bind. congruence.
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

(* -------------------------------------------------------------------------- *)

(* We make [wp] opaque, so as to discourage unfolding it. *)

Opaque wp.

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
  first [ simple eapply wp_IF | simple eapply wp_IFC | simple eapply wp_if ];
    [ tc | intros | intros ].

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

Ltac wp_loop_precondition_hook :=
  idtac.

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
    [ wp_apply lemma with invariant: I | ].

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
