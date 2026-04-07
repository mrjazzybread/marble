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

(* Two reasoning rules for conditional expressions. *)

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
  (b = true → P1 → wp e1 Q) →
  (b = false → P2 → wp e2 Q) →
  wp (IF b THEN e1 ELSE e2) Q.
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

(* Reasoning about a trivial computation (return). *)

Ltac wp_ret :=
  eapply wp_ret.

(* Reasoning about a conditional construct. *)

(* The fist subgoal, [isBool _ _ _], should be solved by [tc]. *)

Ltac wp_if :=
  first [ simple eapply wp_if | simple eapply wp_IF ];
    [ tc | intros | intros ].

(* Reasoning about a [bind] construct whose left-hand side is pure. *)

Ltac wp_bind_eq :=
  eapply wp_bind_eq; intros ? ->.

(* To reason about a [bind] construct whose left-hand side is non-trivial,
   use [wp_op]. (See below.) *)

(* -------------------------------------------------------------------------- *)

(* The hook [wp_intros_hook] simplifies a hypothesis that has just been
   introduced. It is invoked by [wp_intros] below. *)

(* The default definition of this hook is cheap. We expect users to redefine
   this hook if they need more expensive / aggressive simplification. *)

Ltac wp_intros_hook Hx :=
  unpack in Hx.

(* -------------------------------------------------------------------------- *)

(* [wp_intros x] first introduces a variable [x] and a hypothesis [Hx], then
   simplifies this hypothesis by invoking [wp_intro_hook Hx]. It is
   typically used in the second subgoal of [wp_bind] and [wp_conseq]. *)

Ltac wp_intros x :=
  (* Eliminate beta redexes. (There is often one.) *)
  cbv beta;
  let Hx := fresh in
  intros x Hx;
  (* Perform simplification. *)
  wp_intros_hook Hx.

(* -------------------------------------------------------------------------- *)

(* [wp_intros_shadow x] first invokes [wp_intros x'], where [x'] is fresh,
   then forgets everything about [x] and renames [x'] into [x]. It should be
   used when [x'] represents a new array that has been obtained by updating
   the array [x], or more generally, a new mutable data structure that has
   been obtained by updating the data structure [x]. This helps keep the
   goal readable and ensures mutable data structures are used linearly. *)

Ltac wp_intros_shadow x :=
  let x' := fresh in
  wp_intros x';
  clear dependent x;
  rename x' into x.

(* TODO it would be nice if [shadow] could somehow be a modifier
   that wraps an arbitrary tactic *)

(* -------------------------------------------------------------------------- *)

(* The hook [wp_precondition_hook] attempts to prove a precondition. It
   does not fail: if it is unable to prove the goal, it leaves it open. *)

Global Hint Rewrite
  <- List.app_assoc
: wp_precondition_hook.

Ltac wp_precondition_hook :=
  (* Arithmetic simplification is cheap and can be useful in loops,
     e.g., when we have [inv j s] and the goal is [inv (j - 1 + 1) s]. *)
  (* [length] is more expensive but is also useful, e.g., when an
     arithmetic side condition involves applications of the [length]
     function. *)
  autorewrite with z clength wp_precondition_hook;
  (* This can solve arithmetic side conditions. *)
  eauto 3 with lia.

(* -------------------------------------------------------------------------- *)

(* [wp_op_nude lemma] applies the lemma [lemma], which is typically a
   reasoning rule for some operation [op], then attempts to solve its
   preconditions. The goal should have the form [wp (op ...) ?Q] where
   [?Q] is a metavariable. *)

Ltac wp_op_nude lemma :=
  (* Apply the reasoning rule for this operation. *)
  simple eapply lemma;
  (* Attempt to solve the preconditions. Because the semi-colon in Ltac is
     left-associative, each tactic in the sequence below is applied to ALL
     preconditions before the next tactic in the sequence is applied. *)
  (* [tc3] can solve many preconditions cheaply, e.g., [isInt _ _]. This
     instantiates many metavariables, which (in the next round) allows
     [lia] to prove arithmetic side conditions. *)
  tc3;
  (* This tactic is user-configurable. *)
  wp_precondition_hook.

(* -------------------------------------------------------------------------- *)

(* [wp_op lemma x] applies either [wp_bind] or [wp_conseq], then applies
   the lemma [lemma] in the first subgoal and introduces the result under
   the name [x] in the second subgoal. The goal should have the form
   [wp (op ...) Q] or [wp (do x ← op ... ; ...) Q]. *)

(* [wp_op_shadow lemma x] is identical, except it uses
   [wp_intros_shadow x] instead of [wp_intros x]. *)

Ltac wp_op lemma x :=
  first [ simple eapply wp_bind | simple eapply wp_conseq ];
  [ wp_op_nude lemma | wp_intros x ].

Ltac wp_op_shadow lemma x :=
  first [ simple eapply wp_bind | simple eapply wp_conseq ];
  [ wp_op_nude lemma | wp_intros_shadow x ].

(* [wp_op_shadow_pair lemma x y] is an ad hoc variant of [wp_op_shadow] that
   should be used when the result of an operation is a pair (x, y). It is
   needed because [clear dependent] does not accept an intropattern as an
   argument, I believe. *)

Ltac wp_op_shadow_pair lemma x y :=
  let p := fresh in
  first [ simple eapply wp_bind | simple eapply wp_conseq ];
  [ wp_op_nude lemma
  | wp_intros p;
    clear dependent x; clear dependent y;
    destruct p as [x y] ].

(* To see example uses of the above tactics, look at the definitions
   of the tactics [wp_get] and [wp_set] in array.v. *)

(* -------------------------------------------------------------------------- *)

(* [wp_last H] renames the most recently introduced hypothesis [H]. *)

(* The tactics [wp_intros] and [wp_intros_shadow] do not allow naming the
   hypotheses that they introduce. In case there is only one such
   hypothesis, [wp_last] allows renaming it after the fact. *)

Ltac wp_last H :=
  match goal with h: _ |- _ =>
    rename h into H
  end.
