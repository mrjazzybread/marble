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

Ltac wp_ret :=
  eapply wp_ret.

Ltac wp_bind_eq :=
  eapply wp_bind_eq; intros ? ->.

Ltac wp_if :=
  first [ simple eapply wp_if | simple eapply wp_IF ];
    [ tc | intros | intros ].
