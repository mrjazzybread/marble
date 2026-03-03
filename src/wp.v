From stdpp Require Import base.
From array Require Import bool.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

(* TODO comment *)

(* TODO
Notation ID := (λ (A : Type), A).
Global Instance id_ret: MRet ID := λ A x, x.
Global Instance id_bind : MBind ID := λ A B f x, f x.
Local Notation mret := (@mret ID _ _).
 *)

Definition wp {A} (a : A) (Q : A → Prop) :=
  Q a.

Lemma wp_conseq {A} (a : A) (Q Q' : A → Prop) :
  wp a Q →
  (∀ x, Q x → Q' x) →
  wp a Q'.
Proof.
  unfold wp. eauto.
Qed.

Lemma wp_ret {A} (a : A) (Q : A → Prop) :
  Q a →
  wp a Q.
Proof.
  eauto.
Qed.

Lemma wp_iff {A} (a : A) (Q : A → Prop) :
  wp a Q ↔
  Q a.
Proof.
  eauto.
Qed.

Definition bind {A B} (a : A) (b : A → B) : B :=
  let x := a in b x.

Lemma bind_bind {A B C} (e : A) (f : A → B) (g : B → C) :
  bind (bind e f) g =
  bind e (λ x, bind (f x) g).
Proof.
  reflexivity.
Qed.

(* The lemma [bind_if] duplicates the continuation [k]. In situations
   where [k] is very small, this can be convenient; it removes the need
   to provide a specification of the join point. *)

Lemma bind_if {A B} (c : bool) (e1 e2 : A) (k : A → B) :
  bind (if c then e1 else e2) k =
  if c then bind e1 k else bind e2 k.
Proof.
  destruct c; reflexivity.
Qed.

(* TODO use a nicer notation? *)
Global Notation "'do' x ← y ; z" := (bind y (λ x : _, z))
  (at level 20, x pattern, y at level 100, z at level 200).

Lemma wp_bind {A B} (a : A) (b : A → B) (P : A → Prop) (Q : B → Prop) :
  wp a P →
  (∀ x, P x → wp (b x) Q) →
  wp (bind a b) Q.
Proof.
  eauto.
Qed.

Lemma wp_bind_unary {A B} (a : A) (b : A → B) (Q : B → Prop) :
  wp a (λ x, wp (b x) Q) →
  wp (bind a b) Q.
Proof.
  eauto.
Qed.

Lemma wp_bind_eq {A B} (a : A) (b : A → B) (Q : B → Prop) :
  (∀ x, x = a → wp (b x) Q) →
  wp (bind a b) Q.
Proof.
  eauto.
Qed.

Global Ltac wp_bind_eq :=
  eapply wp_bind_eq; intros ? ->.

(* TODO [bind] should be inlined away at extraction *)
Global Opaque wp.

Global Ltac wp_ret :=
  eapply wp_ret.

Lemma wp_if {A} (b : bool) (e1 e2 : A) (Q : A → Prop) {P1 P2 : Prop} :
  isBool b P1 P2 →
  (P1 → wp e1 Q) →
  (P2 → wp e2 Q) →
  wp (if b then e1 else e2) Q.
Proof.
  unfold isBool. intros. destruct b; eauto.
Qed.

Global Ltac wp_if :=
  eapply wp_if; [ isBool | intros | intros ].

(* [check_flex_post] checks that the current postcondition is flexible
   (i.e., a metavariable), and fails if that is not the case. *)

Global Ltac check_flex_post :=
  match goal with
  |- wp _ ?Q =>
    is_evar Q
  end.

(* TODO not useful? *)
Global Ltac wp_let :=
  match goal with
  |- wp (let x := ?e in _) ?Q =>
    set (x := e)
  end.
