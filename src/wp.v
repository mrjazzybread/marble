From stdpp Require Import base.

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
  Q a ->
  wp a Q.
Proof.
  eauto.
Qed.

Definition bind {A B} (a : A) (b : A → B) : B :=
  let x := a in b x.

(* TODO use a nicer notation? *)
Global Notation "' x ⇜ y ; z" := (bind y (λ x : _, z))
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

(* TODO [bind] should be inlined away at extraction *)
Global Opaque wp.
