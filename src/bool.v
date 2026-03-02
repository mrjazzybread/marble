From Stdlib Require Import Utf8.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

(* The Rocq standard library offers two ways of relating a Boolean
   value with a proposition: one is [reflect P b], an inductive type;
   the other is [is_true], a function of type [bool → Prop].
   On a related topic, stdpp offers [decide : {P} + {¬P}]. *)

Definition reflects (b : bool) (P Q : Prop) : Prop :=
  if b then P else Q.

Lemma reflects_andb b1 P1 Q1 b2 P2 Q2 :
  reflects b1 P1 Q1 →
  reflects b2 P2 Q2 →
  reflects (andb b1 b2) (P1 ∧ P2) (Q1 ∨ Q2).
Proof.
  unfold reflects. destruct b1, b2; simpl; tauto.
Qed.

Lemma reflects_orb b1 P1 Q1 b2 P2 Q2 :
  reflects b1 P1 Q1 →
  reflects b2 P2 Q2 →
  reflects (orb b1 b2) (P1 ∨ P2) (Q1 ∧ Q2).
Proof.
  unfold reflects. destruct b1, b2; simpl; tauto.
Qed.

Lemma reflects_negb b P Q :
  reflects b P Q →
  reflects (negb b) Q P.
Proof.
  unfold reflects. destruct b; simpl; tauto.
Qed.

Lemma reflects_intro b P :
  (b = true) ↔ P →
  reflects b P (¬P).
Proof.
  assert (false ≠ true) by congruence.
  unfold reflects. destruct b; simpl; tauto.
Qed.

Lemma reflects_intro_true P Q :
  P →
  reflects true P Q.
Proof.
  unfold reflects. tauto.
Qed.

Lemma reflects_intro_false P Q :
  Q →
  reflects false P Q.
Proof.
  unfold reflects. tauto.
Qed.

Lemma reflects_elim_true b P Q :
  reflects b P Q →
  b = true →
  P.
Proof.
  unfold reflects. intros. subst. tauto.
Qed.

Lemma reflects_elim_false b P Q :
  reflects b P Q →
  b = false →
  Q.
Proof.
  unfold reflects. intros. subst. tauto.
Qed.

Lemma prove_bool_is_false b :
  b ≠ true →
  b = false.
Proof.
  destruct b; congruence.
Qed.

(* TODO here *)

Lemma bool_neg b :
  b = false ↔ b ≠ true.
Proof.
  destruct b; split; congruence.
Qed.

Lemma show_true b :
  negb b = false →
  b = true.
Proof.
  destruct b; simpl; eauto.
Qed.

Lemma show_false b :
  negb b = true →
  b = false.
Proof.
  destruct b; simpl; eauto.
Qed.

Definition isBool (b : bool) (P : Prop) :=
  b = true ↔ P.

Lemma isBool_conseq b P P' :
  isBool b P →
  (P ↔ P') →
  isBool b P'.
Proof.
  unfold isBool. tauto.
Qed.

Lemma isBool_intro P :
  P →
  isBool true P.
Proof.
  unfold isBool. tauto.
Qed.

Lemma isBool_intro_neg P :
  ¬ P →
  isBool false P.
Proof.
  unfold isBool. split; intros; [ congruence | tauto ].
Qed.

Lemma isBool_elim b P :
  isBool b P →
  b = true →
  P.
Proof.
  unfold isBool. tauto.
Qed.

Lemma isBool_elim_neg b P :
  isBool b P →
  b = false →
  ¬ P.
Proof.
  generalize (bool_neg b).
  unfold isBool. tauto.
Qed.
