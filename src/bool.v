From Stdlib Require Import Utf8.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

Lemma bool_neg b :
  b = false ↔ ¬ (b = true).
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
