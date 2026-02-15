From Stdlib Require Import Utf8.

Definition isBool (b : bool) (P : Prop) :=
  b = true ↔ P.

Lemma isBool_conseq b P P' :
  isBool b P →
  (P ↔ P') →
  isBool b P'.
Proof.
  unfold isBool. tauto.
Qed.
