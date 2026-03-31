From Stdlib Require Import Utf8.
From stdpp Require Import base.
From marble Require Import list_extra.
From marble Require Import tactics.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

(* The Rocq standard library offers several ways of relating a Boolean
   value with a proposition: [BoolSpec P Q b] and [reflect P b] are
   inductive types; [is_true] is a function of type [bool → Prop].
   On a related topic, stdpp offers [decide : {P} + {¬P}]. *)

(* We define [isBool b P Q] to mean that [b = true] implies [P]
   and [b = false] implies [Q]. We do not require that [Q] be [¬P];
   this is more flexible and lets us avoid a negation in the lemma
   [reflect_negb], which could lead to the introduction of double
   negations. *)

Class isBool (b : bool) (P Q : Prop) : Prop :=
  build_isBool : if b then P else Q.

Global Hint Mode isBool ! - - : typeclass_instances.
  (* Instantiate the parameter [b] only if its head is already known,
     that is, not a metavariable. The other two parameters are outputs. *)

(* In the fairly common case where [Q] is [¬P], we write [isBool1 P]. *)

Global Notation isBool1 b P :=
  (isBool b P (¬P)).

(* Bridges between [BoolSpec] and [isBool]. *)

Lemma BoolSpec_iff_isBool P Q b :
  BoolSpec P Q b ↔ isBool b P Q.
Proof.
  split.
  + destruct 1; simpl; tauto.
  + destruct b; simpl; constructor; tauto.
Qed.

Global Instance BoolSpec_isBool P Q b :
  BoolSpec P Q b → isBool b P Q.
Proof.
  destruct 1; simpl; tauto.
Qed.

(* Rewriting inside [isBool] and [BoolSpec]. *)

Instance isBool_variance : Proper (eq ==> iff ==> iff ==> iff) isBool.
Proof.
  intros b b' Hb P P' HP Q Q' HQ. subst b'.
  destruct b; simpl; tauto.
Qed.

Instance BoolSpec_variance : Proper (iff ==> iff ==> eq ==> iff) BoolSpec.
Proof.
  intros P P' HP Q Q' HQ b b' Hb. subst b'.
  destruct b; split; inversion 1; constructor; tauto.
Qed.

(* The next three lemmas construct [P] and [Q] by examination of [b]. *)

Global Instance isBool_andb b1 P1 Q1 b2 P2 Q2 :
  isBool b1 P1 Q1 →
  isBool b2 P2 Q2 →
  isBool (andb b1 b2) (P1 ∧ P2) (Q1 ∨ Q2).
Proof.
  unfold isBool. destruct b1, b2; simpl; tauto.
Qed.

Global Instance isBool_orb b1 P1 Q1 b2 P2 Q2 :
  isBool b1 P1 Q1 →
  isBool b2 P2 Q2 →
  isBool (orb b1 b2) (P1 ∨ P2) (Q1 ∧ Q2).
Proof.
  unfold isBool. destruct b1, b2; simpl; tauto.
Qed.

Global Instance isBool_negb b P Q :
  isBool b P Q →
  isBool (negb b) Q P.
Proof.
  unfold isBool. destruct b; simpl; tauto.
Qed.

(* The following lemmas can prove [isBool b P Q] when [b], [P], [Q] are
   already determined. *)

Lemma isBool_intro b P :
  (b = true) ↔ P →
  isBool b P (¬P).
Proof.
  assert (false ≠ true) by congruence.
  unfold isBool. destruct b; simpl; tauto.
Qed.

Global Instance isBool_intro_true P Q :
  P →
  isBool true P Q.
Proof.
  unfold isBool. tauto.
Qed.

Global Instance isBool_intro_false P Q :
  Q →
  isBool false P Q.
Proof.
  unfold isBool. tauto.
Qed.

(* Consequence rules. *)

Lemma isBool_conseq b P P' Q Q' :
  isBool b P Q →
  (P ↔ P') →
  (Q ↔ Q') →
  isBool b P' Q'.
Proof.
  unfold isBool. destruct b; tauto.
Qed.

Lemma isBool1_conseq b P P' :
  isBool1 b P →
  (P ↔ P') →
  isBool1 b P'.
Proof.
  unfold isBool. destruct b; tauto.
Qed.

(* The next two lemmas are used in the tactic [isBool_magic]. *)

Lemma isBool_elim_true b P Q :
  b = true →
  isBool b P Q →
  P.
Proof.
  unfold isBool. intros. subst. tauto.
Qed.

Lemma isBool_elim_false b P Q :
  b = false →
  isBool b P Q →
  Q.
Proof.
  unfold isBool. intros. subst. tauto.
Qed.

(* The tactic [isBool_magic] looks for a hypothesis of the form [?b = true]
   or [?b = false] and transforms it into a hypothesis of the form [P] or [Q]
   provided type class search finds a fact of the form [isBool b P Q]. *)

Global Ltac isBool_magic :=
  match goal with
  | h: ?b = true |- _ =>
      let P := fresh in
      evar (P : Prop);
      assert (P); [
        eapply (@isBool_elim_true b); [ exact h | tc ]
      | clear h; subst P
      ]
  | h: ?b = false |- _ =>
      let P := fresh in
      evar (P : Prop);
      assert (P); [
        eapply (@isBool_elim_false b); [ exact h | tc ]
      | clear h; subst P
      ]
  end.

(* -------------------------------------------------------------------------- *)

(* A few basic facts about Booleans. *)

Lemma bool_neg b :
  b = false ↔ b ≠ true.
Proof.
  destruct b; split; congruence.
Qed.

Lemma negb_eq_false b :
  negb b = false ↔
  b = true.
Proof.
  assert (false ≠ true) by congruence.
  assert (true ≠ false) by congruence.
  destruct b; simpl; tauto.
Qed.

Lemma negb_eq_true b :
  negb b = true ↔
  b = false.
Proof.
  assert (false ≠ true) by congruence.
  assert (true ≠ false) by congruence.
  destruct b; simpl; tauto.
Qed.

Global Hint Rewrite
  negb_eq_false
  negb_eq_true
: bool.

(* -------------------------------------------------------------------------- *)

(* The following instances allow establishing [isBool _ (Forall2 _ _ _)]. *)

Global Instance isBool1_true_Forall2 `{Inhabited A} P (xs ys : list A) :
  length xs = length ys →
  (∀ i, valid i xs → P (xs !!! i) (ys !!! i)) →
  isBool1 true (Forall2 P xs ys).
Proof.
  intros. eapply isBool_intro_true. rewrite Forall2_lookup_total. firstorder.
Qed.

Global Instance isBool1_false_Forall2_witness `{Inhabited A} P (xs ys : list A) :
  ∀ i,
  valid i xs →
  valid i ys →
  ¬ P (xs !!! i) (ys !!! i) →
  isBool1 false (Forall2 P xs ys).
Proof.
  intros. eapply isBool_intro_false. rewrite Forall2_lookup_total. firstorder.
Qed.

Global Instance isBool1_false_Forall2_lengths `{Inhabited A} P (xs ys : list A) :
  length xs ≠ length ys →
  isBool1 false (Forall2 P xs ys).
Proof.
  intros. eapply isBool_intro_false. rewrite Forall2_lookup_total. firstorder.
Qed.
