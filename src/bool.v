From Stdlib Require Import Utf8.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

(* The Rocq standard library offers two ways of relating a Boolean
   value with a proposition: one is [reflect P b], an inductive type;
   the other is [is_true], a function of type [bool → Prop].
   On a related topic, stdpp offers [decide : {P} + {¬P}]. *)

Class reflects (b : bool) (P Q : Prop) : Prop :=
  build_reflects :
  if b then P else Q.
Global Hint Mode reflects ! - - : typeclass_instances.
  (* Instantiate the parameter [b] only if its head is already known,
     that is, not a metavariable. The other two parameters are outputs. *)

(* TODO rename *)
Global Notation reflects1 b P :=
  (reflects b P (¬P)).

Global Instance reflects_andb b1 P1 Q1 b2 P2 Q2 :
  reflects b1 P1 Q1 →
  reflects b2 P2 Q2 →
  reflects (andb b1 b2) (P1 ∧ P2) (Q1 ∨ Q2).
Proof.
  unfold reflects. destruct b1, b2; simpl; tauto.
Qed.

Global Instance reflects_orb b1 P1 Q1 b2 P2 Q2 :
  reflects b1 P1 Q1 →
  reflects b2 P2 Q2 →
  reflects (orb b1 b2) (P1 ∨ P2) (Q1 ∧ Q2).
Proof.
  unfold reflects. destruct b1, b2; simpl; tauto.
Qed.

Global Instance reflects_negb b P Q :
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

Global Instance reflects_intro_true P Q :
  P →
  reflects true P Q.
Proof.
  unfold reflects. tauto.
Qed.

Global Instance reflects_intro_false P Q :
  Q →
  reflects false P Q.
Proof.
  unfold reflects. tauto.
Qed.

(* TODO remove? *)
Lemma reflects_elim_true b P Q :
  b = true →
  reflects b P Q →
  P.
Proof.
  unfold reflects. intros. subst. tauto.
Qed.

Lemma reflects_elim_false b P Q :
  b = false →
  reflects b P Q →
  Q.
Proof.
  unfold reflects. intros. subst. tauto.
Qed.

Lemma reflects_conseq b P P' Q Q' :
  reflects b P Q →
  (P ↔ P') →
  (Q ↔ Q') →
  reflects b P' Q'.
Proof.
  unfold reflects. destruct b; tauto.
Qed.

Lemma reflects1_conseq b P P' :
  reflects1 b P →
  (P ↔ P') →
  reflects1 b P'.
Proof.
  unfold reflects. destruct b; tauto.
Qed.

(* The tactic [reflects] attempts to prove a goal of the form
   [reflects b ?P ?Q] using type class search. *)

Ltac reflects :=
  eauto with typeclass_instances.

(* The tactic [reflects_magic] looks for a hypothesis of the form [?b = true]
   or [?b = false] and transforms it into a hypothesis of the form [P] or [Q]
   provided type class search finds a fact of the form [reflects b P Q]. *)

Ltac reflects_magic :=
  match goal with
  | h: ?b = true |- _ =>
      let P := fresh in
      evar (P : Prop);
      assert (P); [
        eapply (@reflects_elim_true b); [ exact h | reflects ]
      | clear h; subst P
      ]
  | h: ?b = false |- _ =>
      let P := fresh in
      evar (P : Prop);
      assert (P); [
        eapply (@reflects_elim_false b); [ exact h | reflects ]
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
