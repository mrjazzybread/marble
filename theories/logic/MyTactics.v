(* [branches] looks for a disjunction in the context, and destructs it. *)

Tactic Notation "branches" :=
  match goal with h: _ \/ _ |- _ => destruct h end.

(* This tactic unpacks all existentially quantified hypotheses and splits all
   conjunctive hypotheses. *)

Ltac unpack1 :=
  match goal with
  | h: ex _ |- _ => destruct h
  | h: (_ /\ _) |- _ => destruct h
  end.

Tactic Notation "unpack" :=
  repeat progress unpack1.
Goal
  forall (P Q : nat -> Prop),
  (exists n, P n /\ Q n) ->
  (exists n, Q n /\ P n).
Proof.
  intros. unpack. eauto.
Qed.

(* This tactic decomposes an equality hypothesis between two [exist]
   constructors. *)

Ltac xx :=
  match goal with
  h: exist _ _ _ = exist _ _ _ |- _ =>
    inversion h; clear h; subst
  end.

(* This lemma can be useful when trying to exhibit a contradiction. *)

Lemma contradiction:
  forall A : Prop,
  A ->
  ~ A ->
  False.
Proof.
  tauto.
Qed.

(* This lemma can be useful when reasoning about the isomorphism
   between Booleans and propositions. *)

Lemma decision_procedure_says_no:
  forall b P,
  (b = true <-> P) ->
  b = false -> ~ P.
Proof.
  destruct b; intros ? [ _ h2 ].
  discriminate.
  intros _ h. discriminate (h2 h).
Qed.

(* ------------------------------------------------------------------------- *)

(* The tactic [injections] applies [injection] to the equality hypotheses that
   support it. *)

Ltac injections :=
  repeat match goal with
  | h: exist _ ?x _ = exist _ ?y _ |- _ =>
      assert (x = y); [ congruence | clear h ]
  | h: _ = _ |- _ =>
      first [
        (* Try to use [injection] on this hypothesis. *)
        injection h; clear h
        (* If this fails, set it aside. *)
      | revert h
      ]
  end;
  (* When done, re-introduce the hypotheses that were set aside. *)
  intros;
  (* Try substituting what can be substituted. *)
  try subst.

(* Simple forward application tactics. *)

(* [forwards: lemma] applies the lemma [lemma] in forward mode.
   The premises of the lemma become subgoals. *)

Tactic Notation "forwards:" constr(lemma) :=
  let P := fresh in
  evar (P : Prop);
  assert P; [
    unfold P; simple eapply lemma
  | subst P ].

(* [forwards fact: lemma] applies the lemma [lemma] in forward mode.
   The premises of the lemma become subgoals. In the last subgoal,
   the newly acquired fact is named [fact]. *)

Tactic Notation "forwards" simple_intropattern(h) ":" constr(lemma) :=
  let P := fresh in
  evar (P : Prop);
  assert (h: P); [
    unfold P; simple eapply lemma
  | subst P ].
