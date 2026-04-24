From stdpp Require Import base.

(* This file equips the type [option A] with a strict ordering [olt],
   which is intentionally NOT well-founded: [None < None] holds. *)

Section S.

(* Suppose we have a type [A] equipped with a strict order [R]. *)

Context `{StrictOrder A R}.

(* Then, the type [option A] can be equipped with a strict ordering where
   [None < None] holds. This ordering is NOT well-founded: indeed, [None]
   is not accessible. [Some x] is accessible if and only if [x] is
   accessible in the ordering of the type [A]. *)

(* The type [option A], equipped with this ordering, can be used to keep
   track of an invariant. If an element [x] does not satisfy the invariant
   then its measure should be [None]. In other words, if [x] is accessible
   then [x] satisfies the invariant. Thus, a witness of accessibility is,
   at the same time, a witness that the invariant is satisfied. *)

Implicit Type o : option A.

Definition olt o1 o2 :=
  match o1, o2 with
  | None, None =>
      True (* loop! *)
  | None, Some _
  | Some _, None =>
      False
  | Some x1, Some x2 =>
      R x1 x2
  end.

(* We define the non-strict ordering [ole] as the union of [olt] and
   equality. Other definitions come to mind, but this one suits our
   purposes. *)

Definition ole o1 o2 :=
  olt o1 o2 ∨ o1 = o2.

(* Local notations, lemmas, and tactics. *)

Declare Scope option_scope.
Local Infix "<" := olt (at level 70) : option_scope.
Local Infix "≤" := ole (at level 70) : option_scope.
Local Open Scope option_scope.

Local Lemma R_trans x y z : R x y → R y z → R x z.
Proof. intros. transitivity y; eauto. Qed.

Local Ltac injections :=
  repeat match goal with h: Some ?o1 = Some ?o2 |- _ =>
    injection h; clear h; intro
  end; try subst.

(* Properties of [olt]. *)

Lemma olt_refl o : o = None → o < o.
Proof. intro. subst. simpl. tauto. Qed.

Lemma olt_trans o0 o1 o2 : o0 < o1 → o1 < o2 → o0 < o2.
Proof.
  destruct o0 as [o0|]; destruct o1 as [o1|]; destruct o2 as [o2|];
  unfold olt; eauto using R_trans.
  + tauto.
Qed.

(* Properties of [ole]. *)

Lemma ole_refl o : o ≤ o.
Proof. unfold ole. eauto. Qed.

Lemma ole_trans o0 o1 o2 : o0 ≤ o1 → o1 ≤ o2 → o0 ≤ o2.
Proof.
  unfold ole. intros [|] [|]; subst; eauto using olt_trans.
Qed.

Lemma ole_olt_trans o0 o1 o2 : o0 ≤ o1 → o1 < o2 → o0 < o2.
Proof.
  unfold ole. intros [|] ?; subst; eauto using olt_trans.
Qed.

Lemma olt_ole_trans o0 o1 o2 : o0 < o1 → o1 ≤ o2 → o0 < o2.
Proof.
  unfold ole. intros ? [|]; subst; eauto using olt_trans.
Qed.

Lemma olt_ole o0 o1 : o0 < o1 → o0 ≤ o1.
Proof. unfold ole. eauto. Qed.

(* [Some x] at type [option A] is accessible if and only if
   [x] at type [A] is accessible. *)

Lemma Acc_Some : ∀ x, Acc R x → Acc olt (Some x).
Proof.
  induction 1. constructor. intros x' ?.
  (* [x'] cannot be [None]. *)
  destruct x' as [x'|]; simpl in *; [ eauto | tauto ].
Qed.

(* If [A] is well-founded then every [Some x] is accessible. *)

Lemma wf_Some : well_founded R → ∀ x, Acc olt (Some x).
Proof.
  unfold well_founded. eauto using Acc_Some.
Qed.

(* [None] is not accessible. *)

Local Lemma Acc_None_aux : ∀ x, Acc olt x → x = None → False.
Proof.
  induction 1. intro. subst x.
  clear H0. rename H1 into IH.
  eapply IH; [| reflexivity ].
  (* [None < None] is true. *)
  reflexivity.
Qed.

Lemma Acc_None : ¬ Acc olt None.
Proof.
  unfold not. eauto using Acc_None_aux.
Qed.

End S.
