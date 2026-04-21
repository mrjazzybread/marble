From Stdlib Require Import Utf8.
From Equations Require Import Equations.

Scheme Acc_dep_ind := Induction for Acc Sort Prop.

Lemma Acc_dep_ind_strong
  {A} (R : A → A → Prop) (P : ∀ x : A, Acc R x → Prop)
  (obligation : ∀ x : A,
    ∀ Achild : (∀ y : A, R y x → Acc R y),
    ∀ IH : (∀ y : A, ∀ Ay : Acc R y, R y x → P y Ay),
    P x (Acc_intro x Achild)
  )
: ∀ (x : A) (Ax : Acc R x), P x Ax.
Proof.
  intros.
  (* The trick is to apply the weaker statement, not to [P],
     but to the property [λ x Ax, ∀ Ax, P x Ax]. *)
  eapply (Acc_dep_ind A R (λ x Ax, ∀ Ax, P x Ax)); [| exact Ax ].
  clear x Ax. intros x Ay IH Ax.
  destruct Ax. eauto.
Qed.

(* -------------------------------------------------------------------------- *)

Section S.

Context {S A : Type}.

Variable R : S → S → Prop.

Inductive message :=
| MContinue:  S → message
| MBreak: S → A → message.

Lemma wp_loop_aux
  (body : S → message)
  (decrease : ∀ {s m}, body s = m → ∀ {s'}, m = MContinue s' → R s' s)
  (s : S) (ACC : Acc R s) :
  True.
Proof.
  pattern s, ACC; eapply Acc_dep_ind_strong; clear s ACC.
  intros s ? ?.
  (* BUG: this Check command fails with
          Anomaly "intern function not found: equations_list."
     If I just remove the line [Require Import Equations]
     then it succeeds. Also, if I make [m'] an explicit argument
     instead of an implicit argument, then it succeeds. *)
  Check ((λ {m'} s' Heq,
             (Achild s' (decrease s (MContinue s') Heq s' eq_refl)))).
Abort.

End S.
