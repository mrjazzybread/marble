From Stdlib Require Import Utf8.
From Stdlib Require Export Wellfounded.Wellfounded.
From Equations Require Export Equations.

(* The following notation offers syntactic sugar for a "rich"
   conditional construct. In the first branch, the hypothesis
   [e0 = true] appears; in the second branch, [e0 = false]
   appears. A rich conditional must be used when the proof of
   termination of the code depends on this information. *)

Global Notation "'IF' e0 'THEN' e1 'ELSE' e2" :=
  (
    (
      if e0 as b
      return e0 = b → _
      then
        λ (_ : e0 = true), e1
      else
        λ (_ : e0 = false), e2
    ) eq_refl
  )
  (at level 70).

(* A rich conditional construct has the same computational behavior
   as an ordinary conditional construct. *)

Lemma IF_if {A} (e0 : bool) (e1 e2 : A) :
  IF e0 THEN e1 ELSE e2 =
  if e0 then e1 else e2.
Proof.
  destruct e0; reflexivity.
Qed.

(* Instruct Equations to use [eauto with lia] to kill proof obligations. *)

Global Obligation Tactic :=
  simpl in *;
  Tactics.program_simplify;
  CoreTactics.equations_simpl;
  try Tactics.program_solve_wf;
  eauto with lia.
