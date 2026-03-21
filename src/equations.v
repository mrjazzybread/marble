From Stdlib Require Import Utf8.
From Stdlib Require Export Wellfounded.Wellfounded.
From Equations Require Export Equations.
From Equations.Prop Require Import Logic. (* [inspect] *)
  (* If [x] has type [A] then the type of [inspect x] is
     {y : A | x = y}. *)

(* The following notation offers syntactic sugar for a "rich"
   conditional construct. In the first branch, the hypothesis
   [e0 = true] appears; in the second branch, [e0 = false]
   appears. A rich conditional must be used when the proof of
   termination of the code depends on this information. *)

Global Notation "'IF' e0 'THEN' e1 'ELSE' e2" :=
  (
    let (b, p) := inspect (e0) in
    (
      if b as b
      return e0 = b → _
      then
        λ (_ : e0 = true), e1
      else
        λ (_ : e0 = false), e2
    ) p
  )
  (at level 70).

(* Instruct Equations to use [eauto with lia] to kill proof obligations. *)

Global Obligation Tactic :=
  simpl in *;
  Tactics.program_simplify;
  CoreTactics.equations_simpl;
  try Tactics.program_solve_wf;
  eauto with lia.
