(******************************************************************************)
(*                                                                            *)
(*                                  Marble                                    *)
(*                                                                            *)
(*                       François Pottier, Inria Paris                        *)
(*                                                                            *)
(*       Copyright 2026--2026 Inria. All rights reserved. This file is        *)
(*       distributed under the terms of the GNU Library General Public        *)
(*       License, with an exception, as described in the file LICENSE.        *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Utf8.
From Stdlib Require Export Wellfounded.Wellfounded.
From Equations Require Export Equations.
From Equations.Prop Require Export Logic. (* [inspect] *)
Notation inspected x := (exist _ x _).
From marble Require Import wf. (* TODO should be merged into stdpp *)

(* -------------------------------------------------------------------------- *)

(* The following notations offers syntactic sugar for a "rich"
   conditional construct. In the first branch, the hypothesis
   [e0 = true] appears; in the second branch, [e0 = false]
   appears. A rich conditional must be used when the proof of
   termination of the code depends on this information. *)

(* In [IFC e0 THEN e1 ELSE e2], the branches [e1] and [e2] are
   functions of type [e0 = true → A] and [e0 = false → A]. *)

(* In [IF e0 THEN e1 ELSE e2], the branches [e1] and [e2] are
   just terms of type [A]. *)

Global Notation "'IFC' e0 'THEN' e1 'ELSE' e2" :=
  (
    (
      if e0 as b
      return e0 = b → _
      then e1 else e2
    ) eq_refl (* convoy pattern *)
  )
  (at level 70).

Global Notation "'IF' e0 'THEN' e1 'ELSE' e2" :=
  (
    IFC e0 THEN
      λ (_ : e0 = true), e1
    ELSE
      λ (_ : e0 = false), e2
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

Lemma IFC_if {A} (e0 : bool)
  (e1 : (e0 = true) → A) (a1 : A)
  (e2 : (e0 = false) → A) (a2 : A) :
  (∀ pf1, e1 pf1 = a1) →
  (∀ pf2, e2 pf2 = a2) →
  IFC e0 THEN e1 ELSE e2 =
  if e0 then a1 else a2.
Proof.
  intros. destruct e0; congruence.
Qed.

Lemma IFC_if_dep {A} {Q : A → Prop} (e0 : bool)
  (e1 : (e0 = true) → sig Q) (a1 : A)
  (e2 : (e0 = false) → sig Q) (a2 : A) :
  (∀ pf1, proj1_sig (e1 pf1) = a1) →
  (∀ pf2, proj1_sig (e2 pf2) = a2) →
  proj1_sig (IFC e0 THEN e1 ELSE e2) =
  if e0 then a1 else a2.
Proof.
  intros. destruct e0; congruence.
Qed.

(* -------------------------------------------------------------------------- *)

(* The tactic [cleanup] removes an equality hypothesis that is produced
   by [funelim] and that is usually unneeded. *)

Ltac cleanup :=
  match goal with h: sigmaI _ _ _ = sigmaI _ _ _ |- _ =>
    clear h
  end.

(* I can never remember how to perform well-founded induction, so here is
   a recipe. The goal must be either [x ⊢ P], where the variable [x]
   has already been introduced, or [⊢ ∀x. P]. *)

(* We offer two variants: one writes either [using Hwf], where [Hwf]
   is a proof of [well_founded R], or [along R], where type class
   search is able to find a proof of [WellFounded R]. The type class
   [WellFounded] is defined by Equations. *)

Tactic Notation "by" "well-founded" "induction" "on" ident(x) "using" constr(Hwf) :=
  induction x as [ x IH ] using (well_founded_ind Hwf).

Tactic Notation "by" "well-founded" "induction" "on" ident(x) "along" constr(R) :=
  let Hwf := fresh in
  assert (Hwf: WellFounded R) by eauto with typeclass_instances;
  induction x as [ x IH ] using (well_founded_ind Hwf);
  clear Hwf.

(* [induction x as [ x IH ] using (well_founded_ind Hwf)]
   is equivalent to:

  (* Put the goal in the form [P x]. *)
  pattern x;
  (* Apply well-founded induction *)
  eapply (well_founded_ind Hwf);
  (* Clean up. *)
  clear x;
  (* Introduce [x] and the induction hypothesis. *)
  intros x IH.

 *)

(* The tactic [by dependent induction on x Ax] performs (dependent)
   induction on a proof [Ax] of accessibility of [x]. The induction
   principle is [Acc_dep_ind_strong]. *)

Tactic Notation "by" "dependent" "induction" "on" ident(x) ident(Ax) :=
  pattern x, Ax; eapply Acc_dep_ind_strong; clear x Ax;
  intros x Achild IH.
