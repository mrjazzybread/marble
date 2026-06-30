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

From stdpp Require Import base.
From marble Require Import tactics wp iteration.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

(* This file defines cascades. *)

(* A cascade is a finite sequence of elements,
   which are produced on demand. *)

(* It is isomorphic to the type [Seq.t] in OCaml's standard library. *)

(* -------------------------------------------------------------------------- *)

(* The type of cascades. *)

Inductive head _A :=
| Cons : _A → (unit → head _A) → head _A
| Nil  : head _A.

Arguments Cons {_A}.
Arguments Nil  {_A}.

Definition cascade _A :=
  unit → head _A.

(* -------------------------------------------------------------------------- *)

(* The specification of cascades. *)

Section Spec.

(* The relation [isElem] forms a bridge between the types [_A] and [A].
   These types are the runtime type and the logical type of the elements
   of the cascade. *)
Context {_A A : Type}.
Variable isElem : _A → A → Prop.

(* [P] is the type of the producer state. *)
Context {P : Type}.

(* The relation [step] describes a labeled transition system on the
   producer states. [step j x j'] means that the producer can step
   from state [j] to state [j'] while producing element [x]. *)
Variable step : P → A → P → Prop.

(* The predicate [complete] identifies the final producer states. *)
Variable complete : P → Prop.

(* [isCascade c j] and [isHead h j] mean that the cascade [c] or the head
   [h] represents a path, through the labeled transition system, from the
   state [j] to a final state. *)

Inductive isHead : head _A → P → Prop :=
| isHeadCons :
    ∀ j j' _x x c ,
    isElem _x x →
    step j x j' →
    wp (c()) (λ h, isHead h j') → (* [isCascade c j'] *)
    isHead (Cons _x c) j
| isHeadNil :
    ∀ j,
    complete j →
    isHead Nil j.

Definition isCascade (c : cascade _A) (j : P) :=
  wp (c()) (λ h, isHead h j).

End Spec.

(* TODO establish a weakening/simulation rule to replace an LTS
        with a more abstract LTS *)

(* -------------------------------------------------------------------------- *)

(* Converting a higher-order iteration function, in CPS style, to a cascade.  *)

Section Reify.

Context `{isElem : _A → A → Prop}.
Context `{Equiv P : Type}.
Variable step : P → A → P → Prop.
Variable complete : P → Prop.

Context {C : Type}.

Variable foreach : ∀ {S R}, S → C → (S → _A → CPS R S) → CPS R S.

Definition reify (c : C) : cascade _A :=
  λ '(),
    let consume := λ '() _x k, Cons _x k in
    let finish  := λ '(),      Nil       in
    foreach () c consume finish.

Variable init : P.

Variable wp_foreach :
  ∀ {S R} (body : S → _A → CPS R S) (c : C) (ψ : P → R → Prop),
  ITER init complete
    (λ j0 j1 s Q, ∀ _x x, isElem _x x → step j0 x j1 → wp_gcps (body s _x) Q (ψ j1) (ψ j0))
    (λ s Q, wp_gcps (foreach s c body) Q (λ r, ∃ k, complete k ∧ ψ k r) (ψ init)).

Ltac wp_gcps_intro :=
  let k := fresh "k" in
  let Hk := fresh "Hk" in
  intros k Hk.

Lemma wp_reify c :
  isCascade isElem step complete (reify c) init.
Proof.
  unfold reify.
  set (consume := λ '() _x k, Cons _x k).
  set (finish  := λ '(),      Nil      ).
  unfold isCascade.
  unfold ITER in wp_foreach.
  unfold wp_gcps at 2 in wp_foreach.
  eapply wp_foreach with
    (inv := λ j '(), True)
    (ψ := λ j h, isHead isElem step complete h j).
  { prove_Proper. }
  { tauto. }
  { intros j0 j1 s Hs _x x Hx Hstep.
    destruct s. clear Hs.
    unfold consume.
    wp_gcps_intro.
    specialize (Hk () I).
    wp_ret.
    eapply isHeadCons; tc. }
  { intros s Hs.
    destruct s. destruct Hs as (k & ? & Hk).
    unfold finish.
    wp_ret. eauto using isHeadNil. }
Qed.

End Reify.
