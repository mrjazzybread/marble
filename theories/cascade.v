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
From marble Require Import wp.

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
Context `{isElem : _A → A → Prop}.

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
