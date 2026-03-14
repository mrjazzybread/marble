From Stdlib Require Extraction.

From Equations.Prop Require Import Logic.
Extraction Inline inspect.

From marble Require Import wp.
Extraction Inline bind.

From Stdlib Require ExtrOCamlInt63.

From marble Require Import iteration.
Extraction Inline did_break did_not_break.

From marble Require Import int.
Extraction Inline iter_down iter_up xiter_up uxiter_up.

(* Recursive Extraction iter_down iter_up xiter_up uxiter_up. *)

From Stdlib Require ExtrOCamlPArray.
From marble Require Import array.

(* Recursive Extraction of_list blit blit' copy find_index equal. *)
