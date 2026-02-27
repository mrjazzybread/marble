From Stdlib Require Extraction.

From Equations.Prop Require Import Logic.
Extraction Inline inspect.

From array Require Import wp.
Extraction Inline bind.

From Stdlib Require ExtrOCamlInt63.
From array Require Import int.
Recursive Extraction down.

From Stdlib Require ExtrOCamlPArray.
From array Require Import array.
Recursive Extraction of_list blit find_index.

(* TODO test extracting to defensive mutable arrays
   instead of persistent arrays *)
