From Stdlib Require Extraction.

From Equations.Prop Require Import Logic.
Extraction Inline inspect.

From marble Require Import wp.
Extraction Inline bind.

From Stdlib Require ExtrOCamlInt63.

From marble Require Import iteration.
Extraction Inline did_break did_not_break.

From marble Require Import int loop.
Extraction Inline iter_down iter_up xiter_up uxiter_up.
Extraction Inline Ni.
Extraction Inline iter_down_unrolled iter_up_unrolled.
Extraction Inline iter_down_N iter_up_N.

(* Recursive Extraction iter_down iter_up xiter_up uxiter_up. *)

From Stdlib Require ExtrOCamlPArray.
From marble Require Import array.
Extraction Inline to_list.

(* Recursive Extraction of_list blit blit' copy find_index equal. *)

From marble Require Import sort.
Extraction Inline sortto_segment_2.
  (* [sortto_segment_3] are [sortto_segment_4] seem too large to
     be inlined; they have multiple call sites. *)
Extraction Inline optimistic_merge_1 optimistic_merge_2
                  optimistic_merge_12.

Recursive Extraction sort.sort.
