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

From Corelib Require Extraction.

(* The following line avoids a warning. *)
Set Extraction Output Directory ".".

(* -------------------------------------------------------------------------- *)

(* Basics. *)

From Corelib Require ExtrOcamlBasic.
Extraction Inline
  negb
.

(* -------------------------------------------------------------------------- *)

(* Rocq's primitive integers. *)

From Stdlib Require ExtrOCamlInt63.

Extraction Inline
  PrimInt63.add
  PrimInt63.sub
  PrimInt63.mul
  PrimInt63.div
  PrimInt63.eqb
  PrimInt63.ltb
  PrimInt63.leb
.

(* -------------------------------------------------------------------------- *)

(* Rocq's primitive arrays. *)

(* From Stdlib Require ExtrOCamlPArray. *)

From Stdlib Require PArray.

Extract Constant PrimArray.array "'a" => "'a Array63.t".
  (* Extraction Inline PrimArray.array. *) (* BUG *)

Extract Inlined Constant PrimArray.make => "Array63.make".
Extract Inlined Constant PrimArray.get => "Array63.get".
Extract Inlined Constant PrimArray.default => "Array63.default".
Extract Inlined Constant PrimArray.set => "Array63.set".
Extract Inlined Constant PrimArray.length => "Array63.length".
Extract Inlined Constant PrimArray.copy => "Array63.copy".

Extraction Inline
  PrimArray.make
  PrimArray.get
  PrimArray.set
  PrimArray.length
  PrimArray.max_length
.

(* -------------------------------------------------------------------------- *)

(* Our own modules. *)

(* First, we provide [Extraction Inline] commands for each module. *)

(* Then (at the end,), we emit one [Separate Extraction] command
   for all modules at once. *)

From marble Require wp.

Extraction Inline
  wp.bind
.

From marble Require iteration.

Extraction Inline
  iteration.did_break
  iteration.did_not_break
.

From marble Require int.

Extraction Inline
  int._min
  int._max
.

From marble Require loop.

Extraction Inline
  loop.Ni
  loop.iter_up
  loop.xiter_up
  loop.uxiter_up
.

From marble Require array.

Extraction Inline
  array.to_list
  array.list_iteri
  array.list_length
  array.exist
  array.for_all
.

From marble Require sort.

Extraction Inline
  sort.sortto_segment_2
  (* [sortto_segment_3] are [sortto_segment_4] seem too large to
     be inlined; they have multiple call sites. *)
  sort.optimistic_merge_1
  sort.optimistic_merge_2
  sort.optimistic_merge_12
.

From marble Require vector.

From marble Require pqueue.

Separate Extraction

  loop.iter_up
  loop.iter_down
  loop.xiter_up
  loop.xiter_down
  loop.uxiter_up
  loop.uxiter_down

  array.segment_to_list
  array.to_list
  array.list_iteri
  array.list_length
  array.of_list
  array.blit
  array.blit'
  array.copy
  array.sub
  array.append
  array.fill
  array.find_index
  array.exist
  array.for_all
  array.equal
  array.segment_iteri
  array.iteri
  array.init

  sort.sort_seg
  sort.sort
  sort.merge

  vector.create
  vector.length
  vector.get
  vector.set
  vector.pop
  vector.push
  vector.reserve
  vector.segment_iteri
  vector.iteri
  vector.steal_array
  vector.of_array
  vector.of_list

  pqueue.create
  pqueue.insert
  pqueue.extract_nonempty
  pqueue.extract

.
