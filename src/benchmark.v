From stdpp Require Import base.
From Stdlib Require Import ZArith.
From Stdlib Require Import Uint63.
From Stdlib Require Import Array.PArray.
From listz Require Import listz.
From marble Require Import bool int array compare sort vector.
From marble Require Import compare.
Open Scope uint63.

(* The times in comments use OCaml 4.14.2+flambda. *)

Time Definition test_make : array int :=
  Eval vm_compute in
  make 3_000_000 0.
    (* 0.9 to 1 second : 3 million elements/second *)

Definition data (_i : int) :=
  (100000 - _i).

Definition n := 50_000.

Time Definition a : array int :=
  Eval vm_compute in
  init n data.
    (* 4.5 seconds *)

(* TODO report bug?
Time Definition xs : list int :=
  Eval vm_compute in to_list a.
    (* segmentation fault in about 15 seconds *)
 *)

Time Definition b : array int :=
  Eval vm_compute in
  init n data.
    (* 4.5 seconds *)

Time Definition time_naive_blit :=
  Eval vm_compute in
  (naive_blit a 0 b 0 n)%uint63.
    (* 4.5 seconds : 11,000 elements/second *)

Time Definition b' : array int :=
  Eval vm_compute in
  init n data.
    (* 4.5 seconds *)

Time Definition time_simple_blit :=
  Eval vm_compute in
  (simple_blit a 0 b' 0 n)%uint63.
    (* 0.06 seconds : 830,000 elements/second *)

Time Definition c : array int :=
  Eval vm_compute in
  init 16000 data.
    (* 4.5 seconds *)

Time Definition time_sort : array int :=
  Eval vm_compute in
  sort c.
    (* 16000: 49 seconds : 326 elements/second *)
