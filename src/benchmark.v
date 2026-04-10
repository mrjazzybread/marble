From stdpp Require Import base.
From Stdlib Require Import ZArith.
From Stdlib Require Import Uint63.
From Stdlib Require Import Array.PArray.
From listz Require Import listz.
From marble Require Import bool int array compare.
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

Definition time_to_list : int :=
  Eval vm_compute in hd 0 (to_list a).
    (* about 14 seconds : 3500 elements/second *)
    (* calling [hd 0 _] suppresses display, which would crash *)

Time Definition b : array int :=
  Eval vm_compute in
  init n data.
    (* 4.5 seconds *)

Time Definition time_naive_blit :=
  Eval vm_compute in
  (naive_blit a 0 b 0 n)%uint63.
    (* when [iter_up] was defined using Equations, this used to take
       4.5 seconds : 11,000 elements/second *)
    (* now 0.065 seconds : 770,000 elements/second *)

Time Definition b' : array int :=
  Eval vm_compute in
  init n data.
    (* 4.5 seconds *)

Time Definition time_simple_blit :=
  Eval vm_compute in
  (simple_blit a 0 b' 0 n)%uint63.
    (* 0.06 seconds : 830,000 elements/second *)

Time Definition b'' : array int :=
  Eval vm_compute in
  init n data.
    (* 4.5 seconds *)

Time Definition time_equations_blit :=
  Eval vm_compute in
  (equations_blit a 0 b'' 0 n)%uint63.
    (* 4.7 seconds : 10,500 elements/second *)

Time Definition b''' : array int :=
  Eval vm_compute in
  init n data.
    (* 4.5 seconds *)

Time Definition time_blit :=
  Eval vm_compute in
  (blit a 0 b''' 0 n)%uint63.
    (* 0.055 seconds : 910,000 elements/second *)

From marble Require Import sort.

Time Definition c : array int :=
  Eval vm_compute in
  init 16000 data.
    (* 1.4 seconds *)

Time Definition time_sort : array int :=
  Eval vm_compute in
  sort c.
    (* 1600: 1.5 seconds *)
    (* 16000: 22 seconds : 727 elements/second *)
    (* not fast, but already twice faster than with [simple_blit] *)
