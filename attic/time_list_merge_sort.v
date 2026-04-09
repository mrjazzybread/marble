From Stdlib Require Import Utf8 List.
Import ListNotations.
From Stdlib Require Import Uint63.
From Stdlib Require Import Sorting.Mergesort.
From Stdlib Require Import Lia ZifyUint63.

(* This file contains a benchmark of the standard library's merge sort
   algorithm on lists. At this time it works only up to size 32,000
   because larger numbers cause stack overflows. *)

(* Instantiate the standard library's merge sort
   for lists of machine integers. *)
Module Int.
  Definition t := int.
  Definition leb : int → int → bool := Uint63.leb.
  Infix "<=?" := leb.
  Lemma leb_total : forall x y, (x <=? y) = true \/ (y <=? x) = true.
  Proof. unfold leb. lia. Qed.
End Int.
Module Sort := Sort Int.

(** [init_segment i n f] is a list of length [n] whose elements are [f(i)],
    [f(i+1)], etc., up to [f(i+n-1)]. *)
Fixpoint init_segment {A} (i : nat) (n : nat) (f : nat → A) : list A :=
  match n with 0 => [] | S n => f i :: init_segment (S i) n f end.

(** [init n f] is a list of length [n] whose elements are [f(0)],
    [f(1)], etc., up to [f(n-1)]. *)
Definition init {A} (n : nat) (f : nat → A) : list A :=
  init_segment 0 n f.

Definition n : nat :=
  32_000.

Time Definition time_init : list int :=
  Eval vm_compute in
  init n (λ (i : nat), 0%uint63).
    (* 32,000: 0.16 seconds *)

Time Definition time_sort : list int :=
  Eval vm_compute in
  Sort.sort time_init.
    (* 32,000: 0.16 seconds *)
