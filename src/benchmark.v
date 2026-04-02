From stdpp Require Import base.
From Stdlib Require Import Uint63.
From Stdlib Require Import Array.PArray.
From marble Require Import list_init.
From marble Require Import bool int array compare sort vector.
From marble Require Import compare.

From Stdlib Require Import Sorting.Mergesort.
From Stdlib Require Import Lia ZifyUint63.

Module Int.
  Definition t := int.
  Definition leb : int → int → bool := leb. (* or: Uint63.leb *)
  Infix "<=?" := leb.
  Lemma leb_total : forall x y, (x <=? y) = true \/ (y <=? x) = true.
  Proof. unfold leb. unfold compare.leb. simpl. lia. Qed.
End Int.
Module Sort := Sort Int.

Implicit Types _i : int.

Open Scope uint63.

(* TODO move *)
Instance Inhabited_int : Inhabited int.
Proof. constructor. exact 0. Defined.

Definition data _i :=
  (10000 - _i)%uint63.

Time Definition a : array int :=
  Eval vm_compute in
  init 2000 data.
    (*  2000: 0.2 to 0.3 seconds *)
    (* 10000: 1.1 seconds *)

Time Definition a' : array int :=
  Eval vm_compute in
  sort a.
    (*  2000: 2.7 seconds; (was 6 seconds; why?) *)
    (*        native_compute: 0.9 seconds if warm *)
    (* 10000: 39.8 seconds *)

Time Definition xs : list int :=
  Eval vm_compute in
  list_init.init 2000 (λ (i : nat), data (Uint63.of_nat i)).
    (*  2000: 0.18 seconds *)
    (* 10000: 4.1 seconds  *)

Time Definition xs' : list int :=
  Eval vm_compute in
  Sort.sort xs.
    (*  2000: between 0.01 and 0.02 seconds *)
    (* 10000: 0.08 seconds *)
