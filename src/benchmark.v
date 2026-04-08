From stdpp Require Import base.
From Stdlib Require Import ZArith.
From Stdlib Require Import Uint63.
From Stdlib Require Import Array.PArray.
From listz Require Import listz.
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

Open Scope uint63.

(* TODO move *)
Instance Inhabited_int : Inhabited int.
Proof. constructor. exact 0. Defined.

Definition data (_i : int) :=
  (10000 - _i)%uint63.

Time Definition a : array int :=
  Eval vm_compute in
  init 2000 data.
    (*  2000: 0.2 to 0.3 seconds *)
    (* 10000: 1.1 seconds *)

Time Definition a' : array int :=
  Eval vm_compute in
  sort a.
    (*  2000:  5.8 seconds in switch rocq9 (sometimes less than 3s?) *)
    (*         4.4 seconds in switch 4.14.2+flambda *)
    (*        native_compute: 0.9 to 1.2 seconds if warm, 80 seconds if not *)
    (* 10000: 41.7 seconds (wow) *)
    (* 16000: 52.1 seconds in switch 4.14.2+flambda *)

Time Definition xs : list int :=
  Eval vm_compute in
  listz.init 16000%Z (λ (i : Z), data (Uint63.of_Z i)).
    (*  2000: 0.2 seconds in switch rocq9 *)
    (*  2000: 0.1 seconds in switch 4.14.2+flambda *)
    (*  2000: 0.5 seconds in switch 4.14.2+flambda with native_compute *)
    (* 10000: 4.4 seconds  *)
    (* 16000: 6.1 to 6.6 seconds in switch 4.14.2+flambda *)

Time Definition xs' : list int :=
  Eval vm_compute in
  Sort.sort xs.
    (*  2000: between 0.01 and 0.02 seconds *)
    (* 10000: 0.09 seconds *)
    (* 16000: 0.1 seconds *)

(* Why is it 60x times faster to sort a list than to allocate it? *)
(* Why is it 500x times faster to sort a list than to sort an array? *)
