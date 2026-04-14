(* https://github.com/rocq-prover/rocq/issues/21919 *)

(* See also leray.v *)

From Stdlib Require Import ZArith Lia.
From Stdlib Require Import Uint63 ZifyUint63.

Open Scope Z_scope.
Implicit Types _i _j : int.

Definition igt _i _j :=
  to_Z _j < to_Z _i.

Definition rigt _a _i _j :=
  igt (_i - _a) (_j - _a).

Notation   _left _j := (2 * _j + 1)%uint63.
Notation  _right _j := (2 * _j + 2)%uint63.

Local Lemma rigt_left {_i _n} :
  (_n / 2 ≤?_i)%uint63 = false ->
  rigt _n (_left _i)%uint63 _i.
Proof. unfold rigt, igt. lia. Qed.

Local Lemma rigt_right {_i _n} :
  ((_n - 1) / 2 ≤? _i)%uint63 = false ->
  rigt _n (_right _i)%uint63 _i.
Proof. unfold rigt, igt. lia. Qed.

Local Lemma rigt_left_again {_i _n} :
  (_n / 2 ≤?_i)%uint63 = false ->
  rigt _n (_left _i)%uint63 _i.
Proof. eauto 1 using rigt_right with nocore. (* diverges *) Abort.

Lemma foo _n _i :
  ((_n - 1) / 2 ≤? _i)%uint63 = false ->
  True.
Proof.
  intros.
  assert (rigt _n (_left _i) _i) by (unfold rigt, igt; lia).
  (* This second assertion can be proved in the same way: *)
  (* assert (rigt _n (_right _i) _i) by (unfold rigt, igt; lia). *)
  (* Yet an attempt to prove it using [eauto 1] never terminates: *)
  assert (rigt _n (_right _i) _i). eassumption. (* diverges *)
Abort.
