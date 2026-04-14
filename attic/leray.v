(* Yann Leray wrote:

   You found an exponential blow up in the definition of to_Z, coupled
   with primitive add not playing nice.

   https://github.com/rocq-prover/rocq/issues/21919 *)

From Corelib Require Import PrimInt63 Uint63Axioms.

Section K.
Variables i : int.

Notation f n :=
  (let to_Z := (to_Z_rec n) in
  eq_refl : to_Z (add i 0) = to_Z (add i 1)).

Time Fail Check f 10. (* 0.04 second *)
Time Fail Check f 11. (* 0.06 second *)
Time Fail Check f 12. (* 0.13 second *)
Time Fail Check f 13. (* 0.28 second *)
Time Fail Check f 14. (* 0.59 second *)
Time Fail Check f 15. (* 1.28 second *)

(* This example, where [n] is 63, does not terminate. *)
Definition left  i := add i 0.
Definition right i := add i 1.
(* Check (eq_refl : to_Z (left i) = to_Z (right i)). *)

(* The head normal forms of the terms `to_Z (add i 0)` and
   `to_Z (add i 1)` can easily be computed by `Eval hnf`.
   One is
   `if is_even (add i 0) then ... else ...`
   and the other is
   `if is_even (add i 1) then ... else ...`.
   Now, Rocq is able to quickly check that the terms
   `is_even (add i 0)` and `is_even (add i 1)`
   are *not* convertible.
   Can't it immediately deduce that the two `if` constructs
   are not convertible, without attempting to reduce their branches?
 *)


Eval hnf in to_Z (add i 0).
Eval hnf in to_Z (add i 1).
Fail Check (eq_refl : is_even (add i 0) = is_even (add i 1)).

Fail Check (fun (left : int -> int) (right : int -> int) =>
       eq_refl : to_Z (left i) = to_Z (right i)).

End K.
