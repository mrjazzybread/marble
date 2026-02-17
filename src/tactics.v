From Equations Require Import Equations.

(* [cleanup] removes an equality hypothesis that is produced by
   [funelim] and that is usually unneeded. *)
Ltac cleanup :=
  match goal with h: sigmaI _ _ _ = sigmaI _ _ _ |- _ =>
    clear h
  end.
