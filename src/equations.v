From Stdlib Require Import Utf8.
From Stdlib Require Export Wellfounded.Wellfounded.
From Equations Require Export Equations.
From Equations.Prop Require Import Logic. (* [inspect] *)

Global Notation "'IF' e0 'THEN' e1 'ELSE' e2" :=
  (
    let (b, p) := inspect (e0) in
    (
      if b as b
      return e0 = b → _
      then
        λ (_ : e0 = true), e1
      else
        λ (_ : e0 = false), e2
    ) p
  )
  (at level 70).
