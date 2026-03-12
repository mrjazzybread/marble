(* This file contains code which I once thought would be useful to reason
   about an interruptible loop, counting up, on integers. It is perhaps
   overkill. Anyway, it is currently unused. *)

(* The assertion [finished a b i s o] means that the loop has ended.

   It is defined as a disjunction of the following situations:

   - The loop has run at least once. [a < i ≤ b] holds.
     Furthermore, if the loop has stopped early, which is indicated
     by the condition [i < b], then [o] must be [break _].

   - The loop has not run at all, in which case [b ≤ a = i] holds.
     In this case, [i] must be [a] and [o] must be [continue]. *)

Definition finished {A} a b i s (o : option A) :=
  a < i ∧ i ≤ b ∧ (i < b → o ≠ continue) ∨
  b ≤ a ∧ i = a ∧ o = continue.

(* The assertion [finished a b i s o], as defined above, is somewhat strange,
   as it is a disjunction between the case where at least one iteration has
   taken place (a < b) and the case where none has taken place (a ≥ b). What
   seems more natural is a disjunction between the case where the bounds are
   ordered as expected (a ≤ b) and the case where they are not (a > b).
   The following lemma provides an alternate characterization of [finished]
   along these lines. *)

Lemma finished_iff a b i s (o : option A) :
  finished a b i s o ↔
   (
     (* Case [a ≤ b]: *)
       (* Then [i] lies between [a] and [b], inclusive;
          [i] is [a] if and only if the interval is empty;
          if [i] is less than [b] then we must have broken out;
          if the interval is empty then we cannot have broken out. *)
       a ≤ i ∧ i ≤ b ∧ (i = a ↔ a = b) ∧
       (i < b → o ≠ continue) ∧
       (a = b → o = continue)
     ∨
     (* Case [b < a]: *)
         (* Then [i] must be [a] and we cannot have broken out. *)
       b < a ∧ i = a ∧ o = continue
   ).
Proof.
  unfold finished. split; intros [|]; unpack; subst.
  { left. repeat split; eauto with lia. }
  { case (decide (a = b)); intros; [ subst b |].
    + left. eauto with lia.
    + right. eauto with lia. }
  { case (decide (i = a)); intros; [ subst i |].
    + right. eauto with lia.
    + left. eauto with lia. }
  { eauto with lia. }
Qed.

(* Here is a different way of expressing the same result. *)

Lemma finished_iff' a b i s (o : option A) :
  finished a b i s o ↔
   (
     (* Case [a ≤ b]: *)
       a ≤ i ∧ i ≤ b ∧ (i = a ↔ a = b) ∧
       (* If we have broken out then at least one element has been examined.
          If we have not broken out then the loop index has reached the end
          of the interval. *)
       match o with break _ => a < i | continue => i = b end
     ∨
       b < a ∧ i = a ∧ o = continue
   ).
Proof.
  cut (
    a ≤ i ∧ i ≤ b ∧ (i = a ↔ a = b) →
    (i < b → o ≠ continue) ∧ (a = b → o = continue) ↔
    match o with break _ => a < i | continue => i = b end
  ). { rewrite finished_iff. tauto. }
  intros. unpack.
  destruct o; split; intros; unpack; eauto with lia.
  { case (decide (a = b)); intros h; [ exfalso | lia ].
    match goal with H: a = b → _ |- _ => specialize (H h) end.
    congruence. }
  { case (decide (i < b)); intros h; [ exfalso | lia ].
    match goal with H: i < b → _ |- _ => specialize (H h) end.
    congruence. }
Qed.

(* This corollary describes just the case where [a ≤ b] is known to hold.
   It should the most useful corollary in practice. *)

Lemma finished_leq_iff a b i s (o : option A) :
  a ≤ b →
  finished a b i s o ↔
   (
     a ≤ i ∧ i ≤ b ∧ (i = a ↔ a = b) ∧
     match o with break _ => a < i | continue => i = b end
   ).
Proof.
  intros. rewrite finished_iff'. split.
  { intros [|]; [ tauto | lia ]. }
  { tauto. }
Qed.
