(* This lemma is useful when a [compare] function is used to perform a
   two-way comparison. It allows reasoning about each of the two
   branches just once. However, this programming style is not
   recommended, as Rocq will silently duplicate one of the branches. *)

Lemma wp_compare_Gt_Le `{Comparable} {B} (x y : A) (e1 e2 : B) (Q : B → Prop) :
  (x > y → wp e1 Q) →
  (x ≤ y → wp e2 Q) →
  wp (match compare x y with Gt => e1 | _ => e2 end) Q.
Proof.
  intros. destruct (compare_spec x y).
  + eauto using equiv_le.
  + eauto using lt_le.
  + eauto.
Qed.

Global Ltac wp_compare :=
  simple eapply wp_compare_Gt_Le; [ eauto | intro | intro ].
