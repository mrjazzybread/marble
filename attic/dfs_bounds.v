(* We work with marks arrays [m] such that [default m = true] holds. That
   is, outside of the bounds of the array, every vertex is considered
   marked. Therefore, should an out-of-bounds vertex be encountered, then
   this vertex would be ignored. This lets us prove termination without
   imposing any condition on the vertices that the algorithm receives as
   parameters. *)

Definition mok m :=
  default m = true.

Local Lemma remark m _v :
  mok m →
  get m _v = false →
  (_v <? length m)%uint63 = true.
Proof.
  intros Hok Hv.
  (* Assume, by way of contradiction, that [_v <? length m] is false. *)
  destruct ((_v <? length m)%uint63) eqn:Heq; [ tauto | exfalso ].
  (* Then this array access is out of bounds. So [default m] is [false]. *)
  rewrite get_out_of_bounds in Hv by assumption.
  (* But we have assumed that [default m] is [true]. *)
  congruence.
Qed.

(* Thus, the weight-decrease lemma can be reformulated. *)

Local Lemma marking_decreases_weight' m _v :
  mok m →
  get m _v = false →
  (mweight (set m _v true) < mweight m)%nat.
Proof.
  eauto using marking_decreases_weight, remark.
Qed.

(* The marks arrays evolve along the following relation. *)

Local Definition mlt m1 m2 :=
  default m1 = default m2 ∧ (mweight m1 < mweight m2)%nat.

Local Definition mle m1 m2 :=
  default m1 = default m2 ∧ (mweight m1 ≤ mweight m2)%nat.

Local Lemma mle_refl m :
  mle m m.
Proof.
  unfold mle. split; [ congruence | lia ].
Qed.

Local Lemma mle_trans m1 m2 m3 :
  mle m1 m2 → mle m2 m3 → mle m1 m3.
Proof.
  unfold mle. intros. unpack. split; [ congruence | lia ].
Qed.

Local Lemma mle_mlt_trans m1 m2 m3 :
  mle m1 m2 → mlt m2 m3 → mlt m1 m3.
Proof.
  unfold mle, mlt. intros. unpack. split; [ congruence | lia ].
Qed.

Local Lemma mlt_mle_incl m1 m2 :
  mlt m1 m2 → mle m1 m2.
Proof.
  unfold mle, mlt. intros. unpack. split; [ congruence | lia ].
Qed.

Local Lemma wf_mlt : well_founded mlt.
Proof.
  eapply wf_projected with (f := mweight); [| eapply Wf_nat.lt_wf ].
  intros m1 m2. unfold mlt. tauto.
Qed.

(* Rocq 9.1: explicitly instantiating [init] is necessary to avoid
   divergence when Rocq type-checks the definition of [traverse]. *)

Local Notation init :=
  (@init bool bool_inhabated).

(* An array that is allocated via [init] is OK. *)

Local Lemma mok_init _n :
  mok (init _n (λ _, false)).
Proof.
  (* We rely on the fact that [inhabitant] at type [bool] happens to
     be [true]. *)
  unfold mok. change true with (inhabitant : bool). eapply default_init.
Qed.

(* The property [ok s] is preserved by the ordering [≤]. *)

Local Lemma ok_slt {s' s} : s' < s → ok s → ok s'.
Proof.
  destruct s', s. unfold slt, mlt, ok. intros. unpack. congruence.
Qed.

Local Lemma ok_sle {s' s} : s' ≤ s → ok s → ok s'.
Proof.
  destruct s', s. unfold sle, mle, ok. intros. unpack. congruence.
Qed.
