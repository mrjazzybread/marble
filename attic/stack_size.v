Local Lemma marked_bound marked σ :
  wf (marked, σ) →
  marked ⊆ universe.
Proof.
  intros Hwf.
  generalize (wf_reaches Hwf eq_refl); intro Hreaches.
  generalize closure_start_subset_universe; intro.
  set_solver.
Qed.

Axiom funiverse : listset_nodup.listset_nodup vertex.
Axiom fequiv_univ : fequiv universe funiverse.
Axiom size_funiverse: Z.of_nat (base.size funiverse) = n.

Local Lemma length_stack marked σ :
  wf (marked, σ) →
  len σ ≤ n + 1.
Proof using.
  intros Hwf.
  generalize (wf_trace_marked Hwf eq_refl); intro Htrace.
  generalize (length_stack Hwf eq_refl); intros (fvs & Hfequiv & Hsize).
  cut (Z.of_nat (base.size fvs) ≤ n).
  { unfold len. lia. }
  clear Hsize.
  assert (Huniv: trace σ ⊆ universe).
  { apply marked_bound in Hwf. set_solver. }
  clear Htrace.
  assert (fvs ⊆ funiverse).
  { admit. }
  rewrite <- size_funiverse.
  apply inj_le.
  apply fin_sets.subseteq_size.
  assumption.
Admitted. (* TODO *)
