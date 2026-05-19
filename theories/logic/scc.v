(* This file contains a proof of correctness of an algorithm that
   produces the strongly connected components of a directed graph.
   The algorithm is attributed by Cormen et al. to Kosaraju and Sharir,
   and this proof is due to Wegener. *)

From Stdlib Require Import Program.Equality. (* [dependent destruction] *)
From stdpp Require Import sets propset.
Local Notation set := propset.
From marble Require Import tactics.
From marble.logic Require Import lists sets relations dfs.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)

(* This is the description of the algorithm, in four lines. *)

Definition scc_description {V} (E : V → V → Prop) (f2 : forest V) :=
  ∃ f1 top,
  (* The set [top] is reverse closed. (It can be the set of all vertices.) *)
  closed (flip E) top ∧
  (* Some forest [f1] is produced by a DFS traversal of the graph. *)
  dfs E ∅ top f1 ∧
  (* The forest [f2] is produced by a DFS traversal of the reverse graph. *)
  dfs (flip E) ∅ top f2 ∧
  (* And the roots of [f2] are visited in the reverse postorder of [f1]. *)
  ordered (rev (postorder f1)) f2.

(* -------------------------------------------------------------------------- *)

(* The property [is_scc_forest f] means that every (toplevel) tree in the
   forest [f] is a strongly connected component. *)

Inductive is_scc_forest (V : Type) (E : V → V → Prop) : forest V → Prop :=
| IsSccForestEmpty:
    is_scc_forest E Empty
| IsSccForestNonEmpty:
    ∀ w ws vs,
    component E w ≡ {[w]} ∪ support ws →
    is_scc_forest E vs →
    is_scc_forest E (NonEmpty w ws vs).

(* We will show that [scc_description f2] implies [is_scc_forest f2].
   This is the theorem [scc_soundness]. *)

(* Furthermore, because [f2] is produced by a full DFS traversal of the graph,
   every vertex must appear in [f2], and no vertex can appear twice. Thus, all
   components appear in [f2], and no component appears twice. *)

(* -------------------------------------------------------------------------- *)

(* We fix a set [V] of vertices and a subset [masked] of vertices that we wish
   to remove, or hide. We define a notion of list equality up to masked
   vertices, [equpto], and a notion of forest compatibility up to masked
   vertices, [filter]. *)

Section Masked.

(* A type of vertices. *)

Variable V : Type.

(* A set of masked vertices. *)

Variable masked : set V.

(* Membership in [masked] must be decidable, as we need to reason by cases
   on [x ∈ masked]. *)

Context {decision : ∀ x, Decision (x ∈ masked)}.

  (* UGLY: the presence of [decision] slows down
     the tactic [set_solver]. *)

(* The predicate [equpto rs1 rs2] means that the lists [rs1] and [rs2] are
   equal provided one is allowed to ignore the masked elements of [rs1]. *)

(* Note: [EqUpToSync] does not require [a ∉ masked]. This makes the
   predicate [equpto] reflexive and non-deterministic. It also causes a
   slight discrepancy between the definitions of [equpto] and [filter].
   This does not seem to be a problem. *)

Inductive equpto : list V → list V → Prop :=
  | EqUpToNil:
      equpto [] []
  | EqUpToSkip:
      ∀ a bs cs,
      a ∈ masked →
      equpto bs cs →
      equpto (a :: bs) cs
  | EqUpToSync:
      ∀ a bs cs,
      equpto bs cs →
      equpto (a :: bs) (a :: cs).

Hint Constructors equpto : equpto.

Local Infix "≃" := equpto (at level 80).

(* The predicate [filter ws vs] means that the masked vertices form a
   prefix of the forest [ws] and, if we remove them, what remains is
   the forest [vs]. *)

Inductive filter : forest V → forest V → Prop :=
  | FilterEmpty:
      filter Empty Empty
  | FilterMasked:
      (* If [w] is masked, it is dropped, and the forest [ws] of its
         children is recursively filtered. *)
      ∀ w ws vs ws' vs',
      w ∈ masked →
      filter ws ws' →
      filter vs vs' →
      filter (NonEmpty w ws vs) (concat ws' vs')
  | FilterVisible:
      (* If [w] is not masked, it is preserved. We require that none of
         its descendants be masked, so that the forest [ws] is preserved. *)
      ∀ w ws vs vs',
      w ∉ masked →
      support ws ## masked →
      filter vs vs' →
      filter (NonEmpty w ws vs) (NonEmpty w ws vs').

Hint Constructors filter : filter.

(* [equpto] is reflexive. *)

Lemma equpto_reflexive: reflexive equpto.
Proof.
  intro xs. induction xs; eauto with equpto.
Qed.

(* [equpto] is transitive. *)

Lemma equpto_transitive: transitive equpto.
Proof.
  intros xs ys zs. intros Hxy. revert zs. revert xs ys Hxy.
  induction 1; induction zs; intros Hyz;
  dependent destruction Hyz; eauto with equpto.
Qed.

(* [equpto] is preserved by list concatenation. *)

Lemma equpto_append xs1 xs2 ys1 ys2 :
  xs1 ≃ xs2 →
  ys1 ≃ ys2 →
  xs1 ++ ys1 ≃ xs2 ++ ys2.
Proof.
  induction 1; simpl; intros; eauto with equpto.
Qed.

Hint Resolve equpto_reflexive equpto_append : equpto.

(* [equpto] is preserved by list reversal. *)

Lemma equpto_rev rs1 rs2 :
  rs1 ≃ rs2 → rev rs1 ≃ rev rs2.
Proof.
  induction 1; simpl; intros.
  { eauto with equpto. }
  { eapply equpto_transitive; [| eassumption ].
    replace (rev bs) with (rev bs ++ @nil V) at 2 by eapply app_nil_r.
    eauto with equpto. }
  { eauto with equpto. }
Qed.

(* If two forests are compatible up to masked vertices, then their
   linearizations are compatible up to masked vertices. *)

Lemma filter_equpto vs ws :
  filter vs ws →
  postorder vs ≃ postorder ws.
Proof.
  induction 1; simpl; intros; rewrite ?postorder_concat;
  eauto with equpto.
Qed.

Hint Resolve equpto_rev filter_equpto : equpto.

(* The property [ordered rs f] is insensitive to the presence in the list
   [rs] of vertices that are not in the support of [f]. *)

Lemma ordered_equpto rs1 f :
  ordered rs1 f →
  ∀ rs2,
  rs1 ≃ rs2 →
  support f ## masked →
  ordered rs2 f.
Proof.
  induction 1; simpl; intros rs2 heq; intros.
  (* OrderedNil *)
  { dependent destruction heq. constructor. }
  (* OrderedSkip *)
  { dependent destruction heq.
    + eauto.
    + econstructor; eauto. }
  (* OrderedRoot *)
  { dependent destruction heq; [ set_solver |].
    eapply OrderedRoot.
    eapply IHordered; [ eauto | set_solver ]. }
Qed.

(* If a forest [vs] lies entirely outside [masked], then it is
   preserved by filtration. In other words, [filter] is reflexive
   outside [masked]. *)

Lemma filter_reflexive vs :
  support vs ## masked →
  filter vs vs.
Proof.
  induction vs; simpl; intros.
  + econstructor.
  + econstructor.
    - set_solver.
    - set_solver.
    - eapply IHvs2. set_solver.
Qed.

(* [filter] is preserved by concatenation. *)

Lemma filter_concat vs1 ws1 :
  filter vs1 ws1 →
  ∀ vs2 ws2,
  filter vs2 ws2 →
  filter (concat vs1 vs2) (concat ws1 ws2).
Proof.
  induction 1; simpl; intros; eauto;
  rewrite <- ?concat_associative;
  eauto with filter.
Qed.

(* The forest produced by [filter] does not contain masked vertices. *)

(* This lemma is currently unused. *)

Lemma filter_support vs ws :
  filter vs ws →
  support ws ## masked.
Proof.
  induction 1; simpl; rewrite ?support_concat; set_solver.
Qed.

(* -------------------------------------------------------------------------- *)

(* We now mask away not only a set of vertices, but also the incoming and
   outgoing edges carried by these vertices. *)

Variable E : V → V → Prop.

(* The relation [E'] represents the remaining edges. *)

(* An edge is removed as soon as either of its endpoints is removed.
   This seems to be required, later on, when we argue that the set
   of masked vertices is closed both ways, i.e., has no incoming or
   outgoing edges. *)

Definition E' v w :=
  E v w ∧ v ∉ masked ∧ w ∉ masked.

Hint Unfold E' : E'.

(* There are fewer edges in [E'] than in [E]. *)

Lemma fewer_edges v w : E' v w → E v w.
Proof. unfold E'. tauto. Qed.

(* A path from [x] to [z] is preserved unless there is a masked
   vertex [y] on this path. *)

Lemma path_preservation x :
  ∀ z,
  path E x z →
  path E' x z ∨
  ∃ y, y ∈ masked ∧ path E x y ∧ path E y z.
Proof.
  (* First, deal with the case where [x] is masked, which is trivial. *)
  (* [decision] is needed here. *)
  case (decide (x ∈ masked)); intro.
  { right. eauto with path. }
  (* Now, re-introduce [x], and perform an induction. *)
  generalize dependent x.
  induction 2.
  (* Base case. *)
  { eauto with path. }
  (* Inductive case. *)
  (* If [y] is masked, we have a masked vertex on the path from [x]
     to [z], and we are done. *)
  case (decide (y ∈ masked)); intro.
  { right. eauto with path. }
  (* Assume now that [y] is not masked. The edge from [x] to [y] is
     preserved. Furthermore, the induction hypothesis is applicable. *)
  destruct IHpath; [ assumption | | unpack ].
  (* Sub-case 1. *)
  { left. eauto with E' path. }
  (* Sub-case 2. *)
  { right. eauto with path. }
Qed.

(* If no vertex in [vs] is masked, then the image of [vs] through [E']
   is its image through [E], minus any masked vertices. *)

(* This lemma is currently unused. *)

Lemma image_preservation vs :
  vs ## masked →
  image E vs ∖ masked ≡ image E' vs.
Proof.
  unfold E'. set_solver.
Qed.

(* If all [E]-edges out of [vs] lead into [ws], then the same is true
   of all [E']-edges out of [vs], and furthermore these edges lead to
   vertices that are not masked. *)

(* This lemma is currently unused. *)

Lemma into_preservation vs ws :
  into E vs ws →
  into E' vs (ws ∖ masked).
Proof.
  unfold E'. set_solver.
Qed.

(* If no vertex in [w/ws] is masked, and if there in an edge in [E]
   from [w] to every root of [ws], then this remains true in [E']. *)

Lemma outof_preservation w ws :
  w ∉ masked →
  support ws ## masked →
  outof E {[w]} (roots ws) →
  outof E' {[w]} (roots ws).
Proof.
  intros hw hws ?.
  generalize (subset_roots_support ws); intro.
  unfold E'. set_solver. (* [image_preservation] *)
Qed.

(* If a DFS of the original graph produces the forest [ws], and if
   filtering out the masked vertices of [ws] yields the forest [ws'],
   then a DFS of the modified graph yields [ws'], as one would expect. *)

(* One might wonder which sets of marked vertices should appear in the
   conclusion of this lemma. In fact, the masked vertices do not matter
   any more, so we can view them as marked or unmarked, as we please. We
   prove two variants of the lemma, namely [dfs_filter_diff] and
   [dfs_filter_union]. *)

(* This lemma is currently unused. *)

Lemma dfs_filter_diff imarked omarked ws :
  dfs E imarked omarked ws →
  ∀ ws',
  filter ws ws' →
  dfs E' (imarked ∖ masked) (omarked ∖ masked) ws'.
Proof.
  induction 1; intros ? hf; dependent destruction hf.
  (* Empty. *)
  { econstructor. set_solver. }
  (* NonEmpty/Masked *)
  { eapply dfs_concat; [ | eauto ].
    (* The first premise requires tweaking; we must argue that [w]
       is masked, hence it does not make any difference whether it
       is marked or unmarked. *)
    dfs1; [ eauto | set_solver ]. }
  (* NonEmpty/Visible *)
  { econstructor.
    + set_solver.
    + dfs1; [ eauto using filter_reflexive | set_solver ].
    + eapply outof_preservation; set_solver.
    + unfold E'. set_solver. (* [into_preservation] *)
    + eauto. }
Qed.

Lemma dfs_filter_union imarked omarked ws :
  dfs E imarked omarked ws →
  ∀ ws',
  filter ws ws' →
  dfs E' (imarked ∪ masked) (omarked ∪ masked) ws'.
Proof.
  (* This lemma used to be proved via [dfs_filter_diff] and
     [dfs_marked_covariant] and [prove_subset_union_diff], which
     requires decidable membership. A direct proof is preferable. *)
  induction 1; intros ? hfilter; dependent destruction hfilter.
  { econstructor. set_solver. }
  { eapply dfs_concat.
    + dfs1. eauto. set_solver.
    + dfs1. eauto. set_solver. }
  { econstructor.
    + set_solver.
    + dfs1. eauto using filter_reflexive. set_solver.
    + eapply outof_preservation; eauto with set_solver.
    + unfold E'. set_solver. (* [into_preservation] *)
    + eauto. }
Qed.

(* This special case of the previous lemma covers the case where every
   masked vertex is initially marked. *)

Lemma dfs_filter_remainder imarked omarked ws :
  dfs E imarked omarked ws →
  masked ⊆ imarked →
  dfs E' imarked omarked ws.
Proof.
  intros. dfs1. dfs2.
  + eapply dfs_filter_union; [ eauto | eapply filter_reflexive ].
    dfs_imarked. set_solver.
  + dfs_monotonic. set_solver.
  + set_solver.
Qed.

(* -------------------------------------------------------------------------- *)

(* We now assume that the masked vertices form a strongly connected
   component. In that case, quite obviously, the remaining components of
   the original graph are exactly the components of the modified graph. *)

(* We assume that there exists some vertex [r]... *)

Variable r : V.

(* ...such that the masked vertices are exactly the component of [r]. *)

Variable hm : masked ≡ component E r.

(* Let us spell out the obvious consequences of this hypothesis. *)

Lemma scc_masked w : w ∈ masked → scc E r w.
Proof. rewrite hm. unfold component. set_unfold. Qed.

Lemma masked_scc w : scc E r w → w ∈ masked.
Proof. rewrite hm. unfold component. set_unfold. Qed.

(* If [w] is unmasked, then its component in [E'] is the same as its
   component in [E]. *)

Lemma scc_preservation w :
  w ∉ masked →
  component E w ≡ component E' w.
Proof.
  (* One inclusion is already known. *)
  intros. eapply subset_antisymmetric;
    [| eauto using component_covariant_E, fewer_edges ].
  (* Consider a point [x] with paths between [w] and [x]. *)
  eapply prove_subset; intros x [ hwx hxw ].
  (* Apply path preservation to these paths. *)
  generalize (path_preservation hwx); intro fwx.
  generalize (path_preservation hxw); intro fxw.
  (* Three cases arise. *)
  destruct fwx; [ destruct fxw | ].
  (* Case 1. The two paths are preserved. Done. *)
  { constructor; eauto. }
  (* Case 2. The path of [x] to [w] hits a masked vertex [y]. This vertex
     is a member of [r]'s component, hence [w] must also be a member of
     [r]'s component, hence [w] must be masked. Contradiction. *)
  { exfalso. unpack.
    cut (w ∈ masked); [ tauto |].
    eauto 7 using scc_masked, masked_scc with scc path. }
  (* Case 3. Symmetric. *)
   { exfalso. unpack.
    cut (w ∈ masked); [ tauto |].
    eauto 7 using scc_masked, masked_scc with scc path. }
Qed.

(* Thus, an SCC forest for [E'] is an SCC forest for [E]. *)

Lemma is_scc_forest_inclusion f :
  is_scc_forest E' f →
  support f ## masked →
  is_scc_forest E f.
Proof.
  induction 1 as [| w ? ? heq h IH ]; simpl; constructor.
  + rewrite <- heq. eapply scc_preservation.
    clear decision; set_solver.
  + eapply IH. clear decision; set_solver.
Qed.

(* If the vertex [r] reaches the (roots of the) forest [vs], then the
   strongly connected component of [r] forms a prefix of the forest
   [vs]. Thus, there exists a forest [ws] obtained by filtering away
   this component. *)

Lemma filter_scc imarked omarked vs :
  dfs E imarked omarked vs →
  reaches E {[r]} (support vs) →
  ∃ ws,
  filter vs ws.
Proof.
  (* The beginning of the proof is administrative. *)
  induction 1; simpl; intros.
  (* Empty. *)
  { eauto with filter. }
  (* NonEmpty. *)
  edestruct IHdfs2 as (vs' & ?).
  { clear decision; set_solver. }
  clear IHdfs2.
  (* [decision] is used here again. *)
  case (decide (w ∈ masked)); intro.
  (* Case: [w] is masked. *)
  { edestruct IHdfs1 as (ws' & ?).
    { clear decision; set_solver. }
    clear IHdfs1.
    eauto with filter. }
  (* Case: [w] is not masked. *)
  clear IHdfs1. clear decision.
  eexists.
  eapply FilterVisible; [ eauto | | eauto ].
  (* Here comes the key argument. If [w] is not part of [scc E r],
     then none of its descendants in the forest is part of it. *)
  (* Assume, by way of contradiction, that [x] is part of [support ws]
     and is part of [component E r]. *)
  rewrite hm.
  eapply prove_disjoint. intros x ? ?.
  (* Then, there is a path from [r] to [w] to [x] to [r]. *)
  assert (reaches E {[r]} {[w]}) by set_solver.
  assert (reaches E {[w]} {[x]}) by eauto using reaches_root_descendants with dfs.
  assert (reaches E {[x]} {[r]}) by set_solver.
  rewrite reaches_singleton_singleton in *.
  (* Hence, [w] must be part of [component E r]. Contradiction. *)
  cut (w ∈ masked); [ tauto |].
  rewrite hm.
  elem in *. unfold scc in *.
  intuition eauto with path.
Qed.

(* In the particular case where the distinguished vertex [r] is the last
   root of the forest, the same can be said. *)

Lemma filter_last_scc imarked omarked ws vs :
  dfs E imarked omarked (concat vs (NonEmpty r ws Empty)) →
  closed E imarked →
  closed (flip E) omarked →
  ∃ ws',
  filter (concat vs (NonEmpty r ws Empty)) (concat vs ws').
Proof.
  (* The proof consists in applying [filter_reflexive] to the forest [vs]
     and applying [filter_scc] to the tree [w/ws]. *)
  intros Hdfs ? ?.
  generalize Hdfs;
  intros (mmarked & Hdfs1 & Hdfs2)%dfs_concat_inversion.
  edestruct filter_scc.
  { eauto. }
  { simpl. eauto using reaches_root_support with reaches. }
  eexists.
  eapply filter_concat; [ | eauto ].
  eapply filter_reflexive.
  (* We must check that [vs] is disjoint with the component of [r].
     This follows from [bound_scc] and [dfs_disjoint_concat]. *)
  rewrite hm.
  forwards: (bound_scc Hdfs2).
  { eauto using dfs_closed with closed. }
  { assumption. }
  eapply dfs_disjoint_concat in Hdfs. simpl in Hdfs.
  clear decision; set_solver.
Qed.

End Masked.

(* -------------------------------------------------------------------------- *)

(* The operation of masking vertices commutes with the operation of
   reversing the graph edges. *)

Lemma reverse_masked {V} (E : V → V → Prop) masked v w :
  flip (E' masked E) v w ↔ E' masked (flip E) v w.
Proof.
  unfold flip, E'. tauto.
Qed.

Lemma reverse_masked_equiv  {V} (E : V → V → Prop) masked :
  relation_equivalence
    (flip (E' masked E))
    (E' masked (flip E)).
Proof.
  repeat intro. eapply reverse_masked.
Qed.

(* -------------------------------------------------------------------------- *)

(* Here is the main lemma in the proof of soundness of the algorithm. *)

Lemma scc_soundness_main_lemma `{EqDecision V} :
  ∀ f2,
  ∀ E : V → V → Prop,
  ∀ top : set V,
  closed (flip E) top →
  ∀ masked,
  (* The masked vertices have been removed from the graph. They
     probably have no outgoing or incoming edges. For now, we only
     assume that [masked] is closed, both ways. This implies that
     it is impossible to enter or leave this set by following an edge. *)
  closed E masked →
  closed (flip E) masked →
  ∀ f1,
  dfs E masked top f1 →
  dfs (flip E) masked top f2 →
  ordered (rev (postorder f1)) f2 →
  is_scc_forest E f2.
Proof.
  (* As proposed by Wegener, the proof is by induction on the forest [f2]. *)
  induction f2 as [| root2 sons2 _ tail2 IHtail2 ];
  intros E top ? masked hclosed1 hclosed2 f1 hdfs1 hdfs2 ho;
  dependent destruction hdfs2.

  (* Case: [f2] is empty. The result is immediate. *)
  { constructor. }

  (* Case: [f2] is non-empty. *)
  rename imarked into masked.
  rename omarked into top.
  dependent destruction ho.

  (* Sub-case: the reverse post-order of [f1] begins with a vertex [r]
     which is not in the support of [f2]. However, we know that the
     support of [f1] and the support of [f2] coincide. Contradiction! *)
  { exfalso.
    forwards hrf1: member_last_root_support.
    { eauto. }
    forwards hc: @dfs_same_support.
    { eexact hdfs1. }
    { eapply DFSNonEmpty; eauto. }
    rewrite hc in hrf1.
    tauto. }

  (* Sub-case: the root [root2] of the first tree in [f2] is also the head
     of the reverse post-order of [f1]. Hence, [f1] is non-empty and
     [root2] is the root of its last tree. *)
  edestruct isolate_last_tree as (sons1 & head1 & ?). eauto. subst f1.
  (* We note that the forest [tail2] is disjoint with the tree
    [root2/sons2]. *)
  forwards: dfs_disjoint. econstructor; eauto.
  (* We know that the component of [root2] is its reverse closure. *)
  forwards fact1: (last_scc hdfs1 hclosed1).
  { set_solver. }
  (* Hence, it is the very first tree of the forest [f2]. *)
  forwards fact2: exact_closure.
  { econstructor; eauto. }
  { assumption. }
  { assumption. }
  (* Furthermore, this component forms a prefix of the last tree of [f1],
     that is, of the tree [root2/sons1]. In fact, it forms a prefix of
     the forest [f1] as a whole. *)
  set (masked' := component E root2).
  fold masked' in fact1.
  assert (fact: masked' ≡ {[root2]} ∪ support sons2).
  { by rewrite fact1, fact2. }
  clear fact1 fact2.
  assert (decision: ∀ v, Decision (v ∈ masked')).
  { intro v.
    eapply Decision_membership_in_finite_set
      with (xs := {[root2]} ++ supportl sons2).
    rewrite fact. rewrite <- list_to_set_supportl. set_solver. }
  edestruct (@filter_last_scc V masked') as (f1' & ?).
  { exact decision. }
  { unfold masked'. reflexivity. }
  { eexact hdfs1. }
  { eauto with closed. }
  { assumption. }
  (* We now consider a smaller graph, where the vertices of [scc root2]
     are removed. We argue that, with respect to this smaller graph,
     we still have a DFS forest [f1'], obtained from [f1] by removing
     these vertices. This follows from the previous remark. *)
  forwards hdfs1': dfs_filter_union.
  { exact hdfs1. }
  { eassumption. }
  (* We have met part of the goal. There remains to use the induction
     hypothesis in order to prove that [tail2] is an SCC forest. *)
  constructor.
  { fold masked'. exact fact. }
  eapply is_scc_forest_inclusion with (masked := masked'); [
    exact decision
  | unfold masked'; reflexivity
   | (* open *)
   | rewrite fact; assumption
  ].
  (* Let us now apply the induction hypothesis to a smaller graph. We wish
     to exclude the vertices in [scc root2]. *)
  eapply IHtail2 with (top := top) (masked := union masked masked').
  (* Premise 1. [top] is still closed. *)
  { unfold E'. intros w (v & ?). unpack. clear decision; set_solver. }
  (* Premise 2. The new set of masked vertices is still closed. *)
  { unfold E'. intros w (v & ?). unpack. clear decision; set_solver. }
  (* Premise 3. The new set of masked vertices is still reverse closed. *)
  { unfold E', flip. intros v (w & ?). unpack. clear decision; set_solver. }
  (* Premise 4. *)
  { dfs2. eexact hdfs1'.
    assert (root2 ∈ top).
    { dfs_monotonic. clear decision; set_solver. }
    assert (support sons2 ⊆ top).
    { apply dfs_omarked in hdfs2_1. dfs_monotonic.
      clear decision; set_solver. }
    clear decision; set_solver. }
  (* Premise 6. We have a valid DFS over [tail2]. *)
  { rewrite reverse_masked_equiv.
    eapply dfs_filter_remainder; [| clear decision; set_solver ].
    rewrite fact, union_assoc.
    eauto using dfs_second_premise_reformulation. }
  (* Premise 7. Requires reasoning about [ordered]. *)
  { eapply ordered_equpto.
    + eapply OrderedSkip with (r := root2).
      clear decision; set_solver. eauto.
    + match goal with h: {[_]} ++ _ = _ |- _ => rewrite h end.
      eauto using equpto_rev, filter_equpto.
    + rewrite fact. assumption. }
  (* Phew... *)
Qed.

(* This theorem states that if the forest [f2] has been constructed via
   Kosaraju and Sharir's algorithm then it is an SCC forest. In other
   words, this algorithm is correct. *)

Lemma scc_soundness `{EqDecision V} (E : V → V → Prop) f2 :
  scc_description E f2 →
  is_scc_forest E f2.
Proof.
  unfold scc_description. intros. unpack.
  eapply scc_soundness_main_lemma; eauto using prove_image_empty.
Qed.
