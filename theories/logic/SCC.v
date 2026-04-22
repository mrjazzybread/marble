(* This library contains a proof of correctness of an algorithm that
   produces the strongly connected components of a directed graph.
   The algorithm is attributed by Cormen et al. to Kosaraju and Sharir,
   and this proof is due to Wegener. *)

Set Implicit Arguments.
From Stdlib Require Import Program.Equality.
From marble.logic Require Import MyTactics.
From marble.logic Require Import MySets.
From marble.logic Require Import MyRelations.
From marble.logic Require Import MyLists.
From marble.logic Require Import DFS.

(* ---------------------------------------------------------------------------- *)

(* This is the description of the algorithm, in three lines. *)

Definition scc_description
  (V : Type)
  (E : V -> V -> Prop)
  (f2 : forest V) :=

    exists f1,
    (* Some forest [f1] is produced by a DFS traversal of the graph. *)
    dfs E empty_ universe_ f1 /\
    (* The forest [f2] is produced by a DFS traversal of the reverse graph. *)
    dfs (reverse E) empty_ universe_ f2 /\
    (* And the roots of [f2] are visited in the reverse postorder of [f1]. *)
    ordered (rev (postorder f1)) f2.

(* ---------------------------------------------------------------------------- *)

(* The property [is_scc_forest f] means that every (toplevel) tree in the
   forest [f] is a strongly connected component. *)

Inductive is_scc_forest (V : Type) (E : V -> V -> Prop) : forest V -> Prop :=
| IsSccForestEmpty:
    is_scc_forest E (Empty _)
| IsSccForestNonEmpty:
    forall w ws vs,
    scc E w = insert w (support ws) ->
    is_scc_forest E vs ->
    is_scc_forest E (NonEmpty w ws vs).

(* We will show that [scc_description f2] implies [is_scc_forest f2]. This is
   the theorem [scc_soundness]. *)

(* Furthermore, because [f2] is produced by a full DFS traversal of the graph,
   every vertex must appear in [f2], and no vertex can appear twice. Thus, all
   components appear in [f2], and no component appears twice. *)

(* ---------------------------------------------------------------------------- *)

(* We fix a set [V] of vertices and a subset [masked] of vertices that we wish
   to remove, or hide. We define a notion of list equality up to masked
   vertices, [equpto], and a notion of forest compatibility up to masked
   vertices, [filter]. *)

Section Masked.

  (* A type of vertices. *)

  Variable V : Type.

  (* A set of masked vertices. *)

  Variable masked : set V.

  (* The predicate [equpto rs1 rs2] means that the lists [rs1] and [rs2] are
     equal provided one is allowed to ignore the masked elements of [rs1]. *)

  (* Note: [EqUpToSync] does not require [~ member a masked]. This makes the
     predicate [equpto] reflexive and non-deterministic. It also causes a
     slight discrepancy between the definitions of [equpto] and [filter].
     This does not seem to be a problem. *)

  Inductive equpto : list V -> list V -> Prop :=
    | EqUpToNil:
        equpto (@nil _) (@nil _)
    | EqUpToSkip:
        forall a bs cs,
        member a masked ->
        equpto bs cs ->
        equpto (a :: bs) cs
    | EqUpToSync:
        forall a bs cs,
        equpto bs cs ->
        equpto (a :: bs) (a :: cs).

  Hint Constructors equpto : equpto.

  (* The predicate [filter ws vs] means that the masked vertices form a
     prefix of the forest [ws] and, if we remove them, what remains is
     the forest [vs]. *)

  Inductive filter : forest V -> forest V -> Prop :=
    | FilterEmpty:
        filter (Empty _) (Empty _)
    | FilterMasked:
        (* If [w] is masked, it is dropped, and the forest [ws] of its
           children is recursively filtered. *)
        forall w ws vs ws' vs',
        member w masked ->
        filter ws ws' ->
        filter vs vs' ->
        filter (NonEmpty w ws vs) (concat ws' vs')
    | FilterVisible:
        (* If [w] is not masked, it is preserved. We require that none of
           its descendants be masked, so that the forest [ws] is preserved. *)
        forall w ws vs vs',
        ~ member w masked ->
        subset (support ws) (complement masked) ->
        filter vs vs' ->
        filter (NonEmpty w ws vs) (NonEmpty w ws vs').

  Hint Constructors filter : filter.

  (* [equpto] is reflexive. *)

  Lemma equpto_reflexive:
    reflexive equpto.
  Proof.
    intro xs. induction xs; eauto with equpto.
  Qed.

  (* [equpto] is transitive. *)

  Lemma equpto_transitive:
    transitive equpto.
  Proof.
    intros xs ys zs. intros Hxy. revert zs. revert xs ys Hxy.
    induction 1; induction zs; intros Hyz;
    dependent destruction Hyz; eauto with equpto.
  Qed.

  (* [equpto] is preserved by list concatenation. *)

  Lemma equpto_append:
    forall xs1 xs2 ys1 ys2,
    equpto xs1 xs2 ->
    equpto ys1 ys2 ->
    equpto (xs1 ++ ys1) (xs2 ++ ys2).
  Proof.
    induction 1; simpl; intros; eauto with equpto.
  Qed.

  Hint Resolve equpto_reflexive equpto_append : equpto.

  (* [equpto] is preserved by list reversal. *)

  Lemma equpto_rev:
    forall rs1 rs2,
    equpto rs1 rs2 ->
    equpto (rev rs1) (rev rs2).
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

  Lemma filter_equpto:
    forall vs ws,
    filter vs ws ->
    equpto (postorder vs) (postorder ws).
  Proof.
    induction 1; simpl; intros; rewrite ?postorder_concat;
    eauto with equpto.
  Qed.

  Hint Resolve equpto_rev filter_equpto : equpto.

  (* The property [ordered rs f] is insensitive to the presence in the list
     [rs] of vertices that are not in the support of [f]. *)

  Lemma ordered_equpto:
    forall rs1 f,
    ordered rs1 f ->
    forall rs2,
    equpto rs1 rs2 ->
    subset (support f) (complement masked) ->
    ordered rs2 f.
  Proof.
    induction 1; simpl; intros rs2 heq; intros; simplify_sets.
    (* OrderedNil *)
    { dependent destruction heq. constructor. }
    (* OrderedSkip *)
    { dependent destruction heq.
      + eauto.
      + econstructor; eauto. }
    (* OrderedRoot *)
    { dependent destruction heq; [ mysets | ].
      eapply OrderedRoot. eauto. }
  Qed.

  (* If a forest [vs] lies entirely outside [masked], then it is preserved
     by filtration. In other words, [filter] is reflexive outside [masked]. *)

  Lemma filter_reflexive:
    forall vs,
    subset (support vs) (complement masked) ->
    filter vs vs.
  Proof.
    induction vs; simpl; intros; simplify_sets; eauto with filter.
  Qed.

  (* [filter] is preserved by concatenation. *)

  Lemma filter_concat:
    forall vs1 ws1,
    filter vs1 ws1 ->
    forall vs2 ws2,
    filter vs2 ws2 ->
    filter (concat vs1 vs2) (concat ws1 ws2).
  Proof.
    induction 1; simpl; intros; eauto;
    rewrite <- ?concat_associative;
    eauto with filter.
  Qed.

  (* The forest produced by [filter] does not contain any masked vertices. *)

  Lemma filter_support:
    forall vs ws,
    filter vs ws ->
    subset (support ws) (complement masked).
  Proof.
    induction 1; simpl; rewrite ?support_concat; eauto with mysets.
  Qed.

(* ---------------------------------------------------------------------------- *)

(* We now mask away not only a set of vertices, but also the incoming and
   outgoing edges carried by these vertices. *)

  Variable E : V -> V -> Prop.

  (* The relation [E'] represents the remaining edges. *)

  (* An edge is removed as soon as either of its endpoints is removed. This
     seems to be required, later on, when we argue that the set of masked
     vertices is closed both ways, i.e., has no incoming or outgoing edges. *)

  Definition E' v w :=
    E v w /\ ~ member v masked /\ ~ member w masked.

  Hint Unfold E' : E'.

  (* There are fewer edges in [E'] than in [E]. *)

  Lemma fewer_edges:
    forall v w,
    E' v w ->
    E v w.
  Proof.
    unfold E'. tauto.
  Qed.

  (* Hence, if a set is closed with respect to [E], then it is also closed
     with respect to [E']. *)

  Lemma still_closed:
    forall vs,
    closed E vs ->
    closed E' vs.
  Proof.
    generalize (into_contravariant_E fewer_edges). eauto.
  Qed.

  (* The set [masked] is closed with respect to [E'] and [reverse E']. This is
     due to the fact that a masked vertex has no incoming or outgoing edges. *)

  Lemma image_masked_direct:
    into E' masked empty_.
  Proof.
    eapply prove_into_empty. unfold E'. tauto.
  Qed.

  Lemma image_masked_reverse:
    into (reverse E') masked empty_.
  Proof.
    eapply prove_into_empty. unfold reverse, E'. tauto.
  Qed.

  (* The target of an [E'] edge is never masked. *)

  Lemma into_complement_masked:
    forall vs,
    into E' vs (complement masked).
  Proof.
    intros. eapply prove_subset; intros; simplify_sets.
    unfold E' in *. intuition eauto with mysets.
  Qed.

  (* A path from [x] to [z] is preserved, unless there is a masked vertex [y]
     on this path. *)

  Lemma path_preservation:
    forall x z,
    path E x z ->
    path E' x z \/
    exists y, member y masked /\ path E x y /\ path E y z.
  Proof.
    (* First, deal with the case where [x] is masked, which is trivial. *)
    intro x.
    destruct (classic (member x masked)).
    { right. eauto with path. }
    (* Now, re-introduce [x], and perform an induction. *)
    generalize dependent x.
    induction 2.
    (* Base case. *)
    { eauto with path. }
    (* Inductive case. *)
    (* If [y] is masked, we have a masked vertex on the path from [x]
       to [z], and we are done. *)
    destruct (classic (member y masked)).
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
     is its image through [E], minus any masked vertices. The following
     two lemmas prove one inclusion each. *)

  Lemma image_preservation_1:
    forall vs,
    subset vs (complement masked) ->
    subset
      (diff (image E vs) masked)
      (image E' vs).
  Proof.
    intros. eapply prove_subset. intros. simplify_sets.
    eapply prove_member_image. eauto.
    repeat split.
    + eauto.
    + mysets.
    + eauto.
  Qed.

  Lemma image_preservation_2:
    forall vs,
    subset
      (image E' vs)
      (diff (image E vs) masked).
  Proof.
    generalize (into_contravariant_E fewer_edges).
    eauto using into_complement_masked with mysets.
  Qed.

  (* If all [E]-edges out of [vs] lead into [ws], then the same is true
     of all [E']-edges out of [vs], and furthermore these edges lead to
     vertices that are not masked. *)

  Lemma into_preservation:
    forall vs ws,
    into E vs ws ->
    into E' vs (diff ws masked).
  Proof.
    eauto using image_preservation_2 with st mysets.
  Qed.

  (* If no vertex in [w/ws] is masked, and if there in an edge in [E] from [w]
     to every root of [ws], then this remains true in [E']. *)

  Lemma outof_preservation:
    forall w ws,
    member w (complement masked) ->
    subset (support ws) (complement masked) ->
    outof E (singleton w) (roots ws) ->
    outof E' (singleton w) (roots ws).
  Proof.
    intros.
    eapply subset_transitive; [ | eapply image_preservation_1; eauto ].
    eauto 3 using subset_roots_support with st mysets.
  Qed.

  (* If a DFS of the original graph produces the forest [ws], and if filtering
     out the masked vertices of [ws] yields the forest [ws'], then a DFS of the
     modified graph yields [ws'], as one would expect. *)

  (* One might wonder which sets of marked vertices should appear in the
     conclusion of this lemma. In fact, the masked vertices do not matter any
     more, so we can view them as marked or unmarked, as we please. We prove
     two variants of the lemma, namely [dfs_filter_diff] and
     [dfs_filter_union]. *)

  Lemma dfs_filter_diff:
    forall imarked omarked ws,
    dfs E imarked omarked ws ->
    forall ws',
    filter ws ws' ->
    dfs E' (diff imarked masked) (diff omarked masked) ws'.
  Proof.
    induction 1; intros ? hf; dependent destruction hf.
    (* Empty. *)
    { econstructor. }
    (* NonEmpty/Masked *)
    { eapply dfs_concat; [ | eauto ].
      (* The first premise requires tweaking; we must argue that [w]
         is masked, hence it does not make any difference whether it
         is marked or unmarked. *)
      dfs1; [ eauto | eapply subset_antisymmetric ].
      + eauto using prove_subset_intersection_left with mysets.
      + eauto with mysets. }
    (* NonEmpty/Visible *)
    { econstructor.
      + eauto using prove_not_member_via_subset with mysets.
      + dfs1; [ eauto using filter_reflexive | eapply subset_antisymmetric ].
        - mysets.
        - eauto 7 with mysets.
      + eapply outof_preservation; eauto with mysets.
      + eapply into_preservation; eauto.
      + eauto. }
  Qed.

  Lemma dfs_filter_union:
    forall imarked omarked ws ws',
    dfs E imarked omarked ws ->
    filter ws ws' ->
    dfs E' (union imarked masked) (union omarked masked) ws'.
  Proof.
    (* This lemma could be proved via a direct induction, but we prefer to
       view it as a corollary of [dfs_filter_diff] and [dfs_marked_covariant]. *)
    intros. dfs1. dfs2.
    + eapply dfs_marked_covariant;
        eauto using dfs_filter_diff, filter_support.
    + eapply subset_antisymmetric;
        eauto using prove_subset_union_diff with mysets.
    + eapply subset_antisymmetric;
        eauto using prove_subset_union_diff with mysets.
  Qed.

  (* This special case of the above lemma covers the case where every masked
     vertex is initially marked. *)

  Lemma dfs_filter_remainder:
    forall imarked omarked ws,
    dfs E imarked omarked ws ->
    subset masked imarked ->
    dfs E' imarked omarked ws.
  Proof.
    intros. dfs1. dfs2.
    + eapply dfs_filter_union.
      - eauto.
      - eapply filter_reflexive. eauto using dfs_imarked with st mysets.
    + eapply subset_antisymmetric;
        eauto using dfs_monotonic with st mysets.
    + eauto with mysets.
  Qed.

  (* The previous lemma could also have been proven directly, instead of as
     a corollary of [dfs_filter_*], as follows. I keep this proof, for the
     record, because it is cool. *)

  Goal
    forall imarked omarked ws,
    dfs E imarked omarked ws ->
    subset (support ws) (complement masked) ->
    dfs E' imarked omarked ws.
  Proof.
    generalize (image_covariant_E _ fewer_edges); intro.
    induction 1; simpl; intros; simplify_sets; econstructor;
    eauto 3 using outof_preservation with st mysets.
  Qed.

(* ---------------------------------------------------------------------------- *)

(* We now assume that the masked vertices form a strongly connected component.
   In that case, quite obviously, the remaining components of the original
   graph are exactly the components of the modified graph. *)

  (* We assume that there exists some vertex [r]... *)

  Variable r : V.

  (* ...such that the masked vertices are exactly the component of [r]. *)

  Variable hm : masked = scc E r.

  (* Let us spell out the obvious consequences of this hypothesis. *)

  Lemma scc_masked:
    forall w,
    member w masked ->
    scc E r w.
  Proof.
    rewrite hm. intros. eapply use_member. eauto.
  Qed.

  Lemma masked_scc:
    forall w,
    scc E r w ->
    member w masked.
  Proof.
    rewrite hm. intros. eapply prove_member. eauto.
  Qed.

  (* If [w] is unmasked, then its component in [E'] is the same as its component
     in [E]. *)

  Lemma scc_preservation:
    forall w,
    ~ member w masked ->
    scc E w = scc E' w.
  Proof.
    (* One inclusion is already known. *)
    intros. eapply subset_antisymmetric; [ | eauto using scc_covariant_E, fewer_edges ].
    (* Consider a point [x] with paths between [x] and [x]. *)
    eapply prove_subset_directly; intros x [ hwx hxw ].
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
      eauto 8 using contradiction, scc_masked, masked_scc with scc path. }
    (* Case 3. Symmetric. *)
     { exfalso. unpack.
       eauto 8 using contradiction, scc_masked, masked_scc with scc path. }
  Qed.

  (* Thus, an SCC forest for [E'] is an SCC forest for [E]. *)

  Lemma is_scc_forest_inclusion:
    forall f,
    is_scc_forest E' f ->
    subset (support f) (complement masked) ->
    is_scc_forest E f.
  Proof.
    induction 1 as [| ? ? ? heq h ih ]; simpl; constructor;
    simplify_sets; eauto with mysets.
    rewrite <- heq.
    eauto using scc_preservation.
  Qed.

  (* If the vertex [r] reaches the (roots of the) forest [vs], then the strongly
     connected component of [r] forms a prefix of the forest [vs]. Thus, there
     exists a forest [ws] obtained by filtering away this component. *)

  Lemma filter_scc:
    forall imarked omarked vs,
    dfs E imarked omarked vs ->
    reaches E (singleton r) (support vs) ->
    exists ws,
    filter vs ws.
  Proof.
    (* The beginning of the proof is administrative. *)
    induction 1; simpl; intros.
    (* Empty. *)
    { eauto with filter. }
    (* NonEmpty. *)
    edestruct IHdfs2 as (vs' & ?). eauto with st mysets. clear IHdfs2.
    destruct (classic (member w masked)).
    (* Case: [w] is masked. *)
    { edestruct IHdfs1 as (ws' & ?). eauto with st mysets. clear IHdfs1.
      eauto with filter. }
    (* Case: [w] is not masked. *)
    clear IHdfs1.
    eexists.
    eapply FilterVisible; [ eauto | | eauto ].
    (* Here comes the key argument. If [w] is not part of [scc E r],
       then none of its descendants in the forest is part of it. *)
    (* Assume, by way of contradiction, that [x] is part of [support ws]
       and is part of [scc E r]. *)
    eapply prove_subset. intros x ?.
    eapply prove_member_complement.
    rewrite hm. intro.
    (* Then, there is a path from [r] to [w] to [x] to [r]. *)
    assert (reaches E (singleton r) (singleton w))
      by eauto with st mysets.
    assert (reaches E (singleton w) (singleton x))
      by eauto using reaches_root_support with st mysets dfs.
    assert (reaches E (singleton x) (singleton r)).
    { eapply prove_reaches_singleton_singleton.
      eapply use_scc_right. eapply use_member. eauto. }
    (* Hence, [w] must be part of [scc E r]. Contradiction. *)
    assert (member w masked).
    { rewrite hm.
      eapply prove_member.
      eauto 6 using use_reaches_singleton_singleton, reaches_transitive
        with scc. }
    tauto.
  Qed.

  (* In the particular case where the distinguished vertex [r] is the last
     root of the forest, the same can be said. *)

  Lemma filter_last_scc imarked ws vs :
    dfs E imarked universe_ (concat vs (NonEmpty r ws (Empty _))) ->
    closed E imarked ->
    exists ws',
    filter (concat vs (NonEmpty r ws (Empty _))) (concat vs ws').
  Proof.
    (* The proof consists in applying [filter_reflexive] to the forest [vs]
       and applying [filter_scc] to the tree [w/ws]. *)
    intros Hdfs ?.
    generalize Hdfs;
    intros (mmarked & Hdfs1 & Hdfs2)%dfs_concat_inversion.
    edestruct filter_scc.
    { eauto. }
    { simpl. eauto using reaches_root_support with reaches. }
    eexists.
    eapply filter_concat; [ | eauto ].
    eapply filter_reflexive.
    (* We must check that [vs] is disjoint with the component of [r]. This
       follows from [bound_scc]. *)
    eapply contrapose_subset_complement_right.
    rewrite hm.
    eapply subset_transitive; [
      eapply bound_scc; eauto using dfs_closed with closed | ].
    eapply dfs_disjoint_concat in Hdfs.
    eapply subset_transitive; [ | exact Hdfs ].
    simpl. eauto 10 with mysets.
  Qed.

End Masked.

(* ---------------------------------------------------------------------------- *)

(* The operation of masking some vertices commutes with the operation of
   reversing the graph edges. *)

Lemma reverse_masked:
  forall V : Type,
  forall E : V -> V -> Prop,
  forall masked : set V,
  reverse (E' masked E) = E' masked (reverse E).
Proof.
  unfold reverse, E'. intros.
  extensionality v. extensionality w.
  eapply prop_ext. tauto.
Qed.

(* ---------------------------------------------------------------------------- *)

(* Here is the main lemma in the proof of soundness of the algorithm. *)

Lemma scc_soundness_main_lemma {V} :
  forall f2,
  forall E : V -> V -> Prop,
  forall masked,
  (* The masked vertices have been removed from the graph. They
     probably have no outgoing or incoming edges. For now, we only
     assume that [masked] is closed, both ways. This implies that
     it is impossible to enter or leave this set by following an edge. *)
  closed (path E) masked ->
  closed (path (reverse E)) masked ->
  forall f1,
  dfs E masked universe_ f1 ->
  dfs (reverse E) masked universe_ f2 ->
  ordered (rev (postorder f1)) f2 ->
  is_scc_forest E f2.
Proof.
  (* As proposed by Wegener, the proof is by induction on the forest [f2]. *)
  induction f2 as [| root2 sons2 _ tail2 IHtail2 ];
  intros E masked hclosed1 hclosed2 f1 hdfs1 hdfs2 ho;
  dependent destruction hdfs2.

  (* Case: [f2] is empty. The result is immediate. *)
  { constructor. }

  (* Case: [f2] is non-empty. *)
  dependent destruction ho.

  (* Sub-case: the reverse post-order of [f1] begins with a vertex [r]
     which is not in the support of [f2]. However, we know that the
     support of [f1] and the support of [f2] coincide. Contradiction! *)
  { exfalso.
    forwards hrf1: member_last_root_support.
    { eauto. }
    forwards hc: dfs_same_support.
    { eexact hdfs1. }
    { econstructor; eauto. }
    rewrite hc in hrf1.
    tauto. }

  (* Sub-case: the root [root2] of the first tree in [f2] is also the head
     of the reverse post-order of [f1]. Hence, [f1] is non-empty and [root2]
     is the root of its last tree. *)
  edestruct isolate_last_tree as (sons1 & head1 & ?). eauto. subst f1.
  (* We note that the forest [tail2] is disjoint with the tree [root2/sons2]. *)
  forwards: dfs_disjoint. econstructor; eauto.
  (* We know that the component of [root2] is its reverse closure. *)
  forwards fact1: (last_scc hdfs1 hclosed1).
  (* Hence, it is the very first tree of the forest [f2]. *)
  forwards fact2: exact_closure.
  { econstructor; eauto. }
  { eauto. }
  { eapply prove_closed_path_complement; eauto. }
  (* Furthermore, this component forms a prefix of the last tree of [f1],
     that is, of the tree [root2/sons1]. In fact, it forms a prefix of
     the forest [f1] as a whole. *)
  edestruct filter_last_scc as (f1' & ?).
  { reflexivity. }
  { eexact hdfs1. }
  { eauto with closed. }
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
  { congruence. }
  eapply is_scc_forest_inclusion with (masked := scc E root2); [
    reflexivity | | rewrite fact1; rewrite fact2; assumption
  ].
  (* Let us now apply the induction hypothesis to a smaller graph. We wish
     to exclude the vertices in [scc root2]. *)
  eapply IHtail2 with (masked := union imarked (scc E root2)).
  (* Premise 1. The new set of masked vertices is still closed. *)
  { eapply closed_E_closed_path.
    eapply prove_closed_union.
    eapply still_closed. eauto with closed.
    eauto using image_masked_direct with st mysets. }
  (* Premise 2. The new set of masked vertices is still reverse closed. *)
  { eapply closed_E_closed_path.
    eapply prove_closed_union.
    rewrite reverse_masked. eapply still_closed. eauto with closed.
    eauto using image_masked_reverse with st mysets. }
  (* Premise 3. *)
  { dfs2. eexact hdfs1'. eauto with mysets. }
  (* Premise 4. We have a valid DFS over [tail2]. *)
  { rewrite reverse_masked.
    eapply dfs_filter_remainder.
    + rewrite fact1, fact2. eauto using dfs_second_premise_reformulation.
    + eauto with mysets. }
  (* Premise 5. Requires reasoning about [ordered]. *)
  { eapply ordered_equpto.
    + eapply OrderedSkip.
      mysets (* this instantiates (1 := root2) *).
      eassumption.
    + match goal with h: _ :: _ = _ |- _ => rewrite h end.
      eauto using equpto_rev, filter_equpto.
    + rewrite fact1, fact2. assumption. }
  (* Phew... *)
Qed.

Lemma scc_soundness:
  forall V : Type,
  forall E : V -> V -> Prop,
  forall f2,
  scc_description E f2 ->
  is_scc_forest E f2.
Proof.
  unfold scc_description. intros. unpack.
  eapply scc_soundness_main_lemma; eauto with myrelations.
Qed.
