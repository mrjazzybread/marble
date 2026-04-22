(* This library defines a logical view of depth-first search, and explores
   its properties. That is, it defines what it means for a forest to be a
   DFS forest. *)

Set Implicit Arguments.
From Stdlib Require Import Program.Equality. (* [dependent destruction] *)
From marble.logic Require Import MySets.
From marble.logic Require Import MyRelations.
From marble.logic Require Import MyLists.

(* ---------------------------------------------------------------------------- *)

(* We fix a set [V] of vertices. *)

Section D.

(* A type of vertices. *)

Variable V : Type.

(* An inductive type of forests. *)

Inductive forest :=
|    Empty: forest
| NonEmpty:
     V ->      (* the leftmost root of the forest *)
     forest -> (* its children *)
     forest -> (* the remaining roots of the forest *)
     forest.

(* It is customary to define a forest as a list of trees, where a tree is
   a pair of a vertex (the root) and a forest (its children). This means
   that the types [forest] and [tree] are defined in a mutually recursive
   manner. Because Rocq is not very good at mutual recursion, we inline
   the type [tree] into the definition of [forest], thus yielding a single
   recursive definition. As a result, we do not have a type [tree]. This
   is occasionally unpleasant, but in general works well. *)

(* The roots of a forest can be viewed as a set of vertices. *)

Fixpoint roots (f : forest) : set V :=
  match f with
  | Empty =>
      empty_
  | NonEmpty w ws vs =>
      insert w (roots vs)
  end.

(* The roots of a forest can be viewed as a list of vertices. *)

Fixpoint rootsl (f : forest) : list V :=
  match f with
  | Empty =>
      nil
  | NonEmpty w _ vs =>
      w :: rootsl vs
  end.

(* All vertices of a forest can be viewed as a set of vertices. *)

Fixpoint support (f : forest) : set V :=
  match f with
  | Empty =>
      empty_
  | NonEmpty w ws vs =>
      insert w (union (support ws) (support vs))
  end.

(* The roots of a forest form a subset of its support. *)

Lemma subset_roots_support:
  forall vs,
  subset (roots vs) (support vs).
Proof.
  induction vs; simpl; eauto with mysets.
Qed.

(* All vertices of a forest can also be viewed as a list of vertices.
   There are two typical ways of doing this: pre-order and post-order. *)

Fixpoint preorder (f : forest) :=
  match f with
  | Empty =>
      nil
  | NonEmpty w ws vs =>
      w :: preorder ws ++ preorder vs
  end.

Fixpoint postorder (f : forest) :=
  match f with
  | Empty =>
      nil
  | NonEmpty w ws vs =>
      postorder ws ++ w :: postorder vs
  end.

(* A vertex appears in the support if and only if it appears in the
   postorder linearization. *)

Lemma lsupport_postorder:
  forall f,
  lsupport (postorder f) = support f.
Proof.
  induction f; simpl.
  { eauto. }
  { rewrite lsupport_concat.
    rewrite IHf1. simpl.
    rewrite IHf2.
    eauto 20 with mysets. }
Qed.

(* A non-empty forest has a non-empty linearization. *)

Lemma postorder_not_nil:
  forall ws,
  ws <> Empty ->
  postorder ws <> nil.
Proof.
  intros. destruct ws; [ congruence | ]. simpl.
  intros (? & ?)%app_eq_nil.
  congruence.
Qed.

(* The first vertex in the reverse postorder of [f] is (obviously)
   a member of the support of [f]. *)

Lemma member_last_root_support r rs f :
  r :: rs = rev (postorder f) ->
  member r (support f).
Proof.
  intros h.
  rewrite <- lsupport_postorder.
  rewrite <- lsupport_rev.
  rewrite <- h.
  simpl. eauto with mysets.
Qed.

(* Two forests, viewed as lists of trees, can be concatenated. *)

Fixpoint concat (ws vs : forest) : forest :=
  match ws with
  | Empty =>
      vs
  | NonEmpty w ws vs1 =>
      NonEmpty w ws (concat vs1 vs)
  end.

(* The empty forest is a neutral element for concatenation. *)

Lemma concat_empty:
  forall f,
  concat f Empty = f.
Proof.
  induction f; simpl; intros; congruence.
Qed.

(* Forest concatenation is associative. *)

Lemma concat_associative:
  forall xs ys zs,
  concat xs (concat ys zs) = concat (concat xs ys) zs.
Proof.
  induction xs; simpl; intros; congruence.
Qed.

(* The support of the concatenation is the union of the supports. *)

Lemma support_concat:
  forall f1 f2,
  support (concat f1 f2) = union (support f1) (support f2).
Proof.
  induction f1 as [| ? ? _ ? ih ]; simpl; intros.
  eauto with mysets.
  rewrite ih. eauto 25 with mysets.
Qed.

(* The roots of the concatenation is the union of the roots of the parts. *)

Lemma roots_concat:
  forall f1 f2,
  roots (concat f1 f2) = union (roots f1) (roots f2).
Proof.
  induction f1 as [| ? ? _ ? ih ]; simpl; intros.
  { eauto with mysets. }
  { rewrite ih. eauto 20 with mysets. }
Qed.

(* The linearization of the concatenation is the concatenation of the
   linearizations. *)

Lemma preorder_concat:
  forall f1 f2,
  preorder (concat f1 f2) = preorder f1 ++ preorder f2.
Proof.
  induction f1 as [| ? ? _ ? ih ]; simpl; intros.
  { reflexivity. }
  { rewrite <- app_assoc. rewrite ih. reflexivity. }
Qed.

Lemma postorder_concat:
  forall f1 f2,
  postorder (concat f1 f2) = postorder f1 ++ postorder f2.
Proof.
  induction f1 as [| ? ? _ ? ih ]; simpl; intros.
  { reflexivity. }
  { rewrite <- app_assoc. rewrite ih. reflexivity. }
Qed.

(* The function [revf] reverses a forest, viewed as a list of trees.
   The reversal is performed not just at the top level, but at every
   level. This function is used in the specification of the executable
   DFS algorithm, which naturally builds such a recursively-reversed
   forest. *)

Fixpoint revf (f : forest) : forest :=
  match f with
  | Empty =>
      Empty
  | NonEmpty w ws vs =>
      concat (revf vs) (NonEmpty w (revf ws) Empty)
  end.

(* Reversal and concatenation commute. *)

Lemma revf_concat:
  forall f1 f2,
  revf (concat f1 f2) = concat (revf f2) (revf f1).
Proof.
  induction f1; simpl; intros.
  { rewrite concat_empty. reflexivity. }
  { rewrite IHf1_2. rewrite concat_associative. reflexivity. }
Qed.

(* Reversal is involutive. *)

Lemma revf_revf:
  forall f,
  revf (revf f) = f.
Proof.
  induction f; simpl; intros.
  { reflexivity. }
  { rewrite revf_concat. simpl. congruence. }
Qed.

(* Reversal commutes with [support] and [roots]. *)

Lemma support_revf:
  forall f,
  support (revf f) = support f.
Proof.
  induction f; simpl; intros.
  { eauto. }
  { rewrite support_concat. simpl.
    rewrite IHf1, IHf2.
    eauto 20 with mysets. }
Qed.

Lemma roots_revf:
  forall f,
  roots (revf f) = roots f.
Proof.
  induction f; simpl; intros.
  { eauto. }
  { rewrite roots_concat. simpl.
    rewrite IHf2.
    eauto 10 with mysets. }
Qed.

(* The reverse postorder of the forest [f] is the preorder of the recursive
   reversal of [f]. *)

Lemma preorder_revf:
  forall f,
  preorder (revf f) = rev (postorder f).
Proof.
  induction f; simpl; intros.
  { eauto. }
  { rewrite preorder_concat. simpl.
    rewrite IHf1, IHf2.
    rewrite rev_app_distr. simpl. rewrite app_nil_r.
    rewrite <- app_assoc. simpl.
    reflexivity. (* ouf! *) }
Qed.

(* If a forest has a non-empty reverse postorder, which begins with
   the vertex [root2], then this forest is non-empty, and the root
   of its last tree is [root2]. *)

Lemma isolate_last_tree:
  forall root2 f1 rs,
  root2 :: rs = rev (postorder f1) ->
  exists sons1 head1,
  concat head1 (NonEmpty root2 sons1 Empty) = f1.
Proof.
  (* Although this result sounds obvious, its proof is a bit hairy. *)
  induction f1 as [| root1 sons1 _ tail1 ]; simpl; intros rs h.
  (* Clearly, [f1] is non-empty. *)
  { congruence. }
  rewrite rev_app_distr in h. simpl in h.
  (* Now, check whether [tail1] is empty. We do not destruct [tail1]
     because (when it is non-empty) we do not wish to introduce names
     for its components. *)
  assert (fact: tail1 = Empty \/ tail1 <> Empty).
  { destruct tail1; [ left | right ]; congruence. }
  destruct fact; [ subst | ].
  (* If [tail1] is empty, then we have got the last tree in [f1].
     The vertices [root1] and [root2] are equal, and the goal holds. *)
  { injection h. clear h. intros. subst.
    exists sons1, Empty. reflexivity. }
  (* Otherwise, we have to skip this tree and go look further. *)
  { rewrite <- app_assoc in h.
    apply head_of_append in h;
      eauto using rev_not_nil, postorder_not_nil.
    destruct h as (? & ? & ?).
    edestruct IHtail1 as (sons2 & head1 & ?); [ eauto |]. subst.
    exists sons2, (NonEmpty root1 sons1 head1). reflexivity. }
Qed.

(* The predicate [ordered rs f] means that the roots of the forest [f]
   respect the ordering imposed by the list [rs]. *)

(* The predicate is defined in such a way that there can be more
   vertices in [rs] than in [f]. The roots of the forest [f] must
   appear in the list [rs], though, and they must appear in the
   correct order. *)

Inductive ordered : list V -> forest -> Prop :=
| OrderedNil:
    ordered nil Empty
| OrderedSkip:
    (* If the tentative first root [r] does not appear anywhere
       in [f], then it is considered irrelevant. *)
    forall r rs f,
    ~ member r (support f) ->
    ordered rs f ->
    ordered (r :: rs) f
| OrderedRoot:
    (* Otherwise, the tentative first root [r] must indeed be
       the root of the first tree in the forest. *)
    forall r rs ws f,
    ordered rs f ->
    ordered (r :: rs) (NonEmpty r ws f).

(* This (unused) lemma states that if [rs] orders a non-empty forest,
   then it orders its tail, too (provided the root [w] does not occur
   twice in the forest). *)

Lemma ordered_tail rs w ws vs :
  ordered rs (NonEmpty w ws vs) ->
  ~ member w (support vs) ->
  ordered rs vs.
Proof.
  intros h; dependent induction h; intros.
  (* OrderedSkip. *)
  { eapply OrderedSkip; [ | eauto ].
    simpl in *. mysets. }
  (* OrderedRoot. *)
  { eapply OrderedSkip; eauto. }
Qed.

(* ---------------------------------------------------------------------------- *)

(* We fix a set [E] of edges. *)

(* An edge (successor) relation. *)
Variable E : V -> V -> Prop.

Notation into_ vs ws := (into E vs ws).
Notation outof_ vs ws := (outof E vs ws).
Notation closed_ vs := (closed (path E) vs).
Notation reaches_ vs ws := (reaches E vs ws).
Notation scc_ := (scc E).

(* The predicate [dfs imarked omarked f] holds if a depth-first search,
   beginning with the set of marked vertices [imarked], can lead to a final
   set of marked vertices [omarked] and construct the forest [f]. *)

(* This can be viewed as a logic-programming version of the DFS algorithm.
   Note that this predicate is non-deterministic: the order in which the
   roots are visited, as well as the order in which the successors of a
   vertex are visited, are not specified. Furthermore, there is no
   requirement that all vertices of the graph be visited: the forest can be
   partial. (There *is* a requirement that, if a vertex is visited, then all
   of its successors are eventually marked.) *)

(* The set [omarked] is always the union of [imarked] and [support f]. We
   prove this fact a posteriori. We could have chosen instead to remove the
   parameter [omarked]. The current approach works rather well. *)

(* There are two constraints that one might wish to impose on a forest. One
   is an upper bound on its roots (e.g., the roots of the forest must be
   successors of some node [w]), the other is a lower bound on the final set
   of marked nodes (e.g., the search is not allowed to stop until all
   successors of [w] are marked). It is possible to impose these constraints
   either a priori (by parameterizing the predicate [dfs] with appropriate
   information) or a posteriori.  We follow the latter approach, which seems
   more flexible and clearer. *)

Inductive dfs : set V -> set V -> forest -> Prop :=

| DFSEmpty:
    (* There is no a priori constraint on the final set of marked nodes.
       Thus, a search is allowed to stop at any time. *)
    forall imarked,
    dfs imarked imarked Empty

| DFSNonEmpty:
    (* There is no a priori constraint on the roots. Thus, an arbitrary
       unmarked node [w] can be picked as the root of the first tree. *)
    forall imarked mmarked omarked w ws vs,
    ~ member w imarked ->
    (* Once we have picked [w], we mark [w] and traverse its successors,
       yielding a sub-forest [ws]. We impose two constraints a posteriori:
       every root of [ws] must be a successor of [w], and every successor
       of [w] must be marked once we are done constructing [ws]. *)
    dfs (insert w imarked) mmarked ws ->
    outof E (singleton w) (roots ws) ->
    into  E (singleton w) mmarked ->
    (* Once we are done with the successors of [w], we continue, yielding
       a sub-forest [vs]. *)
    dfs mmarked omarked vs ->
    (* The final result is a forest [NonEmpty w ws vs] where [ws] lies
       under [w] and [vs] lies at the same level as [w]. *)
    dfs imarked omarked (NonEmpty w ws vs).

(* ---------------------------------------------------------------------------- *)

(* The tactic [dfs1] states that the goal is an assumption, up to an
   equality in the first parameter of [dfs]. It creates one subgoal,
   which is this equality goal. *)

Local Ltac dfs1 :=
  match goal with h: dfs ?imarked1 _ ?vs |- dfs ?imarked2 _ ?vs =>
    assert (imarked1 = imarked2) as <- ; [| assumption ]
  end.

(* ---------------------------------------------------------------------------- *)

(* Properties of [dfs]. *)

Hint Constructors dfs : dfs.

(* The set of marked vertices grows as the DFS progresses. *)

Lemma dfs_monotonic:
  forall imarked omarked f,
  dfs imarked omarked f ->
  subset imarked omarked.
Proof.
  induction 1; eauto with st mysets.
Qed.

Ltac dfs_monotonic :=
  eapply subset_transitive; [ | eapply dfs_monotonic; eauto ].

(* Every element of a DFS forest is initially unmarked. *)

Lemma dfs_imarked:
  forall imarked omarked f,
  dfs imarked omarked f ->
  subset (support f) (complement imarked).
Proof.
  induction 1; simpl.
  (* Empty. *)
  { eauto with mysets. }
  (* NonEmpty *)
  { eapply prove_subset_union_left; [ | eapply prove_subset_union_left ].
    + eauto with mysets.
    + eauto with st mysets.
    + eauto 6 using dfs_monotonic with st mysets. }
Qed.

(* Every element of a DFS forest is finally marked. *)

Lemma dfs_omarked:
  forall imarked omarked f,
  dfs imarked omarked f ->
  subset (support f) omarked.
Proof.
  induction 1; simpl.
  (* Empty. *)
  { eauto with mysets. }
  (* NonEmpty *)
  { eapply prove_subset_union_left; [ | eapply prove_subset_union_left ].
    + do 2 dfs_monotonic. eauto with mysets.
    + dfs_monotonic. assumption.
    + assumption. }
Qed.

Ltac dfs_omarked :=
  repeat match goal with h: dfs _ _ _ |- _ =>
    generalize (dfs_omarked h); revert h
  end;
  intros.

(* Every vertex that is finally marked either was initially marked
   or is an element of the forest. This is the reciprocal of the
   combination of [dfs_monotonic] and [dfs_omarked]. *)

Lemma dfs_omarked_choice:
  forall imarked omarked f,
  dfs imarked omarked f ->
  subset omarked (union imarked (support f)).
Proof.
  induction 1; simpl.
  (* Empty. *)
  { eauto with mysets. }
  (* NonEmpty. *)
  { eapply subset_transitive; [ eauto | ].
    eapply prove_subset_union_left; [ | mysets ].
    eapply subset_transitive; [ eauto | ].
    mysets. }
Qed.

(* This is the combination of the previous results. *)

Lemma dfs_determines_omarked:
  forall imarked omarked f,
  dfs imarked omarked f ->
  omarked = union imarked (support f).
Proof.
  intros. eapply subset_antisymmetric.
  { eauto using dfs_omarked_choice. }
  { eauto using dfs_monotonic, dfs_omarked with mysets. }
Qed.

(* The support of the forest [f] is exactly the difference between
   [imarked] and [omarked]. This is also a reformulation of the
   above results. *)

Lemma dfs_determines_support:
  forall imarked omarked f,
  dfs imarked omarked f ->
  support f = diff omarked imarked.
Proof.
  intros. eapply subset_antisymmetric.
  { eauto using dfs_imarked, dfs_omarked with mysets. }
  { eapply prove_subset_intersection_left.
    + eapply subset_reflexive.
    + eauto using dfs_omarked_choice.
    + eauto with mysets. }
Qed.

Lemma dfs_determines_support_universe:
  forall imarked f,
  dfs imarked universe_ f ->
  support f = complement imarked.
Proof.
  intros. rewrite <- diff_universe. eauto using dfs_determines_support.
Qed.

(* The second [dfs] premise of [DFSNonEmpty] could also be formulated
   as follows. The set [mmarked] is replaced with the union of [imarked]
   and the support of the tree [w/ws]. *)

Lemma dfs_second_premise_reformulation
  imarked mmarked omarked w ws vs :
  dfs (insert w imarked) mmarked ws ->
  dfs mmarked omarked vs ->
  dfs (union imarked (insert w (support ws))) omarked vs.
Proof.
  intros h1 h2.
  rewrite (dfs_determines_omarked h1) in h2.
  dfs1. eauto 20 with mysets.
Qed.

(* This special case of [dfs_imarked] states that the tree [w/ws]
   is disjoint with the rest of the forest [vs]. *)

Lemma dfs_disjoint imarked omarked w ws vs :
  dfs imarked omarked (NonEmpty w ws vs) ->
  subset (support vs) (complement (insert w (support ws))).
Proof.
  intros h. dependent destruction h.
  (* The elements of the tree [w/ws] are in [mmarked]. *)
  generalize (dfs_second_premise_reformulation h1 h2); intro p.
  (* The elements of [vs] are not in [mmarked]. *)
  apply dfs_imarked in p.
  (* This is it! *)
  mysets.
Qed.

(* The set of initially marked vertices can be enlarged, as long as it
   remains disoint with the support of the forest that is constructed.
   The set of finally marked vertices is then similarly enlarged. *)

Lemma dfs_marked_covariant:
  forall masked imarked omarked ws,
  dfs imarked omarked ws ->
  subset (support ws) (complement masked) ->
  dfs (union imarked masked) (union omarked masked) ws.
Proof.
  induction 1; simpl; intros; econstructor; simplify_sets.
  + eauto with mysets.
  + rewrite union_associative. eauto with st mysets.
  + eauto.
  + eauto with mysets.
  + eauto with st mysets.
Qed.

(* Every successor of a vertex in the forest is finally marked. *)

Lemma dfs_complete_discovery:
  forall imarked omarked ws,
  dfs imarked omarked ws ->
  into_ (support ws) omarked.
Proof.
  (* This is a direct consequence of the definition of [dfs]. *)
  induction 1; simpl; intros.
  { eauto with myrelations. }
  { eauto 7 using prove_into_union_left, dfs_monotonic with st. }
Qed.

(* If every successor of an initially marked vertex is finally marked,
   then the set of finally marked vertices is closed. *)

Lemma dfs_into_closed:
  forall imarked omarked vs,
  dfs imarked omarked vs ->
  into_ imarked omarked ->
  closed_ omarked.
Proof.
  (* Quite remarkably perhaps, the proof is not by induction. [omarked] is
     the union of [imarked] and [support vs], so we reason separately about
     these sets. We then find that the goal follows immediately from the
     hypothesis and from [dfs_complete_discovery]. *)
  eauto 6 using into_contravariant, prove_into_union_left,
    dfs_omarked_choice, dfs_complete_discovery with mysets closed.
Qed.

(* This implies, in particular, that if [imarked] is closed, then [omarked]
   is closed. Thus, any vertex that is reachable from a marked vertex is
   itself marked. In particular, any vertex that is reachable from a root
   of the forest is marked / has been discovered. *)

Lemma dfs_closed:
  forall imarked omarked vs,
  dfs imarked omarked vs ->
  closed_ imarked ->
  closed_ omarked.
Proof.
  eauto using dfs_into_closed, dfs_monotonic with st closed.
Qed.

(* As a different corollary of [dfs_into_closed], if the set of initially
   marked vertices is closed, then, after marking [w] and visiting all of
   its successors, the set of finally marked vertices is closed. *)

Lemma dfs_into_closed_tree:
  forall w imarked mmarked ws,
  dfs (insert w imarked) mmarked ws ->
  closed_ imarked ->
  into_ (singleton w) mmarked ->
  closed_ mmarked.
Proof.
  intros.
  eapply dfs_into_closed; [ eauto | ].
  eapply prove_into_union_left; [ eauto | ].
  eapply subset_transitive; [ eauto with closed | ].
  eauto using dfs_monotonic with st mysets.
Qed.

(* The support of a forest is reachable from its roots. In other words,
   every vertex that is discovered must be reachable. *)

Lemma reaches_roots_support:
  forall imarked mmarked ws,
  dfs imarked mmarked ws ->
  reaches_ (roots ws) (support ws).
Proof.
  induction 1; simpl.
  (* Base case. *)
  { eauto with reaches. }
  (* Inductive case. Split into three sub-goals. *)
  { eapply prove_subset_union_left; [ | eapply prove_subset_union_left ].
  (* Sub-goal 1. [w] reaches [w]. *)
  + eauto using prove_reaches_self with mysets.
  (* Sub-goal 2. [w] reaches [roots ws] reaches [support ws]. *)
  + eauto using reaches_transitive, prove_reaches_union_left_1
      with st reaches.
  (* Sub-goal 3. [roots vs] reaches [support vs]. Use the induction hypothesis. *)
  + eauto using reaches_contravariant with mysets. }
Qed.

(* As a corollary, if [w/ws] is a tree of a DFS forest, then [w] reaches
   all of [ws]. *)

Lemma reaches_root_support imarked mmarked w ws vs :
  dfs imarked mmarked (NonEmpty w ws vs) ->
  reaches_ (singleton w) (support ws).
Proof.
  intros h. dependent destruction h.
  (* This repeats sub-goal 2 above, but never mind. *)
  eauto using reaches_roots_support, reaches_transitive with st reaches.
Qed.

(* The concatenation of two DFS forests (with matching intermediate
   state) is a DFS forest. *)

Lemma dfs_concat:
  forall imarked mmarked vs,
  dfs imarked mmarked vs ->
  forall omarked ws,
  dfs mmarked omarked ws ->
  dfs imarked omarked (concat vs ws).
Proof.
  induction 1; intros; simpl; eauto with dfs.
Qed.

(* Conversely, if a DFS forest is the concatenation of two forests,
   then, for some intermediate state [mmarked], these two forests
   are DFS forests. When used in a forward manner, this lemma allows
   introducing a name, [mmarked], for the vertices that are marked
   after constructing [vs] and before constructing [ws]. *)

Lemma dfs_concat_inversion:
  forall vs imarked omarked ws,
  dfs imarked omarked (concat vs ws) ->
  exists mmarked,
  dfs imarked mmarked vs /\
  dfs mmarked omarked ws.
Proof.
  induction vs; simpl; intros ??? h.
  { eauto with dfs. }
  { dependent destruction h.
    edestruct IHvs2 as (? & ? & ?). eauto.
    eauto with dfs. }
Qed.

(* This variant of [dfs_disjoint] states that if the sub-forests
   [ws] and [vs] are produced one after the other, then they have
   disjoint supports. *)

Lemma dfs_disjoint_concat imarked omarked ws vs :
  dfs imarked omarked (concat ws vs) ->
  subset (support vs) (complement (support ws)).
Proof.
  intros (mmarked & Hws & Hvs)%dfs_concat_inversion.
  (* The elements of [ws] are in [mmarked]. *)
  dfs_omarked.
  (* The elements of [vs] are not in [mmarked]. *)
  apply dfs_imarked in Hvs.
  (* This is it! *)
  mysets.
Qed.

(* ---------------------------------------------------------------------------- *)

(* The following lemmas form an analysis of the relation between a
   DFS forest and the strongly connected components. *)

(* Consider the root [w] of an arbitrary tree [w/ws] in a DFS forest. Let
   [imarked] be the set of vertices discovered before this tree. (We may
   assume that [imarked] is closed.) Then, the closure of [w] is contained
   in the union of [imarked] and of the tree [w/ws]. In other words, there
   are no forward paths: [w] cannot reach the trees towards the right. *)

Lemma bound_closure_direct imarked omarked w ws vs :
  dfs imarked omarked (NonEmpty w ws vs) ->
  closed_ imarked ->
  subset
    (closure E (singleton w))
    (union imarked (insert w (support ws))).
Proof.
  (* This is not a new key result; just a corollary of earlier results. *)
  intros hdfs. intros. dependent destruction hdfs.
  (* Let [mmarked] stand for the set of vertices that are marked after the
     tree [w/ws] has been visited. We know that [w] is a member of [mmarked]
     and that [mmarked] is closed. Thus, the closure of [w] is a subset of
     [mmarked]. Furthermore, [mmarked] is exactly the union of [imarked] and
     of the support of [w/ws]. *)
  eapply subset_transitive.
  eapply prove_subset_closure; [ | eapply dfs_into_closed_tree; eauto ].
  { eauto using dfs_monotonic with st mysets. }
  { eapply subset_transitive; [ eauto using dfs_omarked_choice | ].
    mysets. }
Qed.

(* Symmetrically, an upper bound for the closure of [w] in the reverse graph
   is the support of the forest [w/ws :: vs]. Indeed, because [imarked] is
   closed, the left-hand trees cannot reach [w]. *)

Lemma bound_closure_reverse:
  forall imarked w ws vs,
  dfs imarked universe_ (NonEmpty w ws vs) ->
  closed_ imarked ->
  subset
    (closure (reverse E) (singleton w))
    (support (NonEmpty w ws vs)).
Proof.
  (* This lemma does require that [omarked] be [universe_], as this means
     that [vs] represents *all* of the trees towards the right; there are
     no more. *)
  intros.
  eapply prove_subset_closure; [ simpl; eauto with mysets | ].
  erewrite dfs_determines_support_universe; [ | eauto ].
  eauto using prove_closed_path_complement.
Qed.

(* By combining the previous two lemmas, we find that the strongly
   connected component of [w] must be a subset of the tree [w/ws]. *)

Lemma bound_scc:
  forall imarked w ws vs,
  dfs imarked universe_ (NonEmpty w ws vs) ->
  closed_ imarked ->
  subset (scc_ w) (insert w (support ws)).
Proof.
  intros.
  (* By definition, [scc w] is the intersection of the vertices
     that [w] can reach and the vertices that can reach [w]. *)
  eapply subset_transitive; [ eapply prove_subset_intersection_right | ].
  + eapply prove_subset_scc_closure.
  + eapply prove_subset_scc_reverse_closure.
  (* The previous two lemmas provide upper bounds for the members
     of this intersection. *)
  + eapply subset_transitive; [
      eapply intersection_covariant; [
        eapply bound_closure_direct; eauto
      | eapply bound_closure_reverse; eauto
      ]
    | ].
    (* There remains to compute this intersection. *)
    simpl.
    eapply prove_subset_intersection_left.
    - eapply dfs_imarked; eauto.
    - eapply subset_reflexive.
    - mysets.
Qed.

(* Now, let us further assume that [w] is the root of the last tree in a DFS
   forest. Then, the strongly connected component of [w] is exactly the
   closure of [w] in the reverse graph. *)

Lemma last_scc {imarked vs w ws} :
  dfs imarked universe_ (concat vs (NonEmpty w ws Empty)) ->
  closed_ imarked ->
  scc_ w = closure (reverse E) (singleton w).
Proof.
  intros hdfs. intros.
  (* Only one inclusion is non-trivial. *)
  eapply subset_antisymmetric; [ eapply prove_subset_scc_reverse_closure | ].
  (* The strongly connected component of [w] is the intersection
     of the direct closure and reverse closure of [w]. *)
  eapply subset_transitive; [ | eapply prove_subset_intersection_scc ].
  (* Thus, it suffices to prove that the reverse closure of [w]
     is a subset of its direct closure. *)
  eapply prove_subset_intersection_right; [ | eauto with mysets ].
  (* Now, let us get rid of [vs] in the hypothesis above, as it plays
     no role. *)
  apply dfs_concat_inversion in hdfs.
  destruct hdfs as (? & ? & ?).
  (* By a previous lemma, the reverse closure of [w] is a subset
     of the support of the tree [w/ws]. *)
  eapply subset_transitive; [ eapply bound_closure_reverse; eauto using dfs_closed | ].
  (* Thus, there remains to show that [w] reaches [w/ws]. *)
  simpl. eauto using reaches_root_support with reaches mysets.
Qed.

(* The following lemma is a stronger version of [bound_closure_direct]. If
   [w/ws] is an arbitrary tree in the forest, then, under the assumption
   that [imarked] is closed both ways, the closure of [w] is exactly the set
   [w/ws]. *)

Lemma exact_closure imarked omarked w ws vs :
  dfs imarked omarked (NonEmpty w ws vs) ->
  closed_ imarked ->
  closed_ (complement imarked) ->
  closure E (singleton w) = insert w (support ws).
Proof.
  intros h. intros. eapply subset_antisymmetric.
  (* This inclusion follows from [bound_closure_direct], with the
     additional proviso that there is no overlap with [imarked].
     We know that [w] is not in [imarked], and the hypothesis
     that [complement imarked] is closed ensures that the closure
     of [w] lies outside [imarked]. *)
  { eapply subset_transitive; [ | eapply prove_subset_diff_union ].
    eapply prove_subset_intersection_right.
    + eapply bound_closure_direct; eauto.
    + eapply prove_subset_closure.
      - dependent destruction h. eauto with mysets.
      - eassumption. }
  (* Now, the reverse inclusion is easy. *)
  { eauto using reaches_root_support with reaches mysets. }
Qed.

End D.

Hint Constructors dfs : dfs.

(* ---------------------------------------------------------------------------- *)

(* If two DFS forests agree on the sets [imarked] and [omarked], then they have
   the same support. *)

Lemma dfs_same_support:
  forall V : Type,
  forall (E1 E2 : V -> V -> Prop),
  forall imarked omarked f1 f2,
  dfs E1 imarked omarked f1 ->
  dfs E2 imarked omarked f2 ->
  support f1 = support f2.
Proof.
  intros. erewrite dfs_determines_support by eauto.
  symmetry. eapply dfs_determines_support; eauto.
Qed.

(* ---------------------------------------------------------------------------- *)

(* The tactic [dfs1] states that the goal should be proved up to an
   equality in the first parameter of [dfs], that is, [imarked]. It
   creates a fresh metavariable. Its first subgoal is a [dfs] goal.
   Its second subgoal is an equality. *)

Ltac dfs1 :=
  match goal with |- @dfs ?V _ ?imarked2 _ ?vs =>
    let imarked1 := fresh "imarked" in
    evar (imarked1 : set V);
    cut (imarked1 = imarked2);
    subst imarked1;
    [ intros <- |]
  end.

(* The tactic [dfs2] is similar, but concerns the second parameter,
   that is, [omarked]. *)

Ltac dfs2 :=
  match goal with |- @dfs ?V _ _ ?omarked2 ?vs =>
    let omarked1 := fresh "omarked" in
    evar (omarked1 : set V);
    cut (omarked1 = omarked2);
    subst omarked1;
    [ intros <- |]
  end.
