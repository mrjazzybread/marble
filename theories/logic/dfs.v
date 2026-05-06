(* This library defines a logical view of depth-first search. It defines
   what it means for a forest to be a DFS forest, via an inductive
   predicate [dfs], and explores the properties of this predicate. *)

From Stdlib Require Import Program.Equality. (* [dependent destruction] *)
From stdpp Require Import fin_sets listset_nodup.
Local Notation fset := listset_nodup.
From stdpp Require Import sets propset.
Local Notation set := propset.
From listz Require Import listz. (* singleton list notation *)
Local Opaque listz.stdpp_buffer.singleton_list.
From marble Require Import tactics.
From marble.logic Require Import lists sets relations.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)

(* We fix a set [V] of vertices. *)

Section D.

(* A type of vertices. *)

Variable V : Type.

(* An inductive type of forests. *)

Inductive forest :=
|    Empty: forest
| NonEmpty:
     V →      (* the leftmost root of the forest *)
     forest → (* its children *)
     forest → (* the remaining roots of the forest *)
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
      ∅
  | NonEmpty w ws vs =>
      {[w]} ∪ roots vs
  end.

(* The roots of a forest can be viewed as a list of vertices. *)

Fixpoint rootsl (f : forest) : list V :=
  match f with
  | Empty =>
      []
  | NonEmpty w _ vs =>
      {[w]} ++ rootsl vs
  end.

(* All vertices of a forest can be viewed as a set of vertices. *)

Fixpoint support (f : forest) : set V :=
  match f with
  | Empty =>
      ∅
  | NonEmpty w ws vs =>
      {[w]} ∪ support ws ∪ support vs
  end.

(* The roots of a forest form a subset of its support. *)

Lemma subset_roots_support vs :
  roots vs ⊆ support vs.
Proof.
  induction vs; simpl; set_solver.
Qed.

(* All vertices of a forest can also be viewed as a list of vertices.
   There are two typical ways of doing this: pre-order and post-order. *)

Fixpoint preorder (f : forest) :=
  match f with
  | Empty =>
      []
  | NonEmpty w ws vs =>
      {[w]} ++ preorder ws ++ preorder vs
  end.

Fixpoint postorder (f : forest) :=
  match f with
  | Empty =>
      []
  | NonEmpty w ws vs =>
      postorder ws ++ {[w]} ++ postorder vs
  end.

(* A vertex appears in the support if and only if it appears in the
   postorder linearization. *)

Lemma list_to_set_postorder f :
  list_to_set (postorder f) ≡ support f.
Proof.
  induction f; simpl; autorewrite with list_to_set;
  rewrite ?IHf1, ?IHf2; set_solver.
Qed.

(* A non-empty forest has a non-empty linearization. *)

Lemma postorder_nil_inv ws :
  postorder ws = [] → ws = Empty.
Proof.
  intros. destruct ws as [| ws ].
  + eauto.
  + exfalso.
    simpl in *. rewrite !app_nil in *. unpack.
    eapply singleton_ne_nil. eauto.
Qed.

Lemma postorder_not_nil ws :
  ws ≠ Empty → postorder ws ≠ nil.
Proof.
  intros. generalize (postorder_nil_inv ws). tauto.
Qed.

(* The first vertex in the reverse postorder of [f] is (obviously)
   a member of the support of [f]. *)

Lemma member_last_root_support r rs f :
  {[r]} ++ rs = rev (postorder f) →
  r ∈ support f.
Proof.
  intros h.
  rewrite <- list_to_set_postorder.
  rewrite <- list_to_set_rev.
  rewrite <- h.
  set_solver.
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

Lemma concat_empty f :
  concat f Empty = f.
Proof.
  induction f; simpl; intros; congruence.
Qed.

(* Forest concatenation is associative. *)

Lemma concat_associative xs ys zs :
  concat xs (concat ys zs) = concat (concat xs ys) zs.
Proof.
  induction xs; simpl; intros; congruence.
Qed.

(* The support of the concatenation is the union of the supports. *)

Lemma support_concat f1 f2 :
  support (concat f1 f2) ≡ support f1 ∪ support f2.
Proof.
  induction f1 as [| ? ? _ ? ih ]; simpl; intros;
  rewrite ?ih; set_solver.
Qed.

(* The roots of the concatenation is the union of the roots of the parts. *)

Lemma roots_concat f1 f2 :
  roots (concat f1 f2) ≡ roots f1 ∪ roots f2.
Proof.
  induction f1 as [| ? ? _ ? ih ]; simpl; intros;
  rewrite ?ih; set_solver.
Qed.

(* The linearization of the concatenation is the concatenation of the
   linearizations. *)

Lemma preorder_concat f1 f2 :
  preorder (concat f1 f2) = preorder f1 ++ preorder f2.
Proof.
  induction f1 as [| ? ? _ ? ih ]; simpl; intros.
  { reflexivity. }
  { rewrite ih, <- !app_assoc. reflexivity. }
Qed.

Lemma postorder_concat f1 f2 :
  postorder (concat f1 f2) = postorder f1 ++ postorder f2.
Proof.
  induction f1 as [| ? ? _ ? ih ]; simpl; intros.
  { reflexivity. }
  { rewrite ih, <- !app_assoc. reflexivity. }
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

Lemma revf_concat f1 f2 :
  revf (concat f1 f2) = concat (revf f2) (revf f1).
Proof.
  induction f1; simpl; intros.
  { rewrite concat_empty. reflexivity. }
  { rewrite IHf1_2. rewrite concat_associative. reflexivity. }
Qed.

(* Reversal is involutive. *)

Lemma revf_revf f :
  revf (revf f) = f.
Proof.
  induction f; simpl; intros.
  { reflexivity. }
  { rewrite revf_concat. simpl. congruence. }
Qed.

(* Reversal commutes with [support] and [roots]. *)

Lemma support_revf f :
  support (revf f) ≡ support f.
Proof.
  induction f; simpl; intros.
  { eauto. }
  { rewrite support_concat. simpl.
    rewrite IHf1, IHf2.
    set_solver. }
Qed.

Lemma roots_revf f :
  roots (revf f) ≡ roots f.
Proof.
  induction f; simpl; intros.
  { eauto. }
  { rewrite roots_concat. simpl.
    rewrite IHf2.
    set_solver. }
Qed.

(* The reverse postorder of the forest [f] is the preorder of the recursive
   reversal of [f]. *)

Lemma preorder_revf f :
  preorder (revf f) = rev (postorder f).
Proof.
  induction f; simpl; intros.
  { eauto. }
  { rewrite preorder_concat. simpl.
    rewrite IHf1, IHf2, !rev_app_distr.
    lego. }
Qed.

(* If a forest has a non-empty reverse postorder, which begins with
   the vertex [root2], then this forest is non-empty, and the root
   of its last tree is [root2]. *)

Lemma isolate_last_tree:
  ∀ root2 f1 rs,
  {[root2]} ++ rs = rev (postorder f1) →
  exists sons1 head1,
  concat head1 (NonEmpty root2 sons1 Empty) = f1.
Proof.
  (* Although this result sounds obvious, its proof is a bit hairy. *)
  induction f1 as [| root1 sons1 _ tail1 ]; simpl; intros rs h.
  (* Clearly, [f1] is non-empty. *)
  { exfalso. rewrite app_nil in h. destruct h.
    eapply singleton_ne_nil. eauto. }
  rewrite !rev_app_distr, rev_singleton in h.
  (* Now, check whether [tail1] is empty. We do not destruct [tail1]
     because (when it is non-empty) we do not wish to introduce names
     for its components. *)
  assert (fact: tail1 = Empty \/ tail1 ≠ Empty).
  { destruct tail1; [ left | right ]; congruence. }
  destruct fact; [ subst | ].
  (* If [tail1] is empty, then we have got the last tree in [f1].
     The vertices [root1] and [root2] are equal, and the goal holds. *)
  { simpl in h.
    apply app_inj_1 in h; [| length; reflexivity ].
    destruct h as (h1 & h2).
    apply singleton_inj in h1.
    subst. exists sons1, Empty. reflexivity. }
  (* Otherwise, we have to skip this tree and go look further. *)
  { rewrite <- app_assoc in h.
    assert (rev (postorder tail1) ≠ []).
    { eauto using rev_not_nil, postorder_not_nil. }
    apply app_eq_inv'_le in h; [| lengths; length in *; lia ].
    destruct h as (? & ? & ?).
    edestruct IHtail1 as (sons2 & head1 & ?); [ eauto |]. subst.
    exists sons2, (NonEmpty root1 sons1 head1). reflexivity. }
Qed.

(* The predicate [ordered rs f] means that the roots of the forest [f]
   respect the ordering imposed by the list [rs]. *)

(* There may be vertices in [rs] that do not appear in [support f]:
   they are irrelevant.

   The roots of the forest [f] must appear in the list [rs], and must
   appear in the correct order.

   A root of the forest [f] can in fact appear several times in [rs];
   then, only its first occurrence matters. Later occurrences are
   irrelevant. For this reason, [ordered rs f] does NOT imply
   [filter (λ v, v ∈ support f) rs = rootsl f]. *)

Inductive ordered : list V → forest → Prop :=
| OrderedNil:
    ordered nil Empty
| OrderedSkip:
    (* If the tentative first root [r] does not appear anywhere
       in [f], then it is considered irrelevant. *)
    ∀ r rs f,
    r ∉ support f →
    ordered rs f →
    ordered ({[r]} ++ rs) f
| OrderedRoot:
    (* Otherwise, the tentative first root [r] must indeed be
       the root of the first tree in the forest. *)
    ∀ r rs ws f,
    ordered rs f →
    ordered ({[r]} ++ rs) (NonEmpty r ws f).

(* If [f] is ordered by [rs] then the roots of [f] form a subset of
   the list [rs], viewed as a set. *)

Lemma ordered_subset rs f :
  ordered rs f →
  roots f ⊆ list_to_set rs.
Proof.
  induction 1; simpl; set_solver.
Qed.

(* It is possible to prepend extra vertices [rs1] in front of the
   list [rs2], provided that these vertices do not appear in the
   forest [f].  *)

(* This generalizes the constructor [OrderedSkip]. *)

Lemma ordered_skip rs2 f rs1 :
  ordered rs2 f →
  list_to_set rs1 ## support f →
  ordered (rs1 ++ rs2) f.
Proof.
  induction rs1 as [| r1 rs1 ]; intros.
  { assumption. }
  { change (r1 :: rs1) with ({[r1]} ++ rs1). list.
    eapply OrderedSkip; set_solver. }
Qed.

(* Provided [rs1] and [f2] have no common vertices, two judgments
   [ordered rs1 f1] and [ordered rs2 f2] can be concatenated. *)

Lemma ordered_concat rs1 f1 :
  ordered rs1 f1 →
  ∀ rs2 f2,
  list_to_set rs1 ## support f2 →
  ordered rs2 f2 →
  ordered (rs1 ++ rs2) (concat f1 f2).
Proof.
  (* The proof is easy, but it took some time to realize that
     this was the correct (and necessary) inductive statement. *)
  induction 1; intros; simpl concat; list.
  { assumption. }
  { eapply OrderedSkip.
    - rewrite support_concat. set_solver.
    - eapply IHordered. set_solver. assumption. }
  { eapply OrderedRoot.
    eapply IHordered. set_solver. assumption. }
Qed.

(* -------------------------------------------------------------------------- *)

(* We fix a set [E] of edges. *)

(* An edge (successor) relation. *)
Variable E : V → V → Prop.

Notation into_ vs ws := (into E vs ws).
Notation outof_ vs ws := (outof E vs ws).
Notation closed_ vs := (closed E vs).
  (* note: [closed (path E)] and [closed E] are equivalent *)
Notation closure_ vs := (closure E vs).
Notation reaches_ vs ws := (reaches E vs ws).
Notation component_ := (component E).

(* The predicate [dfs imarked omarked f] holds if a depth-first search,
   beginning with the set of marked vertices [imarked], can lead to a
   final set of marked vertices [omarked] and construct the forest [f]. *)

(* This can be viewed as a logic-programming version of the DFS algorithm.
   Note that this predicate is non-deterministic: the order in which the
   roots are visited, as well as the order in which the successors of a
   vertex are visited, are not specified. Furthermore, there is no
   requirement that all vertices of the graph be visited: the forest can
   be partial. (There *is* a requirement that, if a vertex is visited,
   then all of its successors are eventually marked.) *)

(* The set [omarked] is always the union of [imarked] and [support f]. We
   prove this fact a posteriori. We could have chosen instead to remove
   the parameter [omarked]. The current approach works rather well. *)

(* There are two constraints that one might wish to impose on a forest.
   One is an upper bound on its roots (e.g., the roots of the forest must
   be successors of some node [w]), the other is a lower bound on the
   final set of marked nodes (e.g., the search is not allowed to stop
   until all successors of [w] are marked). It is possible to impose these
   constraints either a priori (by parameterizing the predicate [dfs] with
   appropriate information) or a posteriori. We follow the latter
   approach, which seems more flexible and clearer. *)

Inductive dfs : set V → set V → forest → Prop :=

| DFSEmpty:
    (* There is no a priori constraint on the final set of marked nodes.
       Thus, a search is allowed to stop at any time. *)
    ∀ imarked omarked,
    imarked ≡ omarked →
    dfs imarked omarked Empty

| DFSNonEmpty:
    (* There is no a priori constraint on the roots. Thus, an arbitrary
       unmarked node [w] can be picked as the root of the first tree. *)
    ∀ imarked mmarked omarked w ws vs,
    w ∉ imarked →
    (* Once we have picked [w], we mark [w] and traverse its successors,
       yielding a sub-forest [ws]. We impose two constraints a posteriori:
       every root of [ws] must be a successor of [w], and every successor
       of [w] must be marked once we are done constructing [ws]. *)
    dfs ({[w]} ∪ imarked) mmarked ws →
    outof E {[w]} (roots ws) →
    into  E {[w]} mmarked →
    (* Once we are done with the successors of [w], we continue, yielding
       a sub-forest [vs]. *)
    dfs mmarked omarked vs →
    (* The final result is a forest [NonEmpty w ws vs] where [ws] lies
       under [w] and [vs] lies at the same level as [w]. *)
    dfs imarked omarked (NonEmpty w ws vs).

(* -------------------------------------------------------------------------- *)

(* This local tactic is redefined (exported) at the end of this file. *)

Ltac dfs1 :=
  match goal with |- dfs ?imarked2 _ ?vs =>
    let imarked1 := fresh "imarked" in
    evar (imarked1 : set V);
    cut (imarked1 ≡ imarked2);
    subst imarked1;
    [ intros <- |]
  end.

(* -------------------------------------------------------------------------- *)

(* Properties of [dfs]. *)

Hint Constructors dfs : dfs.

(* The leftmost root of a forest is initially unmarked. *)

Lemma root_is_unmarked w ws vs imarked omarked :
  dfs imarked omarked (NonEmpty w ws vs) →
  w ∉ imarked.
Proof.
  intros hdfs. dependent destruction hdfs. assumption.
Qed.

(* [dfs] is compatible with set equality. *)

Global Instance : Proper (equiv ==> equiv ==> eq ==> impl) dfs.
Proof.
  intros imarked1 imarked2 ? omarked1 omarked2 ? f1 f2 ?. subst.
  unfold impl. intro Hdfs.
  generalize dependent omarked2.
  generalize dependent imarked2.
  generalize dependent omarked1. revert imarked1. revert f2.
  induction 1; intros.
  + econstructor. set_solver.
  + econstructor; eauto.
    - set_solver.
    - eapply IHHdfs1; set_solver.
Qed.

(* The set of marked vertices grows as the DFS progresses. *)

Lemma dfs_monotonic imarked omarked f :
  dfs imarked omarked f →
  imarked ⊆ omarked.
Proof.
  induction 1; set_solver.
Qed.

Ltac dfs_monotonic :=
  repeat match goal with
  h: dfs _ _ _ |- _ =>
    generalize (dfs_monotonic h); revert h
  end;
  intros.

(* Every element of a DFS forest is initially unmarked. *)

Lemma dfs_imarked imarked omarked f :
  dfs imarked omarked f →
  support f ## imarked.
Proof.
  induction 1; simpl; dfs_monotonic; set_solver.
Qed.

Ltac dfs_imarked :=
  repeat match goal with h: dfs _ _ _ |- _ =>
    generalize (dfs_imarked h); revert h
  end;
  intros.

(* Every element of a DFS forest is finally marked. *)

Lemma dfs_omarked imarked omarked f :
  dfs imarked omarked f →
  support f ⊆ omarked.
Proof.
  induction 1; simpl; dfs_monotonic; set_solver.
Qed.

Ltac dfs_omarked :=
  repeat match goal with h: dfs _ _ _ |- _ =>
    generalize (dfs_omarked h); revert h
  end;
  intros.

(* Every vertex that is finally marked either was initially marked
   or is an element of the forest. This is the reciprocal of the
   combination of [dfs_monotonic] and [dfs_omarked]. *)

Lemma dfs_omarked_choice imarked omarked f :
  dfs imarked omarked f →
  omarked ⊆ imarked ∪ support f.
Proof.
  induction 1; simpl; set_solver.
Qed.

(* This is the combination of the previous results. *)

Lemma dfs_determines_omarked imarked omarked f :
  dfs imarked omarked f →
  omarked ≡ imarked ∪ support f.
Proof.
  intros. eapply subset_antisymmetric.
  { eauto using dfs_omarked_choice. }
  { dfs_monotonic. dfs_omarked. set_solver. }
Qed.

(* The support of the forest [f] is exactly the difference between
   [imarked] and [omarked]. This is also a reformulation of the
   above results. *)

Lemma dfs_determines_support imarked omarked f :
  dfs imarked omarked f →
  support f ≡ omarked ∖ imarked.
Proof.
  intros hdfs. dfs_imarked.
  rewrite (dfs_determines_omarked hdfs).
  set_solver.
Qed.

(* The second [dfs] premise of [DFSNonEmpty] could also be formulated
   as follows. The set [mmarked] is replaced with the union of [imarked]
   and the support of the tree [w/ws]. *)

Lemma dfs_second_premise_reformulation imarked mmarked omarked w ws vs :
  dfs ({[w]} ∪ imarked) mmarked ws →
  dfs mmarked omarked vs →
  dfs (imarked ∪ {[w]} ∪ support ws) omarked vs.
Proof.
  intros h1 h2.
  rewrite (dfs_determines_omarked h1) in h2.
  dfs1. eassumption. set_solver.
Qed.

(* This special case of [dfs_imarked] states that the tree [w/ws]
   is disjoint with the rest of the forest [vs]. *)

Lemma dfs_disjoint imarked omarked w ws vs :
  dfs imarked omarked (NonEmpty w ws vs) →
  support vs ## {[w]} ∪ support ws.
Proof.
  intros h. dependent destruction h.
  (* The elements of the tree [w/ws] are in [mmarked]. *)
  generalize (dfs_second_premise_reformulation h1 h2); intro p.
  (* The elements of [vs] are not in [mmarked]. *)
  apply dfs_imarked in p.
  (* This is it! *)
  set_solver.
Qed.

(* The set of initially marked vertices can be enlarged, as long as it
   remains disoint with the support of the forest that is constructed.
   The set of finally marked vertices is then similarly enlarged. *)

(* This lemma is currently unused. *)

Lemma dfs_marked_covariant masked imarked omarked ws :
  dfs imarked omarked ws →
  support ws ## masked →
  dfs (imarked ∪ masked) (omarked ∪ masked) ws.
Proof.
  induction 1; simpl; intros; econstructor.
  + set_solver.
  + set_solver.
  + autorewrite with sets. eapply IHdfs1. set_solver.
  + eauto.
  + set_solver.
  + eapply IHdfs2. set_solver.
Qed.

(* Every successor of a vertex in the forest is finally marked. *)

Lemma dfs_complete_discovery imarked omarked ws :
  dfs imarked omarked ws →
  into_ (support ws) omarked.
Proof.
  (* This is a direct consequence of the definition of [dfs]. *)
  induction 1; simpl; intros; dfs_monotonic; set_solver.
Qed.

(* If every successor of an initially marked vertex is finally marked,
   then the set of finally marked vertices is closed. *)

Lemma dfs_into_closed imarked omarked vs :
  dfs imarked omarked vs →
  into_ imarked omarked →
  closed_ omarked.
Proof.
  (* Quite remarkably perhaps, the proof is not by induction. [omarked] is
     the union of [imarked] and [support vs], so we reason separately about
     these sets. We then find that the goal follows immediately from the
     hypothesis and from [dfs_complete_discovery]. *)
  intros hdfs ?.
  generalize (dfs_omarked_choice hdfs); intro.
  generalize (dfs_complete_discovery hdfs); intro.
  set_solver.
Qed.

(* This implies, in particular, that if [imarked] is closed, then [omarked]
   is closed. Thus, any vertex that is reachable from a marked vertex is
   itself marked. In particular, any vertex that is reachable from a root
   of the forest is marked / has been discovered. *)

Lemma dfs_closed imarked omarked vs :
  dfs imarked omarked vs →
  closed_ imarked →
  closed_ omarked.
Proof.
  eauto using dfs_into_closed, dfs_monotonic, subset_transitive.
Qed.

(* As a different corollary of [dfs_into_closed], if the set of initially
   marked vertices is closed, then, after marking [w] and visiting all of
   its successors, the set of finally marked vertices is closed. *)

Lemma dfs_into_closed_tree w imarked mmarked ws :
  dfs ({[w]} ∪ imarked) mmarked ws →
  closed_ imarked →
  into_ {[w]} mmarked →
  closed_ mmarked.
Proof.
  intros. dfs_monotonic.
  eapply dfs_into_closed; [ eauto | ].
  set_solver.
Qed.

(* The support of a forest is reachable from its roots. In other words,
   every vertex that is discovered must be reachable. *)

Lemma reaches_roots_support imarked mmarked ws :
  dfs imarked mmarked ws →
  reaches_ (roots ws) (support ws).
Proof.
  induction 1; simpl.
  (* Base case. *)
  { eauto with reaches. }
  (* Inductive case. Split into three sub-goals. *)
  { eapply prove_subset_union_left.
    eapply prove_subset_union_left.
    (* Sub-goal 1. [w] reaches [w]. *)
    + eapply prove_reaches_self. set_solver.
    (* Sub-goal 2. [w] reaches [roots ws] reaches [support ws]. *)
    + eapply prove_reaches_union_left_1.
      eapply reaches_transitive; [| eassumption ].
      eauto 2 using subset_transitive with reaches.
    (* Sub-goal 3. [roots vs] reaches [support vs].
       Use the induction hypothesis. *)
    + set_solver. }
Qed.

(* As a corollary, if [w/ws] is a tree of a DFS forest,
   then [w] reaches all of [ws]. *)

Lemma reaches_root_support imarked mmarked w ws vs :
  dfs imarked mmarked (NonEmpty w ws vs) →
  reaches_ {[w]} (support ws).
Proof.
  intros h. dependent destruction h.
  (* This repeats part of sub-goal 2 above, but never mind. *)
  eapply reaches_transitive with (ys := roots ws).
  { eauto using subset_transitive with reaches. }
  { eauto using reaches_roots_support. }
Qed.

Lemma reaches_root_descendants w ws vs imarked omarked x :
  dfs imarked omarked (NonEmpty w ws vs) →
  x ∈ support ws →
  reaches_ {[w]} {[x]}.
Proof.
  intros hdfs ?.
  generalize (reaches_root_support hdfs); intro.
  set_solver.
Qed.

(* If there are initially no marked vertices, then, at the end of
   a DFS traversal, the marked vertices are exactly the vertices
   that are reachable from the start vertices. *)

Lemma omarked_is_closure_start omarked vs start :
  dfs ∅ omarked vs →
  roots vs ⊆ start →
  start ⊆ omarked →
  omarked ≡ closure_ start.
Proof.
  intros Hdfs ??.
  assert (closed_ omarked) by eauto using dfs_closed with set_solver.
  eapply subset_antisymmetric.
  (* Every marked vertex is reachable. *)
  { assert (reaches E start (roots vs))
      by eauto using prove_reaches_self.
    generalize (reaches_roots_support Hdfs); intro.
    generalize (dfs_omarked_choice Hdfs); intro.
    eauto 2 using reaches_transitive, subset_transitive with set_solver. }
  (* Every reachable vertex is marked. *)
  { eapply prove_closure_subset; [ eauto |].
    rewrite closed_path. assumption. }
Qed.

(* The concatenation of two DFS forests (with matching intermediate
   state) is a DFS forest. *)

Lemma dfs_concat imarked mmarked vs :
  dfs imarked mmarked vs →
  ∀ omarked ws,
  dfs mmarked omarked ws →
  dfs imarked omarked (concat vs ws).
Proof.
  induction 1; intros; simpl.
  + rewrite H. assumption.
  + eauto with dfs.
Qed.

(* Conversely, if a DFS forest is the concatenation of two forests,
   then, for some intermediate state [mmarked], these two forests
   are DFS forests. When used in a forward manner, this lemma allows
   introducing a name, [mmarked], for the vertices that are marked
   after constructing [vs] and before constructing [ws]. *)

Lemma dfs_concat_inversion vs : ∀ imarked omarked ws,
  dfs imarked omarked (concat vs ws) →
  ∃ mmarked,
  dfs imarked mmarked vs ∧
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
  dfs imarked omarked (concat ws vs) →
  support vs ## support ws.
Proof.
  intros (mmarked & Hws & Hvs)%dfs_concat_inversion.
  (* The elements of [ws] are in [mmarked]. *)
  dfs_omarked.
  (* The elements of [vs] are not in [mmarked]. *)
  dfs_imarked.
  (* This is it! *)
  set_solver.
Qed.

(* -------------------------------------------------------------------------- *)

(* The following lemmas form an analysis of the relation between a
   DFS forest and the strongly connected components. *)

(* Consider the root [w] of an arbitrary tree [w/ws] in a DFS forest. Let
   [imarked] be the set of vertices discovered before this tree. (We may
   assume that [imarked] is closed.) Then, the closure of [w] is contained
   in the union of [imarked] and of the tree [w/ws]. In other words, there
   are no forward paths: [w] cannot reach the trees towards the right. *)

Lemma bound_closure_direct imarked omarked w ws vs :
  dfs imarked omarked (NonEmpty w ws vs) →
  closed_ imarked →
  closure_ {[w]} ⊆ imarked ∪ {[w]} ∪ support ws.
Proof.
  (* This is not a new key result; just a corollary of earlier results. *)
  intros hdfs. intros. dependent destruction hdfs.
  (* Let [mmarked] stand for the set of vertices that are marked after the
     tree [w/ws] has been visited. We know that [w] is a member of
     [mmarked] and that [mmarked] is closed. Thus, the closure of [w] is
     a subset of [mmarked]. Furthermore, [mmarked] is exactly the union of
     [imarked] and of the support of [w/ws]. *)
  assert (w ∈ mmarked) by (dfs_monotonic; set_solver).
  assert (closed_ mmarked) by eauto using dfs_into_closed_tree.
  eapply subset_transitive.
  + eapply prove_closure_subset with (ws := mmarked).
    - set_solver.
    - rewrite closed_path. assumption.
  + generalize (dfs_omarked_choice hdfs1); intro. set_solver.
Qed.

(* Symmetrically, an upper bound for the closure of [w] in the reverse
   graph is the support of the forest [w/ws :: vs]. Indeed, because
   [imarked] is closed, the left-hand trees cannot reach [w]. *)

(* The hypothesis [closed (flip E) omarked] states that no reverse edge
   can exit the set [omarked]. This implies that [vs] represents all of
   the trees towards the right; there are no more. To satisfy this
   hypothesis, it suffices to let [omarked] be the set of all vertices. *)

Lemma bound_closure_reverse imarked omarked w ws vs :
  dfs imarked omarked (NonEmpty w ws vs) →
  closed_ imarked →
  closed (flip E) omarked →
  closure (flip E) {[w]} ⊆ support (NonEmpty w ws vs).
Proof.
  intros hdfs hclosed huniv.
  eapply prove_closure_subset; [ simpl; set_solver |].
  erewrite dfs_determines_support; [| eauto ].
  rewrite closed_path.
  (* [closed (flip E) (omarked ∖ imarked)] is needed here, and we have
     [closed (flip E) omarked]. The latter implies the former because
     [imarked] is closed. *)
  set_solver.
Qed.

(* By combining the previous two lemmas, we find that the strongly
   connected component of [w] must be a subset of the tree [w/ws]. *)

Lemma bound_scc imarked omarked w ws vs :
  dfs imarked omarked (NonEmpty w ws vs) →
  closed_ imarked →
  closed (flip E) omarked →
  component_ w ⊆ {[w]} ∪ support ws.
Proof.
  intros hdfs hclosed huniv.
  (* By definition, [component_ w] is the intersection of the vertices
     that [w] can reach and the vertices that can reach [w]. *)
  eapply subset_transitive; [ eapply prove_subset_intersection_right | ].
  + eapply prove_component_subset_closure.
  + eapply prove_component_subset_closure_flip.
  (* The previous two lemmas provide upper bounds for the members
     of this intersection. *)
  + generalize (bound_closure_direct hdfs hclosed); intro.
    generalize (bound_closure_reverse hdfs hclosed huniv); intro.
    dfs_imarked. dfs_monotonic.
    set_solver. (* a bit slow *)
Qed.

(* Now, let us further assume that [w] is the root of the last tree in a
   DFS forest. Then, the strongly connected component of [w] is exactly
   the closure of [w] in the reverse graph. *)

Lemma last_scc {imarked omarked vs w ws} :
  dfs imarked omarked (concat vs (NonEmpty w ws Empty)) →
  closed_ imarked →
  closed (flip E) omarked →
  component_ w ≡ closure (flip E) {[w]}.
Proof.
  intros hdfs hclosed huniv.
  (* Only one inclusion is non-trivial. *)
  eapply subset_antisymmetric; [ apply prove_component_subset_closure_flip |].
  (* The strongly connected component of [w] is the intersection
     of the direct closure and reverse closure of [w]. *)
  eapply subset_transitive; [ | eapply prove_intersection_subset_component ].
  (* Thus, it suffices to prove that the reverse closure of [w]
     is a subset of its direct closure. *)
  eapply prove_subset_intersection_right; [ | set_solver ].
  (* Now, let us get rid of [vs] in the hypothesis [hdfs],
     as it plays no role. *)
  apply dfs_concat_inversion in hdfs.
  destruct hdfs as (mmarked & ? & ?).
  (* By a previous lemma, the reverse closure of [w] is a subset
     of the support of the tree [w/ws]. *)
  eapply subset_transitive; [
    eapply bound_closure_reverse; eauto using dfs_closed |].
  (* Thus, there remains to show that [w] reaches [w/ws]. *)
  simpl. eauto using reaches_root_support with reaches.
Qed.

(* The following lemma is a stronger version of [bound_closure_direct]. If
   [w/ws] is an arbitrary tree in the forest, then, under the assumption
   that [imarked] is closed both ways, the closure of [w] is exactly the
   set [w/ws]. *)

Lemma exact_closure imarked omarked w ws vs :
  dfs imarked omarked (NonEmpty w ws vs) →
  closed_ imarked →
  closed (flip E) imarked →
  closure_ {[w]} ≡ {[w]} ∪ support ws.
Proof.
  intros hdfs hci hrci. intros. eapply subset_antisymmetric.
  (* This inclusion follows from [bound_closure_direct], with the
     additional proviso that there is no overlap with [imarked]. [w] is
     not in [imarked], and the hypothesis that [imarked] is reverse-closed
     ensures that the closure of [w] lies outside [imarked]. *)
  { generalize (bound_closure_direct hdfs hci); intro.
    assert (w ∉ imarked) by eauto using root_is_unmarked.
    assert (fact: closed_ (⊤ ∖ imarked)) by set_solver.
    rewrite <- closed_path in fact. (* no escape *)
    set_solver. }
  (* Now, the reverse inclusion is easy. *)
  { eauto using reaches_root_support with reaches. }
Qed.

End D.

Hint Constructors dfs : dfs.

(* -------------------------------------------------------------------------- *)

(* If two DFS forests agree on the sets [imarked] and [omarked], then they
   have the same support. *)

Lemma dfs_same_support {V} (E1 E2 : V → V → Prop) imarked omarked f1 f2 :
  dfs E1 imarked omarked f1 →
  dfs E2 imarked omarked f2 →
  support f1 ≡ support f2.
Proof.
  intros. erewrite !dfs_determines_support by eauto. eauto.
Qed.

(* [dfs] is compatible with relation equivalence. *)

Lemma dfs_eqrel {V} (E1 E2 : V → V → Prop) imarked omarked f :
  relation_equivalence E1 E2 →
  dfs E1 imarked omarked f →
  dfs E2 imarked omarked f.
Proof.
  intros Hrequiv.
  induction 1; econstructor;
  rewrite <- ?Hrequiv; eauto.
Qed.

Global Instance Proper_dfs_rel {V} :
  Proper (relation_equivalence ==> eq ==> eq ==> eq ==> iff) (@dfs V).
Proof.
  intros E1 E2 Hrequiv.
  intros imarked1 imarked2 ? omarked1 omarked2 ? f1 f2 ?. subst.
  split; eapply dfs_eqrel.
  + eauto.
  + symmetry. eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* The tactic [dfs1] states that the goal should be proved up to an
   equality in the first parameter of [dfs], that is, [imarked]. It
   creates a fresh metavariable. Its first subgoal is a [dfs] goal.
   Its second subgoal is an equality. *)

Ltac dfs1 :=
  match goal with |- @dfs ?V _ ?imarked2 _ ?vs =>
    let imarked1 := fresh "imarked" in
    evar (imarked1 : set V);
    cut (imarked1 ≡ imarked2);
    subst imarked1;
    [ intros <- |]
  end.

(* The tactic [dfs2] is similar, but concerns the second parameter,
   that is, [omarked]. *)

Ltac dfs2 :=
  match goal with |- @dfs ?V _ _ ?omarked2 ?vs =>
    let omarked1 := fresh "omarked" in
    evar (omarked1 : set V);
    cut (omarked1 ≡ omarked2);
    subst omarked1;
    [ intros <- |]
  end.

Ltac dfs_monotonic :=
  repeat match goal with
  h: dfs _ _ _ _ |- _ =>
    generalize (dfs_monotonic h); revert h
  end;
  intros.

Ltac dfs_imarked :=
  repeat match goal with h: dfs _ _ _ _ |- _ =>
    generalize (dfs_imarked h); revert h
  end;
  intros.

Ltac dfs_omarked :=
  repeat match goal with h: dfs _ _ _ _ |- _ =>
    generalize (dfs_omarked h); revert h
  end;
  intros.

Arguments Empty {V}.

(* -------------------------------------------------------------------------- *)

(* (New in 2026!) The above results describe the structure of a complete DFS
   forest. However, in order to describe an interactive traversal, where a
   producer performs the traversal and emits events, and where a consumer
   observes these events, it is desirable to have a small-step description,
   that is, a labeled transition system whose state represents an ongoing
   (incomplete) DFS traversal. *)

Section Interactive.
Variable V : Type.
Variable E : V → V → Prop.
Local Notation dfs := (@dfs V E).

(* We work with two kinds of observable events. [Enter v] means that the
   vertex [v] has just been discovered and entered; we are about to
   explore its successors. [Exit v] means that all of the descendants of
   [v] have been explored; we about to come back up out of [v]. The
   sequence of all [Enter] events is a "pre-order" enumeration of the
   vertices; the sequence of all [Exit] events is a "post-order"
   enumeration of the vertices. *)

Inductive event :=
| Enter : V → event
| Exit  : V → event.

(* A stack is a (nonempty) list of stack frames. *)

(* A stack frame contains an optional vertex [ov] and a forest [vs]. *)

(* When [ov] is [None], one can think of it as a special vertex that
   represents the entry point of the entire traversal. The successors of
   this entry vertex are the start vertices of the traversal. This entry
   vertex has no incoming edges. *)

(* The forest [vs] represents the descendants of [ov] that have been
   explored already. *)

(* A well-formed stack must have at least one frame; it cannot be empty. In
   a well-formed stack, the bottom frame must have [ov = None], and only the
   bottom frame can have [ov = None]. One might wonder whether one should
   adopt a different representation of stacks, where these properties are
   built in. However, the current representation lets us inspect the top
   frame without wondering whether it is or is not also the bottom frame.
   Things are likely to be slightly painful either way. *)

Inductive frame :=
| Frame : option V → forest V → frame.

Definition stack :=
  list frame.

Implicit Type ov : option V.
Implicit Type σ : stack.

(* The start vertices of the traversal. *)

Variable start : set V.

(* [edge ov w] means that there is an edge from [ov] to [w] in the graph
   [E], extended with an edge of the entry vertex [None] to every start
   vertex. *)

Definition edge ov w :=
  match ov with
  | Some v => E v w
  | None   => w ∈ start
  end.

(* The trace of a stack is the set of vertices that appear directly in the
   stack frames (ignoring the subforests that hang off of a stack frame).
   In other words, it is the set of vertices that are currently being
   visited -- the grey vertices. *)

Fixpoint trace σ : set V :=
  match σ with
  | [] => ∅
  | Frame ov _ :: σ => option_to_set ov ∪ trace σ
  end.

(* The support of a stack is the set of vertices that appear in a stack
   frame or in a subforest hanging off of a stack frame. *)

Fixpoint support_stack σ : set V :=
  match σ with
  | [] => ∅
  | Frame ov vs :: σ => option_to_set ov ∪ support vs ∪ support_stack σ
  end.

(* [top σ] is the vertex found in the top frame of the stack [σ]. *)

Definition top σ : option V :=
  match σ with
  | Frame ov vs :: _ => ov
  | []               => None (* dummy; cannot happen *)
  end.

(* [store w ws σ] appends the tree [w/ws] to the forest
   that is stored in the top frame of the stack [σ]. *)

Definition store w ws σ : stack :=
  match σ with
  | [] =>
      [] (* cannot happen *)
  | Frame ov vs :: σ =>
      Frame ov (concat vs (NonEmpty w ws Empty)) :: σ
  end.

Lemma length_store σ w ws :
  length (store w ws σ) = length σ.
Proof.
  destruct σ as [| [ov vs]]; simpl store; length; eauto.
Qed.

(* The labeled transition system [step] describes the evolution of the
   state, and the corresponding observable events, as the depth-first
   search traversal progresses. *)

(* A state [γ] is a pair of a set of vertices [marked] and a stack [σ]. *)

Definition state : Type :=
  (set V * stack).

Implicit Type γ : state.

(* [step γ e γ'] means that the system can evolve from [γ] to [γ']] while
   emitting the observable event [e]. *)

Inductive step : state → event → state → Prop :=

| StepEnter:
    ∀ marked σ marked' σ' w,
    (* If [w] is an unmarked child of the top stack vertex, *)
    edge (top σ) w →
    w ∉ marked →
    (* then [w] can be marked *)
    marked' ≡ {[w]} ∪ marked →
    (* and a new frame, carrying [w] together with an empty forest,
       can be pushed onto the stack. *)
    σ' = Frame (Some w) Empty :: σ →
    (* This transition corresponds to the event [Enter w]. *)
    step
      (marked, σ)
      (Enter w)
      (marked', σ')

| StepExit:
    ∀ marked σ w ws σ0 marked' σ',
    (* Suppose the top stack frame contains [w] and its children [ws]. *)
    σ = Frame (Some w) ws :: σ0 →
    (* If all children of [w] are marked *)
    {[x | E w x]} ⊆ marked →
    (* then the top stack frame can be popped, and the tree [w/ws] can be
       stored in the previous frame. *)
    σ' = store w ws σ0 →
    (* The set of marked vertices is unchanged. *)
    marked' ≡ marked →
    (* This transition corresponds to the event [Exit w]. *)
    step
      (marked, σ)
      (Exit w)
      (marked', σ').

(* Not every stack is well-formed. A stack is well-formed only if it
   corresponds to the beginning of a well-formed DFS forest. *)

(* [wf imarked (omarked, σ)] means that the state [(omarked, σ)] is
   well-formed: starting with the set of marked vertices [imarked],
   one may reach a state where the set of marked vertices is [omarked]
   and the stack is [σ]. *)

Inductive wf : set V → state → Prop :=

| WfNil:
    ∀ imarked omarked vs ,
    (* If [vs] is a well-formed DFS forest *)
    dfs imarked omarked vs →
    (* and if every root of [vs] is a start vertex *)
    roots vs ⊆ start →
    (* then a stack that consists of just one frame, containing the entry
       vertex [None] and the forest [vs], is well-formed. *)
    wf imarked (omarked, Frame None vs :: [])

| WfDeep:
    ∀ imarked mmarked σ omarked w ws ,
    (* If the stack [σ] is well-formed, *)
    wf imarked (mmarked, σ) →
    (* If [w] is an unmarked child of the top stack vertex, *)
    edge (top σ) w →
    w ∉ mmarked →
    (* If, after marking [w], a forest [ws] of children of [w] has
       been traversed, *)
    dfs ({[w]} ∪ mmarked) omarked ws →
    outof E {[w]} (roots ws) →
    (* Then the stack [σ], extended with one frame that contains [w]
       and [ws], is well-formed. *)
    wf imarked (omarked, Frame (Some w) ws :: σ).

Local Hint Constructors wf : wf.

(* A state [(marked, σ)] is final if every start vertex is marked and
   [σ] consists of a single frame. If this state is well-formed, then
   the fact that there is a single frame can be expressed by writing
   [top σ = None]. *)

Inductive final : state → Prop :=
| Final :
    ∀ marked σ,
    start ⊆ marked →
    top σ = None →
    final (marked, σ).

(* Hints for the proofs that follow. *)

Local Hint Resolve dfs_concat : dfs.

Local Hint Extern 1 (roots (concat _ _) ⊆ _) =>
  rewrite roots_concat
: set_solver.

(* The set of marked vertices grows over time. *)

Lemma wf_monotonic imarked γ :
  wf imarked γ →
  ∀ omarked σ,
  γ = (omarked, σ) →
  imarked ⊆ omarked.
Proof.
  induction 1; intros ?? Heq;
  injection Heq; clear Heq; intros <- <-;
  dfs_monotonic; set_solver.
Qed.

Ltac wf_monotonic :=
  repeat match goal with
  h: wf _ _ |- _ =>
    generalize (wf_monotonic h eq_refl); revert h
  end;
  intros.

(* The vertices found in the support of the stack were not marked
   initially. *)

Lemma wf_imarked imarked γ :
  wf imarked γ →
  ∀ omarked σ,
  γ = (omarked, σ) →
  support_stack σ ## imarked.
Proof.
  induction 1; intros ?? Heq;
  injection Heq; clear Heq; intros <- <-;
  [| specialize (IHwf _ _ eq_refl) ];
  simpl support_stack.
  { dfs_imarked. set_solver. }
  { wf_monotonic. dfs_imarked. dfs_omarked. set_solver. }
Qed.

Ltac wf_imarked :=
  repeat match goal with h: wf _ _ |- _ =>
    generalize (wf_imarked h eq_refl); revert h
  end;
  intros.

(* A stack that contains just one empty frame is well-formed. *)

Lemma wf_init :
  ∀ imarked,
  wf imarked (imarked, Frame None Empty :: []).
Proof.
  intros. eapply WfNil; eauto with dfs set_solver.
Qed.

(* The transition system preserves well-formedness. *)

Lemma wf_step :
  ∀ γ e γ',
  step γ e γ' →
  ∀ imarked,
  wf imarked γ →
  wf imarked γ'.
Proof.
  induction 1; intros imarked Hwf; dependent destruction Hwf.
  (* Case: [StepEnter/WfNil]. *)
  { eauto with wf dfs set_solver. }
  (* Case: [StepEnter/WfDeep]. *)
  { eauto with wf dfs set_solver. }
  (* Case: [StepExit/WfDeep]. *)
  { dependent destruction Hwf.
    (* Subcase: [WfNil]. [ov] is [None]. *)
    { eapply WfNil; eauto with dfs set_solver. }
    (* Subcase: [WfNil]. [ov] is [None]. *)
    { eapply WfDeep; eauto with dfs set_solver. }}
Qed.

(* If the stack has just one frame then this frame holds a DFS forest [vs]
   whose roots form a subset of [start]. *)

Lemma wf_completion imarked omarked σ :
  wf imarked (omarked, σ) →
  top σ = None →
  ∃ vs,
  σ = Frame None vs :: [] ∧
  dfs imarked omarked vs ∧
  roots vs ⊆ start.
Proof.
  intros Hwf ?. dependent destruction Hwf.
  { eauto. }
  { exfalso. simpl in *. congruence. }
Qed.

(* The trace of a well-formed stack is a subset of [omarked ∖ imarked]. *)

(* In other words, every vertex in the trace is marked. *)

Lemma wf_trace_marked imarked γ :
  wf imarked γ →
  ∀ omarked σ,
  γ = (omarked, σ) →
  trace σ ⊆ omarked ∖ imarked.
Proof.
  induction 1; intros ?? Heq;
  injection Heq; clear Heq; intros <- <-;
  [| specialize (IHwf _ _ eq_refl) ];
  simpl trace.
  { set_solver. }
  { wf_monotonic. dfs_monotonic. set_solver. }
Qed.

(* The top vertex [top σ] is part of the trace. *)

(* Therefore it is marked. *)

Lemma wf_top_trace σ :
  option_to_set (top σ) ⊆ trace σ.
Proof.
  induction σ as [| [ ? ?] σ ]; simpl; set_solver.
Qed.

Lemma wf_top_marked imarked omarked σ :
  wf imarked (omarked, σ) →
  option_to_set (top σ) ⊆ omarked ∖ imarked.
Proof.
  intros Hwf. transitivity (trace σ).
  + eapply wf_top_trace.
  + eauto using wf_trace_marked.
Qed.

Lemma wf_top_marked' imarked omarked σ :
  wf imarked (omarked, σ) →
  option_to_set (top σ) ⊆ omarked.
Proof.
  intros. transitivity (omarked ∖ imarked).
  + eauto using wf_top_marked.
  + set_solver.
Qed.

(* If one starts from an empty set of marked vertices, then at any
   time, the marked vertices are reachable from the start vertices,
   and so is the vertex [top σ]. (In fact, every vertex) *)

Lemma wf_reaches γ :
  wf ∅ γ →
  ∀ omarked σ ,
  γ = (omarked, σ) →
  reaches E start omarked. (* [omarked ⊆ closure E start] *)
Proof.
  (* This proof feels abnormally difficult. Maybe we are missing some
     lemmas, or maybe they exist but I did not find them. *)
  intros Hwf. dependent induction Hwf;
  match goal with h: dfs _ _ _ |- _ => rename h into Hdfs end;
  intros ?? Heq;
  injection Heq; clear Heq; intros <- <-;
  dfs_monotonic;
  generalize (dfs_determines_omarked Hdfs);
  generalize (reaches_roots_support Hdfs);
  intros.
  (* Case [WfNil]. *)
  { set_solver. }
  (* Case [WfDeep]. *)
  { specialize (IHHwf eq_refl mmarked σ eq_refl).
    (* [top σ] is marked, therefore is reachable. *)
    assert (option_to_set (top σ) ⊆ mmarked) by eauto using wf_top_marked'.
    (* Because [w] is a successor of [top σ], [w] is reachable, too. *)
    assert (reaches E start {[w]}).
    { destruct (top σ) eqn:Heq; unfold edge in *.
      + assert (reaches E {[v]} {[w]})
          by eauto using prove_reaches_singleton_singleton.
        eauto using reaches_transitive, subset_transitive.
      + eauto using prove_reaches_self with set_solver. }
    (* [w] reaches its successors. *)
    assert (image E {[w]} ⊆ closure E {[w]}).
    { eauto using prove_image_subset_closure. }
    (* Therefore [w] reaches [roots ws]. *)
    assert (reaches E {[w]} (roots ws)).
    { set_solver. }
    (* [start] reaches [w] reaches [roots ws] reaches [support ws]. *)
    assert (reaches E start (support ws))
      by eauto using reaches_transitive.
    (* The result follows. *)
    set_solver. }
Qed.

(* A corollary. *)

Lemma wf_reaches' omarked σ w :
  wf ∅ (omarked, σ) →
  edge (top σ) w →
  reaches E start (omarked ∪ {[w]}).
Proof.
  (* Also abnormally difficult. *)
  intros Hwf Hedge.
  generalize (wf_reaches Hwf eq_refl); intros Homarked.
  eapply prove_subset_union_left; [ exact Homarked |].
  assert (option_to_set (top σ) ⊆ omarked) by eauto using wf_top_marked'.
  destruct (top σ); unfold edge in *; simpl in *.
  + assert (reaches E {[v]} {[w]})
      by eauto using prove_reaches_singleton_singleton.
    eauto using reaches_transitive, subset_transitive.
  + eauto using prove_reaches_self with set_solver.
Qed.

(* A well-formed stack has length at least 1. *)

Lemma wf_nonempty imarked omarked σ :
  wf imarked (omarked, σ) →
  1 ≤ length σ.
Proof.
  intros Hwf. dependent destruction Hwf; subst; length.
  + lia.
  + unfold stack in *. lengths. lia.
Qed.

(* Between the moment where a vertex is entered and the moment where this
   vertex is exited, the stack does not change at all, except possibly in
   the top frame, where new trees can be stored. *)

(* The proposition [similar σ σ'] describes this evolution. *)

Inductive similar : stack → stack → Prop :=
| Sim :
    ∀ ov vs1 vs2 vs σ,
    concat vs1 vs2 = vs →
    similar (Frame ov vs1 :: σ) (Frame ov vs :: σ).

(* [similar] is reflexive, except in the special case of an empty stack,
   which is not well-formed. *)

Lemma similar_reflexive imarked omarked σ :
  wf imarked (omarked, σ) →
  similar σ σ.
Proof.
  inversion 1; subst;
  eapply Sim with (vs2 := Empty);
  eapply concat_empty.
Qed.

(* [similar] is transitive. *)

Lemma similar_transitive σ1 σ2 σ3 :
  similar σ1 σ2 →
  similar σ2 σ3 →
  similar σ1 σ3.
Proof.
  inversion 1; inversion 1; subst. econstructor.
  rewrite concat_associative. eauto.
Qed.

(* Two similar stacks have the same top vertex. *)

Lemma similar_same_top σ σ' :
  similar σ σ' →
  top σ = top σ'.
Proof.
  inversion 1. simpl. eauto.
Qed.

(* Two similar stacks have the same edges exiting the top vertex. *)

Lemma similar_same_edges σ σ' w :
  similar σ σ' → edge (top σ) w → edge (top σ') w.
Proof.
  intros.
  assert (top σ = top σ') by eauto using similar_same_top.
   congruence.
Qed.

(* Storing a tree [w/ws] into a stack [σ] is permitted by [similar]. *)

Lemma similar_store imarked omarked w ws σ :
  wf imarked (omarked, σ) →
  similar σ (store w ws σ).
Proof.
  inversion 1; subst; simpl; econstructor; eauto.
Qed.

(* A corollary of [wf_completion]. *)

Lemma wf_completion' imarked omarked σ σ' :
  wf imarked (omarked, σ') →
  similar σ σ' →
  σ = Frame None Empty :: [] →
  ∃ vs,
  σ' = Frame None vs :: [] ∧
  dfs imarked omarked vs ∧
  roots vs ⊆ start.
Proof.
  intros Hwf Hsimilar ?. subst.
  assert (top σ' = None).
  { dependent destruction Hsimilar. eauto. }
  eauto using wf_completion.
Qed.

(* If [(marked', σ')] is well-formed, similar to the initial state,
   and has marked all of the start vertices, then it is a final state. *)

Lemma wf_similar_final marked' σ' :
  wf ∅ (marked', σ') →
  similar [Frame None Empty] σ' →
  start ⊆ marked' →
  final (marked', σ').
Proof.
  intros Hwf Hsimilar ?.
  dependent destruction Hsimilar.
  dependent destruction Hwf.
  econstructor; eauto.
Qed.

(* The postorder enumeration of the vertices in a stack. *)

Fixpoint postorder_stack (σ : stack) :=
  match σ with
  | [] =>
      []
  | Frame ov vs :: σ =>
      (* The optional vertex [ov] is NOT part of the postorder enumeration:
         it will become part of this enumeration only when this stack frame
         is popped. *)
      postorder_stack σ ++ postorder vs
  end.

Lemma postorder_stack_store imarked omarked v ws σ :
  wf imarked (omarked, σ) →
  postorder_stack (store v ws σ) =
  postorder_stack σ ++ postorder ws ++ {[v]}.
Proof.
  intros Hwf. dependent destruction Hwf; unfold store; simpl;
  rewrite postorder_concat; simpl; list; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* [bottom σ] is the vertex found in the second frame of the stack [σ],
   starting from the bottom. (The bottommost frame does not contain a
   vertex.) *)

Fixpoint bottom σ : option V :=
  match σ with
  | Frame ov vs :: Frame _ _ :: [] => ov
  |                Frame _ _ :: [] => None
  |                             [] => None
  | Frame ov vs :: σ               => bottom σ
  end.

(* If the stack [σ] is well-formed and has exactly two frames, then
   its bottom vertex is found in its top frame. *)

Lemma bottom_two imarked omarked ov vs σ :
  wf imarked (omarked, Frame ov vs :: σ) →
  length σ = 1 →
  bottom (Frame ov vs :: σ) = ov.
Proof.
  intros Hwf Hlen.
  dependent destruction Hwf; [ eauto |].
  dependent destruction Hwf; [ eauto | exfalso].
  apply wf_nonempty in Hwf. length in Hlen. lia.
Qed.

(* If the stack [σ] is well-formed and has at least two frames, then
   pushing a new frame onto it does not change its bottom vertex. *)

Lemma bottom_push imarked omarked ov vs σ :
  wf imarked (omarked, Frame ov vs :: σ) →
  length σ ≠ 1 →
  bottom (Frame ov vs :: σ) = bottom σ.
Proof.
  (* I had difficulty finding this proof. *)
  intros Hwf Hlen.
  dependent destruction Hwf; [ eauto |].
  dependent destruction Hwf; [ length in Hlen; lia |].
  destruct σ0 as [| [ ? ? ] ? ].
  { exfalso. dependent destruction Hwf. }
  eauto.
Qed.

(* A combination of the previous two lemmas. *)

Lemma bottom_eq imarked omarked ov vs σ :
  wf imarked (omarked, Frame ov vs :: σ) →
  bottom (Frame ov vs :: σ) =
    if decide (length σ = 1) then ov else bottom σ.
Proof.
  intros. case (decide (length σ = 1)); intro.
  + erewrite bottom_two by eauto. reflexivity.
  + erewrite bottom_push by eauto. reflexivity.
Qed.

(* Storing a new tree into the top stack frame does not affect [bottom]. *)

Lemma bottom_store v vs σ :
  bottom (store v vs σ) = bottom σ.
Proof.
  destruct σ as [| [ ow ws ] σ ]; eauto.
Qed.

Lemma bottom_frame_concat v vs w ws σ :
  bottom (Frame (Some v) (concat vs (NonEmpty w ws Empty)) :: σ) =
  bottom (Frame (Some v) vs :: σ).
Proof.
  reflexivity.
Qed.

(* The bottom vertex [bottom σ] is part of the trace. *)

(* Therefore it is marked. *)

Lemma wf_bottom_trace imarked γ :
  wf imarked γ →
  ∀ omarked σ,
  γ = (omarked, σ) →
  option_to_set (bottom σ) ⊆ trace σ.
Proof.
  induction 1; intros ?? Heq;
  injection Heq; clear Heq; intros <- <-;
  [| specialize (IHwf _ _ eq_refl) ].
  { set_solver. }
  { match goal with h: wf _ _ |- _ => dependent destruction h end.
    { set_solver. }
    match goal with foo: stack |- _ => rename foo into σ end.
    assert (1 ≤ length σ) by eauto using wf_nonempty.
    erewrite bottom_push by (length; eauto with wf lia).
    rewrite IHwf. simpl trace. set_solver. }
Qed.

(* The bottom stack vertex is marked. *)

Lemma wf_bottom_marked imarked omarked σ :
  wf imarked (omarked, σ) →
  option_to_set (bottom σ) ⊆ omarked ∖ imarked.
Proof.
  intros Hwf. transitivity (trace σ).
  + eauto using wf_bottom_trace.
  + eauto using wf_trace_marked.
Qed.

Lemma wf_bottom_marked' imarked omarked σ :
  wf imarked (omarked, σ) →
  option_to_set (bottom σ) ⊆ omarked.
Proof.
  intros Hwf. transitivity (omarked ∖ imarked).
  + eauto using wf_bottom_marked.
  + set_solver.
Qed.

(* If the stack has at least three frames then the top vertex and the
   bottom vertex must be distinct. *)

Lemma wf_top_ne_bottom imarked omarked v vs σ w :
  wf imarked (omarked, Frame (Some v) vs :: σ) →
  bottom σ = Some w →
  v ≠ w.
Proof.
  intros Hwf Hbottom.
  destruction Hwf.
  (* We have [v ∉ mmarked], but [w ∈ mmarked], therefore [v ≠ w]. *)
  assert (w ∈ mmarked).
  { match goal with h: wf _ _ |- _ => clear Hwf; rename h into Hwf end.
    generalize (wf_bottom_marked' Hwf); intro Hmarked.
    rewrite Hbottom in Hmarked.
    simpl in Hmarked. set_solver. }
  set_solver.
Qed.

(* If [σ] is well-formed then [top σ = None] is equivalent to
   [length σ = 1]. *)

(* This condition itself is equivalent to [length σ ≤ 1]. *)

Lemma top_None imarked omarked σ :
  wf imarked (omarked, σ) →
  top σ = None ↔
  length σ = 1.
Proof.
  intros Hwf. destruction Hwf; simpl; length.
  { tauto. }
  { match goal with h: wf _ _ |- _ => eapply wf_nonempty in h end.
    assert (Some w ≠ None) by congruence.
    assert (length σ0 + 1 ≠ 1) by lia.
    tauto. }
Qed.

(* If [σ] is well-formed then [bottom σ = None] is equivalent to
   [length σ = 1]. *)

Lemma bottom_None imarked γ :
  wf imarked γ →
  ∀ omarked σ,
  γ = (omarked, σ) →
  bottom σ = None ↔
  length σ = 1.
Proof.
  induction 1; intros ?? Heq;
  injection Heq; clear Heq; intros <- <-;
  [| specialize (IHwf _ _ eq_refl) ];
  simpl top; length.
  { tauto. }
  { erewrite bottom_eq by eauto with wf.
    match goal with h: wf _ _ |- _ =>
      generalize (wf_nonempty h); intro end.
    assert (Some w ≠ None) by congruence.
    case (decide (length σ = 1)); intro;
    case (decide (length σ + 1 = 1)); intro;
    try lia; try tauto. }
Qed.

(* -------------------------------------------------------------------------- *)

(* The predicate [ordered rs f], which concerns forests, is extended to
   stacks. The predicate [ordered_stack rs σ] depends only on the bottom
   one or two frames. In short, it states that the forest [vs] stored in
   frame 0 and the bottom vertex [v] stored in frame 1 should be ordered
   by [rs]. *)

(* One might wonder whether these conditions should be built into the
   predicate [wf], so that there would be no need for a separate predicate
   [ordered_stack]. For now, it seems preferable to keep them separate. *)

Inductive ordered_stack : list V → stack → Prop :=
| OrderedStackNil:
    (* In the special bottom frame, which stores a forest [vs], we require
       this forest to be ordered by [rs]. We further require [list_to_set
       rs ⊆ support vs], which means that all of the root vertices that
       have been enumerated so far are part of [vs]. This requirement is
       exploited in the proof of the lemma [ordered_stack_exit]. *)
    ∀ rs vs,
    ordered rs vs →
    list_to_set rs ⊆ support vs →
    ordered_stack rs (Frame None vs :: [])
| OrderedStackDeep:
    (* If [w] is the bottom vertex of the stack then we require [w] to
       be the last element of [rs]; otherwise we ignore this frame. *)
    ∀ rs' w ws rs σ,
    ordered_stack rs' σ →
    (rs = if decide (length σ = 1) then rs' ++ {[w]} else rs') →
    ordered_stack rs (Frame (Some w) ws :: σ).

(* [ordered_stack] is true initially. *)

Lemma ordered_stack_init :
  ordered_stack [] (Frame None Empty :: []).
Proof.
  econstructor; [ econstructor | set_solver ].
Qed.

(* [ordered_stack] is preserved by an [Exit] step. *)

Lemma ordered_stack_exit rs imarked marked σ w marked' σ' :
  ordered_stack rs σ →
  wf imarked (marked, σ) →
  step (marked, σ) (Exit w) (marked', σ') →
  ordered_stack rs σ'.
Proof.
  (* The proof is not difficult in principle, but quite painful
     in actuality, perhaps because viewing a stack as a list of
     frames is not a good idea. *)
  destruct 1; intros Hwf Hstep; dependent destruction Hstep.
  dependent destruction Hwf.
  match goal with foo: stack |- _ => rename foo into σ end.
  generalize (wf_nonempty Hwf); intro.
  case_decide.
  (* Case: [length σ = 1]. We are pushing a complete tree
     into the bottom stack frame. *)
  { destruct σ as [| [ ov vs ] σ ]; [ length in *; lia |].
    destruct σ as [|]; [| length in *; lengths; lia ].
    (* [ov] must be [None]. *)
    rewrite <- top_None in * by eauto. simpl in *. subst ov.
    dependent destruction Hwf.
    match goal with h: ordered_stack _ _ |- _ =>
      dependent destruction h end.
    econstructor.
    + eapply ordered_concat; eauto.
      - simpl support. dfs_imarked. dfs_omarked. set_solver.
      - change {[w]} with ({[w]} ++ []).
        eapply OrderedRoot. econstructor.
    + rewrite support_concat, list_to_set_app, list_to_set_singleton.
      set_solver. }
  (* Case: [length σ ≠ 1]. There are at least two frames. *)
  { destruct σ as [| [ ? ? ] σ ]; [ length in *; lia |].
    destruct σ as [| [ ? ? ] σ ]; [ length in *; lengths; lia |].
    simpl in *.
    match goal with h: ordered_stack _ _ |- _ =>
      dependent destruction h end.
    (* Are there two frames, or more than two? *)
    case_decide.
    (* Subcase: there are two. *)
    { destruct σ; [| length in *; lengths; lia ].
      econstructor; length; eauto. }
    (* Subcase: there are more than two. In this case [ordered_stack] is
       insensitive to the top frame. *)
    { econstructor; length in *; eauto.
      case_decide; eauto with lia. }}
Qed.

(* -------------------------------------------------------------------------- *)

(* [isRootMap ρ vs] means that [ρ], a map of vertices to vertices,
   correctly records the root of every vertex in [vs]. That is, every
   vertex [v] in the forest [vs] is mapped to the root of its tree in
   [vs]. *)

Inductive isRootMap (ρ : V → V) : forest V → Prop :=
| IsRootMapEmpty :
    isRootMap ρ Empty
| IsRootMapNonEmpty :
    ∀ w ws vs,
    (∀ w', w' ∈ {[w]} ∪ support ws → ρ w' = w) →
    isRootMap ρ vs →
    isRootMap ρ (NonEmpty w ws vs).

(* [isRootMapStack ρ σ] means that [ρ] correctly records the root of every
   vertex in the stack [σ]. *)

Inductive isRootMapStack (ρ : V → V) : stack → Prop :=
| IsRootListOneFrame :
    (* In the bottom frame, we require [ρ] to be a correct
       root map for the forest [vs]. *)
    ∀ vs,
    isRootMap ρ vs →
    isRootMapStack ρ (Frame None vs :: [])
| IsRootListSeveralFrames :
    (* In every other frame, we require [w] and [ws] to be mapped to the
       bottom vertex of the stack, namely [v], as this vertex will become
       the root of the tree that is being constructed. *)
    (* In this case, [σ] must be nonempty. *)
    ∀ v w ws σ,
    isRootMapStack ρ σ →
    bottom (Frame (Some w) ws :: σ) = Some v →
    (∀ w', w' ∈ {[w]} ∪ support ws → ρ w' = v) →
    isRootMapStack ρ (Frame (Some w) ws :: σ).

Hint Constructors isRootMap isRootMapStack : isRootMap.

(* A trivial lemma. *)

Lemma isRootMap_concat ρ f1 f2 :
  isRootMap ρ f1 →
  isRootMap ρ f2 →
  isRootMap ρ (concat f1 f2).
Proof.
  induction 1; simpl concat; intros; [ eauto |].
  econstructor; eauto.
Qed.

Hint Resolve isRootMap_concat : isRootMap.

(* [isRootMapStack] holds of an arbitrary roots map and an empty stack. *)

Lemma isRootMapStack_init ρ :
  isRootMapStack ρ [Frame None Empty].
Proof.
  econstructor. econstructor.
Qed.

(* [isRootMapStack] is preserved by [Exit] transitions. *)

Lemma isRootMapStack_store imarked omarked ρ w ws σ :
  wf imarked (omarked, Frame (Some w) ws :: σ) →
  isRootMapStack ρ (Frame (Some w) ws :: σ) →
  isRootMapStack ρ (store w ws σ).
Proof using.
  intros Hwf Hroots.
  dependent destruction Hroots.
  generalize Hwf; intro Hcopy.
  dependent destruction Hwf.
  dependent destruction Hwf.
  { dependent destruction Hroots. simpl in *.
    assert (w = v) by congruence. subst w.
    unfold store. eauto with isRootMap. }
  { match goal with foo: stack |- _ => rename foo into σ end.
    assert (1 ≤ length σ) by eauto using wf_nonempty.
    erewrite bottom_push in * by (length; eauto with lia).
    dependent destruction Hroots.
    match goal with h1: bottom _ = Some ?v1,
                    h2: bottom _ = Some ?v2 |- _ =>
      assert (v1 = v2) by congruence; subst v1; clear h1
    end.
    match goal with h1: ∀ w' : V, _, h2: ∀ w' : V, _ |- _ =>
      rename h2 into Htop; rename h1 into Hnext end.
    unfold store. econstructor.
    { assumption. }
    { rewrite bottom_frame_concat. eauto. }
    { intros w' Hw'.
      rewrite support_concat in Hw'. simpl support in Hw'.
      set_unfold in Hw'.
      repeat destruct Hw' as [Hw'|Hw']; last tauto.
      + eapply Hnext. eauto with set_solver.
      + eapply Hnext. eauto with set_solver.
      + eapply Htop. eauto with set_solver.
      + eapply Htop. eauto 2 with set_solver. }}
Qed.

(* When it is applied to a well-formed forest, [isRootMap] is
   insensitive to the value of the function [ρ] outside of the set
   [omarked ∖ imarked]. In other words, the value of [ρ w] matters
   only when [w] is marked. *)

Lemma isRootMap_domain ρ vs :
  isRootMap ρ vs →
  ∀ ρ' imarked omarked,
  dfs imarked omarked vs →
  (∀ w, w ∈ omarked ∖ imarked → ρ' w = ρ w) →
  isRootMap ρ' vs.
Proof.
  induction 1; inversion 1; intros Himpl; subst.
  { econstructor. }
  { dfs_monotonic.
    econstructor; intros.
    + dfs_imarked. dfs_omarked.
      rewrite Himpl by set_solver. eauto.
    + eauto with set_solver. }
Qed.

(* A similar result about [isRootMapStack]. *)

Lemma isRootMapStack_domain ρ σ :
  isRootMapStack ρ σ →
  ∀ ρ' imarked omarked,
  wf imarked (omarked, σ) →
  (∀ w, w ∈ omarked ∖ imarked → ρ' w = ρ w) →
  isRootMapStack ρ' σ.
Proof.
  induction 1; inversion 1; intros Himpl; subst.
  { econstructor. eauto using isRootMap_domain. }
  { dfs_monotonic.
    econstructor; eauto.
    + eauto with set_solver.
    + wf_imarked. dfs_omarked.
      rewrite Himpl by eauto with set_solver.
      eauto. }
Qed.

Lemma isRootMapStack_domain' ρ σ :
  isRootMapStack ρ σ →
  ∀ ρ' imarked omarked,
  wf imarked (omarked, σ) →
  (∀ w, w ∈ omarked → ρ' w = ρ w) →
  isRootMapStack ρ' σ.
Proof.
  eauto using isRootMapStack_domain with set_solver.
Qed.

(* Updating a partial root map with one vertex [v]. *)

Lemma isRootMapStack_update `{EqDecision V} imarked omarked σ ρ ρ' σ' v root' :
  isRootMapStack ρ σ →
  σ' = Frame (Some v) Empty :: σ →
  wf imarked (omarked, σ') →
  bottom σ' = Some root' →
  ρ' v = root' →
  (∀ v', v' ≠ v → ρ' v' = ρ v') →
  isRootMapStack ρ' σ'.
Proof.
  intros ?? Hwf ???. subst. dependent destruction Hwf.
  econstructor.
  { eapply isRootMapStack_domain'; eauto.
    intros w Hw. case (decide (w = v)).
    + intros ->. exfalso. tauto. (* [v ∈ mmarked ∧ v ∉ mmarked] *)
    + intros. eauto. }
  { eassumption. }
  { simpl support. intros w' Hw'. set_unfold in Hw'.
    assert (w' = v) by tauto. clear Hw'. subst w'.
    reflexivity. }
Qed.

(* Once the stack becomes empty, [isRootMapStack] implies [isRootMap]. *)

Lemma isRootMapStack_completion ρ vs :
  isRootMapStack ρ [Frame None vs] →
  isRootMap ρ vs.
Proof.
  inversion 1. assumption.
Qed.

(* -------------------------------------------------------------------------- *)

(* The following lemmas aim to establish an upper bound on the size of
   a stack. *)

(* We must use finite sets, which have a notion of [size]. *)

Section Size.

Context `{EqDecision V}.

(* We define [vs ≃ fvs] to mean that the set [vs] has the same
   inhabitants as the finite set [fvs]. This implies that [vs]
   is finite and that its cardinal is [size fvs]. *)

Definition fequiv (vs : set V) (fvs : fset V) :=
  ∀ v, v ∈ vs ↔ v ∈ fvs.

Infix "≃" := fequiv (at level 70).

(* The trace of a well-formed stack is a finite set, and the length of
   the stack is at most the cardinal of its trace, plus 1, as the
   bottom frame does not contain a vertex. *)

Lemma length_stack imarked γ :
  wf imarked γ →
  ∀ omarked σ,
  γ = (omarked, σ) →
  ∃ fvs,
  trace σ ≃ fvs ∧
  (List.length σ ≤ size fvs + 1)%nat.
Proof.
  induction 1; intros ?? Heq;
  injection Heq; clear Heq; intros <- <-;
  [| specialize (IHwf _ _ eq_refl) ];
  simpl.
  { exists ∅. rewrite size_empty. split.
    + intro v. set_solver.
    + lia. }
  { destruct IHwf as (fvs & ? & ?).
    assert (w ∉ trace σ).
    { eapply wf_trace_marked in H; eauto. set_solver. }
    exists (fvs ∪ {[w]}). split.
    + unfold fequiv in *. set_solver.
    + rewrite size_union, size_singleton.
      - lia.
      - unfold fequiv in *. set_solver. }
Qed.

End Size.

(* -------------------------------------------------------------------------- *)

End Interactive.

(* -------------------------------------------------------------------------- *)

(* Hints and tactics. *)

Hint Constructors wf : wf.

Hint Resolve
  wf_init
  wf_step
: wf.

Hint Constructors similar : similar.

Hint Resolve
  similar_reflexive
  similar_transitive
: similar.

Ltac destructStep :=
  match goal with h: step _ _ _ _ _ |- _ => destruction h end.

Ltac wf_nonempty :=
  repeat match goal with
  | h : wf _ _ _ _ |- _ => generalize (wf_nonempty h); revert h
  end; intros.

Ltac destructWf :=
  match goal with h: wf _ _ _ _ |- _ => destruction h end;
  try solve [ exfalso; wf_nonempty; length in *; lia ].
