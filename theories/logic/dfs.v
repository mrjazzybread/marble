(* This library defines a logical view of depth-first search. It defines
   what it means for a forest to be a DFS forest, via an inductive
   predicate [dfs], and explores the properties of this predicate. *)

From Stdlib Require Import Program.Equality. (* [dependent destruction] *)
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

(* The predicate is defined in such a way that there can be more
   vertices in [rs] than in [f]. The roots of the forest [f] must
   appear in the list [rs], though, and they must appear in the
   correct order. *)

Inductive ordered : list V → forest → Prop :=
| OrderedNil:
    ordered nil Empty
| OrderedSkip:
    (* If the tentative first root [r] does not appear anywhere
       in [f], then it is considered irrelevant. *)
    ∀ r rs f,
    r ∉ (support f) →
    ordered rs f →
    ordered ({[r]} ++ rs) f
| OrderedRoot:
    (* Otherwise, the tentative first root [r] must indeed be
       the root of the first tree in the forest. *)
    ∀ r rs ws f,
    ordered rs f →
    ordered ({[r]} ++ rs) (NonEmpty r ws f).

(* This (unused) lemma states that if [rs] orders a non-empty forest,
   then it orders its tail, too (provided the root [w] does not occur
   twice in the forest). *)

Lemma ordered_tail rs w ws vs :
  ordered rs (NonEmpty w ws vs) →
  w ∉ support vs →
  ordered rs vs.
Proof.
  intros h; dependent induction h; intros.
  (* OrderedSkip. *)
  { eapply OrderedSkip; [ | eauto ].
    simpl in *. set_solver. }
  (* OrderedRoot. *)
  { eapply OrderedSkip; eauto. }
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
  { repeat eapply prove_subset_union_left.
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
  (* This repeats sub-goal 2 above, but never mind. *)
  eauto using reaches_roots_support, reaches_transitive,
              subset_transitive with reaches.
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

Lemma bound_closure_reverse imarked w ws vs :
  dfs imarked ⊤ (NonEmpty w ws vs) →
  closed_ imarked →
  closure (flip E) {[w]} ⊆ support (NonEmpty w ws vs).
Proof.
  (* This lemma does require that [omarked] be [⊤], as this means that
     [vs] represents *all* of the trees towards the right; there are no
     more. *)
  intros.
  eapply prove_closure_subset; [ simpl; set_solver |].
  erewrite dfs_determines_support; [| eauto ].
  rewrite closed_path. set_solver.
Qed.

(* By combining the previous two lemmas, we find that the strongly
   connected component of [w] must be a subset of the tree [w/ws]. *)

Lemma bound_scc imarked w ws vs :
  dfs imarked ⊤ (NonEmpty w ws vs) →
  closed_ imarked →
  component_ w ⊆ {[w]} ∪ support ws.
Proof.
  intros hdfs hclosed.
  (* By definition, [component_ w] is the intersection of the vertices
     that [w] can reach and the vertices that can reach [w]. *)
  eapply subset_transitive; [ eapply prove_subset_intersection_right | ].
  + eapply prove_component_subset_closure.
  + eapply prove_component_subset_closure_flip.
  (* The previous two lemmas provide upper bounds for the members
     of this intersection. *)
  + generalize (bound_closure_direct hdfs hclosed); intro.
    generalize (bound_closure_reverse hdfs hclosed); intro.
    dfs_imarked. dfs_monotonic.
    set_solver.
Qed.

(* Now, let us further assume that [w] is the root of the last tree in a
   DFS forest. Then, the strongly connected component of [w] is exactly
   the closure of [w] in the reverse graph. *)

Lemma last_scc {imarked vs w ws} :
  dfs imarked ⊤ (concat vs (NonEmpty w ws Empty)) →
  closed_ imarked →
  component_ w ≡ closure (flip E) {[w]}.
Proof.
  intros hdfs hclosed.
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
  closed_ (⊤ ∖ imarked) →
  closure_ {[w]} ≡ {[w]} ∪ support ws.
Proof.
  intros hdfs hci hcci. intros. eapply subset_antisymmetric.
  (* This inclusion follows from [bound_closure_direct], with the
     additional proviso that there is no overlap with [imarked]. We know
     that [w] is not in [imarked], and the hypothesis that [⊤ ∖ imarked]
     is closed ensures that the closure of [w] lies outside [imarked]. *)
  { rewrite <- closed_path in hcci. (* no escape *)
    generalize (bound_closure_direct hdfs hci); intro.
    assert (w ∉ imarked) by eauto using root_is_unmarked.
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

(* The labeled transition system [step] describes the evolution of the
   state, and the corresponding observable events, as the depth-first
   search traversal progresses. *)

(* A state is a pair of a set of vertices [marked] and a stack [σ]. *)

(* [step marked σ event marked' σ'] means that the system can evolve from
   [marked] and [σ] to [marked'] and [σ'] while emitting the observable
   event [event]. *)

Inductive step : set V → stack → event → set V → stack → Prop :=

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
      marked σ
      (Enter w)
      marked' σ'

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
      marked σ
      (Exit w)
      marked' σ'.

(* Not every stack is well-formed. A stack is well-formed only if it
   corresponds to the beginning of a well-formed DFS forest. *)

(* [wf imarked omarked σ] means that the stack [σ] is well-formed:
   starting with the set of marked vertices [imarked], it is possible to
   reach a state where the set of marked vertices is [omarked] and the
   stack is [σ]. *)

Inductive wf : set V → set V → stack → Prop :=

| WfBottom:
    ∀ imarked omarked vs ,
    (* If [vs] is a well-formed DFS forest *)
    dfs imarked omarked vs →
    (* and if every root of [vs] is a start vertex *)
    roots vs ⊆ start →
    (* then a stack that consists of just one frame, containing the entry
       vertex [None] and the forest [vs], is well-formed. *)
    wf imarked omarked (Frame None vs :: [])

| WfDeep:
    ∀ imarked mmarked σ omarked w ws ,
    (* If the stack [σ] is well-formed, *)
    wf imarked mmarked σ →
    (* If [w] is an unmarked child of the top stack vertex, *)
    edge (top σ) w →
    w ∉ mmarked →
    (* If, after marking [w], a forest [ws] of children of [w] has
       been traversed, *)
    dfs ({[w]} ∪ mmarked) omarked ws →
    outof E {[w]} (roots ws) →
    (* Then the stack [σ], extended with one frame that contains [w]
       and [ws], is well-formed. *)
    wf imarked omarked (Frame (Some w) ws :: σ).

Hint Constructors wf : wf.

(* Hints for the proofs that follow. *)

Local Hint Resolve dfs_concat : dfs.

Local Hint Extern 1 (roots (concat _ _) ⊆ _) =>
  rewrite roots_concat
: set_solver.

(* A well-formed stack is nonempty. *)

Lemma wf_nonempty imarked omarked σ :
  wf imarked omarked σ →
  0 < length σ.
Proof.
  induction 1; length; lia.
Qed.

(* A stack that contains just one empty frame is well-formed. *)

Lemma wf_init :
  ∀ imarked,
  wf imarked imarked (Frame None Empty :: []).
Proof.
  intros. eapply WfBottom; eauto with dfs set_solver.
Qed.

(* The transition system preserves well-formedness. *)

Lemma wf_step :
  ∀ marked σ event marked' σ',
  step marked σ event marked' σ' →
  ∀ imarked,
  wf imarked marked σ →
  wf imarked marked' σ'.
Proof.
  induction 1; intros imarked Hwf; dependent destruction Hwf; subst σ'.
  (* Case: [StepEnter/WfBottom]. *)
  { eauto with wf dfs set_solver. }
  (* Case: [StepEnter/WfDeep]. *)
  { eauto with wf dfs set_solver. }
  (* Case: [StepExit/WfBottom]. *)
  { exfalso. congruence. }
  (* Case: [StepExit/WfDeep]. *)
  { match goal with h: _ :: _ = _ :: _ |- _ => injection h; clear h end.
    intros -> -> ->.
    dependent destruction Hwf.
    (* Subcase: [WfBottom]. [ov] is [None]. *)
    { eapply WfBottom; eauto with dfs set_solver. }
    (* Subcase: [WfBottom]. [ov] is [None]. *)
    { eapply WfDeep; eauto with dfs set_solver. }}
Qed.

(* At any time, if the stack has height 1 (its minimum height) then
   the unique stack frame contains a DFS forest [vs] whose roots
   form a subset of [start]. *)

Lemma wf_completion imarked omarked σ :
  wf imarked omarked σ →
  length σ = 1 →
  ∃ vs,
  σ = Frame None vs :: [] ∧
  dfs imarked omarked vs ∧
  roots vs ⊆ start.
Proof.
  intros Hwf ?. dependent destruction Hwf.
  { eauto. }
  { generalize (wf_nonempty Hwf); intro. length in *. lia. }
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
  wf imarked omarked σ →
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

Lemma similar_push imarked omarked w ws σ :
  wf imarked omarked σ →
  similar σ (store w ws σ).
Proof.
  inversion 1; subst; simpl; econstructor; eauto.
Qed.

End Interactive.

Hint Constructors similar : similar.

Hint Resolve
  similar_reflexive
  similar_transitive
  similar_push
: similar.
