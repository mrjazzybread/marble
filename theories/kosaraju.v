(******************************************************************************)
(*                                                                            *)
(*                                  Marble                                    *)
(*                                                                            *)
(*                       François Pottier, Inria Paris                        *)
(*                                                                            *)
(*       Copyright 2026--2026 Inria. All rights reserved. This file is        *)
(*       distributed under the terms of the GNU Library General Public        *)
(*       License, with an exception, as described in the file LICENSE.        *)
(*                                                                            *)
(******************************************************************************)

From stdpp Require Import numbers list well_founded.
From stdpp Require Import sets propset.
From listz Require Import listz.
Notation len := length.
From Stdlib Require Import Uint63.
From Stdlib Require Import Array.PArray.
From Stdlib Require Export ZifyNat ZifyUint63.
From marble Require Import tactics bool int list iteration loop array wp.
From marble.logic Require Import sets relations dfs scc.
From marble Require Import traverse.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

Local Ltac wp_intro_hook Hx ::= idtac.

(* This file implements Kosaraju and Sharir's algorithm, which computes
   the strongly connected components of a directed graph in linear time. *)

(* -------------------------------------------------------------------------- *)

(* We assume that the vertices of the graph are numbered from 0 to [n-1].
   This assumption allows us to mark vertices by maintaining an array of
   Boolean marks. This is simple and efficient. *)

Local Notation _vertex := int.

Implicit Type _v _w : _vertex.
Implicit Type _vs _ws : list _vertex.

Local Notation vertex := Z.
Implicit Type v w : vertex.
Local Notation vertices := (propset vertex).

Implicit Type rs : list vertex.
Implicit Type vs : vertices.

(* -------------------------------------------------------------------------- *)

(* Let us first introduce the parameters that describe the graph. *)

(* [_n], [foreach_vertex], [foreach_predecessor], and
   [foreach_successor] are runtime parameters. *)

(* The remaining parameters are logical. *)

Section G.

(* The vertices must be numbered from 0 to [n], excluded. *)

Variable _n : int.
Variable n : Z.
Variable isInt_n : isInt _n n.
Variable bound_n : 0 ≤ n ≤ max_array_length.

(* [foreach_vertex] iterates on all vertices. *)

Variable foreach_vertex : ∀ {S}, S → (S → _vertex → S) → S.

(* [foreach_vertex] must enumerate all vertices,
   in an arbitrary order, possibly with repetitions. *)

Variable wp_foreach_vertex:
  ∀ {S} (body : S → _vertex → S),
  ITER_SET [] {[ v | 0 ≤ v < n ]}
    (λ _ w a Q, ∀ _w, isInt _w w → wp (body a _w) Q)
    (λ     a Q, wp (foreach_vertex a body) Q).

(* [foreach_predecessor a _w] iterates on the predecessors of the
   vertex [_w]. *)

Variable foreach_predecessor : ∀ {S}, S → _vertex → (S → _vertex → S) → S.

(* [foreach_successor a _v] iterates on the successors of the vertex [_v]. *)

Variable foreach_successor : ∀ {S}, S → _vertex → (S → _vertex → S) → S.

(* The vertices form a directed graph. *)

Variable E : relation vertex.

Local Notation predecessors v := (image (flip E) {[v]}).
Local Notation successors v   := (image E {[v]}).
Local Notation closure vs     := (closure E vs).
Local Notation scc v w        := (scc E v w).

(* No edge can leave the interval [0, n). *)

Hypothesis edges_respect_bound :
  ∀ v w, 0 ≤ v < n → E v w → 0 ≤ w < n.

Hypothesis reverse_edges_respect_bound :
  ∀ v w, 0 ≤ w < n → E v w → 0 ≤ v < n.

(* The function [foreach_successor], applied to [_v], must enumerate the
   successors of the vertex [v]. They can be enumerated in an arbitrary
   order, and it is permitted for a vertex [w] to be presented several
   times. *)

Variable wp_foreach_successor:
  ∀ {S} (body : S → _vertex → S),
  ∀Int _v v, 0 ≤ v < n →
  ITER_SET [] (successors v)
    (λ _ w a Q, ∀ _w, isInt _w w → wp (body a _w) Q)
    (λ     a Q, wp (foreach_successor a _v body) Q).

(* The function [foreach_predecessor], applied to [_w], must enumerate the
   predecessors of the vertex [w]. They can be enumerated in an arbitrary
   order, and it is permitted for a vertex [v] to be presented several
   times. *)

Variable wp_foreach_predecessor:
  ∀ {S} (body : S → _vertex → S),
  ∀Int _w w, 0 ≤ w < n →
  ITER_SET [] (predecessors w)
    (λ _ v a Q, ∀ _v, isInt _v v → wp (body a _v) Q)
    (λ     a Q, wp (foreach_predecessor a _w body) Q).

(* -------------------------------------------------------------------------- *)

(* Kosaraju and Sharir's algorithm, which computes the strongly connected
   components of the graph, is expressed in three lines, as follows:

   1. Traverse the graph [E] and construct a list [vs] of its vertices
      in reverse postorder.
   2. Using the list [vs] as the list of the start vertices,
   3. traverse the reverse graph [flip E] and construct a map [_group]
      of each vertex to the root of its tree in the DFS forest.

   Then [_group] maps each vertex to a distinguished member of
   its strongly connected component. *)

Definition kosaraju : array _vertex :=
  do _vs ← list_rev_post _n (@foreach_vertex) (@foreach_successor) ;
  let foreach_start {S} (s : S) yield := fold_left yield _vs s in
  do _group ← group _n (@foreach_start) (@foreach_predecessor) ;
  _group.

(* -------------------------------------------------------------------------- *)

(* Some simple yet important lemmas about the conjunction of the predicates
   [is_scc_forest] (defined in scc.v) and [isRootMap] (defined in dfs.v). *)

(* If [f] is an SCC forest then a root map for [f] is also an SCC map:
   that is, every vertex [v] is mapped to a distinguished element of
   its component. This is stated by two lemmas: 1- [v] and [ρ v]
   inhabit the same component; 2- within one component, all vertices
   are mapped by [ρ] to the same vertex. *)

Lemma scc_forest_root_map_1 ρ f :
  is_scc_forest E f →
  isRootMap ρ f →
  ∀ v, v ∈ support f →
  v ∈ component E (ρ v).
    (* synonymous with [scc v (ρ v)]; see next lemma *)
Proof.
  induction f as [| w ws f ]; inversion 1; inversion 1; subst; simpl.
  { intro v. elem. tauto. }
  { intro v. rewrite elem_of_union. intros [ Hv | Hv ].
    (* Case: [v] lies in this tree, whose root is [w]. *)
    { assert (ρ v = w) as -> by eauto.
      match goal with h: component E w ≡ _ |- _ => rewrite h end.
      assumption. }
    (* Case: [v] does not lie in this tree. *)
    { eauto. }}
Qed.

Lemma scc_forest_root_map_1' ρ f :
  is_scc_forest E f →
  isRootMap ρ f →
  ∀ v, v ∈ support f →
  scc v (ρ v).
Proof.
  intros.
  forwards fact: scc_forest_root_map_1; eauto.
  set_unfold in fact. eauto with scc.
Qed.

Lemma scc_forest_root_map_2 ρ f :
  is_scc_forest E f →
  isRootMap ρ f →
  ∀ v1, v1 ∈ support f →
  ∀ v2, v2 ∈ support f →
  scc v1 v2 →
  ρ v1 = ρ v2.
Proof.
  (* This proof is minimalistic, in the sense that it does not assume
     that [f] is a DFS forest. So [f] could contain several copies of
     the same component. All copies must have the same root anyway.
     This proof does not use the fact that ρ must be idempotent; in
     fact, it proves that ρ must be idempotent (see the next lemma). *)
  induction f as [| w ws f ]; simpl; intros Hforest Hroot.
  { intro v1. elem. tauto. }
  { intros v1 Hv1 v2 Hv2 Hscc.
    rewrite elem_of_union in Hv1, Hv2.
    assert (fact1: v1 ∈ component E (ρ v1))
      by eauto using scc_forest_root_map_1.
    assert (fact2: v2 ∈ component E (ρ v2))
      by eauto using scc_forest_root_map_1.
    elem in fact1. elem in fact2.
    assert (v2 ∈ component E (ρ v1)).
    { elem. eauto with scc. }
    assert (v1 ∈ component E (ρ v2)).
    { elem. eauto with scc. }
    inversion Hforest; inversion Hroot; subst.
    match goal with h: component E _ ≡ _ |- _ =>
      rename h into Hcomponent end.
    destruct Hv1 as [ Hv1 | Hv1 ];
    destruct Hv2 as [ Hv2 | Hv2 ].
    { assert (ρ v1 = w) by eauto.
      assert (ρ v2 = w) by eauto.
      congruence. }
    { assert (ρ v1 = w) by eauto.
      assert (ρ v2 = w) by set_solver. (* cool! *)
      congruence. }
    { assert (ρ v2 = w) by eauto.
      assert (ρ v1 = w) by set_solver. (* cool! *)
      congruence. }
    { eauto. }}
Qed.

(* The previous results imply that [ρ] is idempotent. This result is
   unused. Furthermore, [isRootMap ρ f] alone implies that [ρ] is
   idempotent; see the lemma [isRootMap_idempotent]. *)

Lemma scc_forest_root_map_idempotent ρ f :
  is_scc_forest E f →
  isRootMap ρ f →
  ∀ v, v ∈ support f → ρ (ρ v) = ρ v.
Proof.
  intros.
  assert (v ∈ component E (ρ v)) by eauto using scc_forest_root_map_1.
  elem in *.
  eapply scc_forest_root_map_2; eauto using isRootMap_support.
Qed.

(* Thus, two vertices inhabit the same component if and only if they
   have the same image through [ρ]. *)

Lemma scc_forest_root_map ρ f :
  is_scc_forest E f →
  isRootMap ρ f →
  ∀ v1, v1 ∈ support f →
  ∀ v2, v2 ∈ support f →
  scc v1 v2 ↔ ρ v1 = ρ v2.
Proof.
  split.
  { eauto using scc_forest_root_map_2. }
  { assert (fact1: v1 ∈ component E (ρ v1))
      by eauto using scc_forest_root_map_1.
    assert (fact2: v2 ∈ component E (ρ v2))
      by eauto using scc_forest_root_map_1.
    elem in *.
    intro Heq. rewrite Heq in fact1. eauto with scc. }
Qed.

(* -------------------------------------------------------------------------- *)

(* Specification and proof of Kosaraju and Sharir's algorithm. *)

Lemma wp_kosaraju :
  wp kosaraju (λ _group,
    ∃ ρ,
    rich.isArray isInt _group ρ ∧
    len ρ = n ∧
    (* [ρ] is idempotent. *)
    (∀ v, 0 ≤ v < n → ρ !!! (ρ !!! v) = ρ !!! v) ∧
    (* The vertices [v] and [ρ v] are members of the same component. *)
    (∀ v, 0 ≤ v < n → scc v (ρ !!! v)) ∧
    (* If two vertices [v] and [w] are members of the same component
       then they have the same image through [ρ]. *)
    (∀ v w, 0 ≤ v < n → 0 ≤ w < n → scc v w → ρ !!! v = ρ !!! w) ∧
    (* In other words, two vertices inhabit the same component if and
       only if they have the same image through [ρ]. *)
    (∀ v w, 0 ≤ v < n → 0 ≤ w < n → scc v w ↔ ρ !!! v = ρ !!! w)
  ).
Proof.
  unfold kosaraju.

  (* 1a. Definitions. *)
  set (start := universe n).
  set (permitted := permitted_set start).
  set (complete := complete_set start).

  (* 1b. Invoke [list_rev_post]. *)
  specialize wp_list_rev_post with
    (start := start) (permitted := permitted) (complete := complete)
  ; intro wp_list_rev_post.
  wp_op wp_list_rev_post introducing: _vs;
  clear wp_list_rev_post.
  (* Precondition: [permitted] holds of the empty list. *)
  { unfold permitted, permitted_set. set_solver. }
  (* Precondition: [permitted] is prefix-closed. *)
  { unfold permitted, permitted_set. set_solver. }

  (* 1c. Deconstruct the postcondition of [list_rev_post]. *)
  wp_destruct_post (marked & f1 & Hdfs1 & Hroots & Hmarked & Hvs).
  (* Every vertex is marked. *)
  rewrite (closure_start_is_universe n start) in Hmarked by eauto with lia.
  rewrite Hmarked in Hdfs1.
  (* The list [_vs] corresponds to [vs], a reverse postorder enumeration
     of the forest [f1]. *)
  set (vs := rev (postorder f1)). fold vs in Hvs.
  clear dependent marked.
  clear Hroots. (* unused *)
  (* The list [vs] covers the set [start]. *)
  assert (Hstart: list_to_set vs ≡ start).
  { subst vs. rewrite list_to_set_rev, list_to_set_postorder.
    dfs_omarked. apply dfs_omarked_choice in Hdfs1. set_solver. }
  (* The universe is reverse closed. *)
  assert (closed (flip E) (universe n)) by set_solver.

  (* 2a. More definitions. *)
  (* This time, the predicate [complete] is deterministic: it is important
     that the root vertices be enumerated in the order of the list [vs]. *)
  clear dependent permitted.
  clear complete.
  set (permitted := permitted_sequence vs).
  set (complete := complete_sequence vs).

  (* 2b. Invoke [group]. *)
  specialize (wp_group _n n isInt_n bound_n) with
    (start := start) (permitted := permitted) (complete := complete)
    (E := flip E)  (wp_foreach_successor := @wp_foreach_predecessor)
  ; intro wp_group.
  wp_op wp_group introducing: _group; clear wp_group.
  (* Precondition: [permitted] respects the set [start]. *)
  { unfold permitted, permitted_sequence.
    intros. rewrite <- Hstart. eapply prefix_list_to_set. eauto. }
  (* Precondition: [complete] respects the set [start]. *)
  { unfold complete, complete_sequence. set_solver. }
  (* Precondition: [permitted] holds of the empty list. *)
  { unfold permitted, permitted_sequence. tc. }
  (* Precondition: [permitted] is prefix-closed. *)
  { unfold permitted, permitted_sequence. tc. }
  (* Precondition: [fold_left _ _vs _] enumerates the list [vs]. *)
  { unfold permitted, complete. intros. eapply wp_fold_left'.
    eapply Forall2_impl; eauto. tauto. }

  (* 2c. Deconstruct the postcondition of [group]. *)
  wp_destruct_post
    (rs & marked & f2 & ρ & Hdfs2 & Hordered & Hcomplete
        & Hroots & Hmarked & ? & ? & Hmap).
  (* Every vertex is marked. *)
  rewrite (closure_start_is_universe n start) in Hmarked by eauto with lia.
  rewrite Hmarked in Hdfs2.
  clear dependent marked.
  clear Hroots. (* unused *)
  (* The forest [f2] is ordered by the list [vs]. *)
  unfold complete, complete_sequence in Hcomplete. subst rs.
  (* Therefore [f2] is an SCC forest! *)
  assert (is_scc_forest E f2).
  { eapply scc_soundness. econstructor. eauto. }
  (* The support of [f2] covers every vertex. *)
  assert (∀ v, 0 ≤ v < n → v ∈ support f2).
  { apply dfs_omarked_choice in Hdfs2.
    unfold universe in Hdfs2.
    intros v Hv. specialize (Hdfs2 v). set_unfold in Hdfs2. tauto. }

  (* 3. Conclude. *)
  wp_ret. eexists; pack; tc.
  (* Postcondition 1: [ρ] is idempotent. *)
  { eapply isRootMap_idempotent with (ρ := λ v, ρ !!! v); eauto. }
  (* Postcondition 2: [v] and [ρ !!! v] inhabit the same component. *)
  { eapply scc_forest_root_map_1' with (ρ := λ v, ρ !!! v); eauto. }
  (* Postcondition 3: if [v] and [w] inhabit the same component then
     [ρ !!! v] and [ρ !!! w] are equal. *)
  { eapply scc_forest_root_map_2 with (ρ := λ v, ρ !!! v); eauto. }
  (* Postcondition 4: two vertices inhabit the same component if and
     only if they have the same image through [ρ]. *)
  { eapply scc_forest_root_map with (ρ := λ v, ρ !!! v); eauto. }

Qed.

End G.

(* -------------------------------------------------------------------------- *)
