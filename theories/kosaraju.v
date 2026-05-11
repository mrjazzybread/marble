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
From marble Require Import tactics bool int iteration loop array wp.
From marble.logic Require Import sets relations dfs.
From marble Require Import traverse.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

(* -------------------------------------------------------------------------- *)

(* We assume that the vertices of the graph are numbered from 0 to [n-1].
   This assumption allows us to mark vertices by maintaining an array of
   Boolean marks. This is simple and efficient. *)

Local Notation _vertex := int.
Local Notation marks  := (array bool).

Implicit Type _v _w : _vertex.
Implicit Type _vs _ws : list _vertex.
Implicit Type m : marks.

Local Notation vertex := Z.
Implicit Type v w : vertex.
Local Notation vertices := (propset vertex).

(* -------------------------------------------------------------------------- *)

(* Let us first introduce the parameters that describe the graph. *)

(* [foreach_start] and [foreach_successor] are runtime parameters. *)

(* The remaining parameters are logical. *)

Section G.

(* The vertices must be numbered from 0 to [n], excluded. *)

Variable _n : int.
Variable n : Z.
Variable isInt_n : isInt _n n.
Variable bound_n : 0 ≤ n ≤ max_array_length.

(* [foreach_start] iterates on the start vertices. *)

Variable foreach_start : ∀ {A}, A → (A → _vertex → A) → A.

(* [start] is the set of vertices where the traversal should begin. *)

Variable start : vertices.

(* The start vertices must lie in the interval [0, n). *)

Hypothesis start_respects_bound :
  ∀ v, v ∈ start → 0 ≤ v < n.

(* [foreach_start] must enumerate the vertices in the set [start],
   in an arbitrary order, possibly with repetitions. *)

Variable wp_foreach_start:
  ∀ {A} (body : A → _vertex → A),
  ITER_SET ∅ start
    (λ w a Q, ∀ _w, isInt _w w → wp (body a _w) Q)
    (λ a Q, wp (foreach_start a body) Q).

(* [foreach_predecessor a _w] iterates on the predecessors of the
   vertex [_w]. *)

Variable foreach_predecessor : ∀ {A}, A → _vertex → (A → _vertex → A) → A.

(* [foreach_successor a _v] iterates on the successors of the vertex [_v]. *)

Variable foreach_successor : ∀ {A}, A → _vertex → (A → _vertex → A) → A.

(* The vertices form a directed graph. *)

Variable E : relation vertex.

Local Notation predecessors v := (image (flip E) {[v]}).
Local Notation successors v   := (image E {[v]}).
Local Notation closed vs      := (closed E vs).
Local Notation closure vs     := (closure E vs).

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
  ∀ {A} (body : A → _vertex → A),
  ∀Int _v v,
  0 ≤ v < n →
  ITER_SET ∅ (successors v)
    (λ w a Q, ∀ _w, isInt _w w → wp (body a _w) Q)
    (λ a Q, wp (foreach_successor a _v body) Q).

(* The function [foreach_predecessor], applied to [_w], must enumerate the
   predecessors of the vertex [w]. They can be enumerated in an arbitrary
   order, and it is permitted for a vertex [v] to be presented several
   times. *)

Variable wp_foreach_predecessor:
  ∀ {A} (body : A → _vertex → A),
  ∀Int _w w,
  0 ≤ w < n →
  ITER_SET ∅ (predecessors w)
    (λ v a Q, ∀ _v, isInt _v v → wp (body a _v) Q)
    (λ a Q, wp (foreach_predecessor a _w body) Q).

(* -------------------------------------------------------------------------- *)

(* Kosaraju and Sharir's algorithm, which computes the strongly connected
   components of the graph, is expressed in three lines, as follows:

   1. Traverse the graph [E] and construct a list [vs] of its vertices
      in reverse postorder.
   2. Using the list [vs] as the list of the start vertices,
   3. traverse the reverse graph [flip E] and construct a map [ρ] of each
      vertex to the root of its tree in the DFS forest.

   Then [ρ] actually maps each vertex to a distinguished member of its
   strongly connected component. *)

Definition scc : array _vertex :=
  do vs ← list_rev_post _n (@foreach_start) (@foreach_successor) ;
  let foreach_start {S} (s : S) yield := fold_left yield vs s in
  do ρ ← group _n (@foreach_start) (@foreach_predecessor) ;
  ρ.

End G.

(* -------------------------------------------------------------------------- *)
