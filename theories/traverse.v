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
From marble Require Import listz_buffer. (* TODO *)
From marble.logic Require Import sets relations dfs.
Implicit Type _i _j _k _n : int.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

(* This file defines depth-first search algorithms. *)

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

(* [_n], [foreach_start], [foreach_successor] are runtime parameters. *)

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

(* [foreach_start] must enumerate the vertices in the set [start].

   How should the specification of [foreach_start] be expressed? This is
   a subtle question. If [foreach_start] enumerates the vertices in an
   arbitrary order, then this is fine: we can tolerate that. Yet, if
   [foreach_start] enumerates the vertices in a predictable order, then
   we can guarantee that the roots of the DFS forest that we construct
   respect this order. And, in some applications, such as Kosaraju and
   Sharir's algorithm, this matters. So, we write the specification of
   [foreach_start] in a very general form, such that both [ITER_LIST]
   and [ITER_SET'] are instances of this general form.

   This general form requires the user to provide a predicate [complete]
   such that 1- a complete list covers the set [start]; and 2- there
   exists a complete list. For example, the predicate [complete] might
   be true of every list that covers the set [start]; or of every list
   that covers the set [start] and does not have repeated elements; or
   of only of one specific list that covers the set [start].

   For some definitions of [complete], repetition is possible:
   [foreach_start] may produce a vertex several times. *)

Variable complete : list vertex → Prop.

Variable complete_spec :
  ∀ rs, complete rs → list_to_set rs ≡ start.

Variable complete_nonempty :
  ∃ rs, complete rs.

(* We define [permitted rs] to hold if and only if [rs] is a prefix of
   some complete list. (There is no reason to allow the user to provide
   their own definition of [permitted]. This definition seems as general
   as possible.) *)

Definition permitted : list vertex → Prop :=
  λ rs, ∃ rs', complete (rs ++ rs').

(* Any permitted list forms a subset of [start]. *)

Local Lemma permitted_spec rs : permitted rs → list_to_set rs ⊆ start.
Proof.
  intros (rs' & Hcomplete). apply complete_spec in Hcomplete. set_solver.
Qed.

(* The empty list is permitted. *)

Local Lemma permitted_nil : permitted [].
Proof.
  destruct complete_nonempty as (rs & Hcomplete). eauto.
Qed.

(* The predicate [permitted] is prefix-closed. *)

Local Lemma permitted_prefix rs1 rs2 :
  permitted (rs1 ++ rs2) → permitted rs1.
Proof.
  unfold permitted. intros (rs' & Hcomplete). list in *. eauto.
Qed.

Local Lemma permitted_prefix_of rs rs' :
  permitted rs' → rs `prefix_of` rs' → permitted rs.
Proof.
  unfold prefix. intros ? (? & ?). subst. eauto using permitted_prefix.
Qed.

(* [foreach_start] is expected to produce the start vertices in an order
   that respects the predicates [permitted] and [complete]. *)

Variable wp_foreach_start:
  ∀ {A} (body : A → _vertex → A),
  @ITER (list vertex) (eq)
    [] complete A
    ( λ rs0 rs1 a Q,
      ∀Int _v v,
      rs0 ++ {[v]} = rs1 →
      permitted rs1 →
      wp (body a _v) Q
    )
    (λ a Q, wp (foreach_start a body) Q).

(* [foreach_successor a _v] iterates on the successors of the vertex [_v]. *)

(* Fortunately, no properties of this function are needed in the proof of
   termination of [visit]. *)

Variable foreach_successor : ∀ {A}, A → _vertex → (A → _vertex → A) → A.

(* The vertices form a directed graph. *)

Variable E : relation vertex.

Local Notation successors v := (image E {[v]}).
Local Notation closed vs    := (closed E vs).
Local Notation closure vs   := (closure E vs).

(* No edge can leave the interval [0, n). *)

Hypothesis edges_respect_bound :
  ∀ v w, 0 ≤ v < n → E v w → 0 ≤ w < n.

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

(* -------------------------------------------------------------------------- *)

(* Let us write [universe] for the set of all vertices. *)

Definition universe : vertices :=
  {[ v | 0 ≤ v < n ]}.

Lemma start_subset_universe : start ⊆ universe.
Proof using start_respects_bound.
  clear -start_respects_bound.
  set_solver.
Qed.

Lemma closed_universe : closed universe.
Proof using edges_respect_bound.
  clear -edges_respect_bound.
  set_solver.
Qed.

Lemma closure_start_subset_universe : closure start ⊆ universe.
Proof using start_respects_bound edges_respect_bound.
  eapply prove_closure_subset.
  + eapply start_subset_universe.
  + rewrite closed_path. eapply closed_universe.
Qed.

(* If every vertex is a start vertex then every vertex is reachable. *)

Lemma closure_start_is_universe :
  universe ⊆ start →
  closure start ≡ universe.
Proof using start_respects_bound edges_respect_bound.
  intros. eapply subset_antisymmetric.
  + eapply closure_start_subset_universe.
  + transitivity start.
    - assumption.
    - eauto using reaches_reflexive.
Qed.

(* This universe is finite. *)

Lemma finite_universe :
  ∃ rs, list_to_set rs ≡ universe.
Proof.
  exists (listz.init n (λ i, i)).
  rewrite list_to_set_init.
  unfold universe.
  intro v. elem. split.
  + intros (i & ? & ?). lia.
  + intros. eauto with lia.
Qed.

(* -------------------------------------------------------------------------- *)

(* [marked], [imarked], [omarked] denote sets of vertices. *)

Implicit Types marked imarked omarked : vertices.

Implicit Types examined : vertices.

Implicit Types started : list vertex.

Implicit Type σ : stack vertex.

(* We wish to specify what sequences of events the user can expect to
   observe. In short, we are a producer of events. We must expose the
   labeled transition system that we obey: that is, we must define the
   type of producer states as well as the relation that specifies one we
   move from one producer state to the next, while emitting an event. *)

(* A producer state is a tuple [(rs, marked, σ)]. *)

(* We name this type [ghost] to emphasize that it is NOT the type of
   runtime states, [S]. Producer states do not exist at runtime. *)

Local Notation ghost :=
  (dfs.state vertex).

Implicit Type γ : ghost.

(* We write [history γ] for the first component of [γ],
   namely [rs]. *)

Local Notation history γ :=
  (let '(rs, marked, σ) := γ in rs).

(* [γ0] is the initial (ghost) state. *)

Local Notation γ0 :=
  (@γ0 vertex).

(* A transition from state [γ] to state [γ'], emitting an event [e], is
   permitted if the relation [step] allows it. *)

Local Notation step :=
  (dfs.step E).

(* The assertion [wf γ] means that the set of vertices [marked] and the
   stack [σ] are a well-formed state of an ongoing DFS traversal of the
   graph [E]. *)

Local Notation wf := (dfs.wf E).

(* The assertion [perm γ] means that the list [rs] (a component of [γ])
   satisfies [permitted rs]. We need to keep track of this property;
   yet we do not want to build it into the definition of [wf], because
   this pollutes the theory of [wf]. *)

Local Notation perm γ :=
  (permitted (history γ)).

(* The assertion [edge (top σ) v] means that there is an edge of the
   stack's current vertex to [v]. (If the stack has no current vertex,
   it is true.) *)

Local Notation edge := (dfs.edge E).

(* The assertion [dfs marked vs] that [vs] is a DFS forest for the
   graph [E], with initial set of marked vertices ∅, and final set of
   marked vertices [marked]. *)

Local Notation dfs := (dfs.dfs E ∅).

(* [isEvent _e e] relates a runtime event [_e] and an event [e].
   They are the same thing, up to the relation between a machine
   integer [_v] and an ideal integer [v]. *)

Inductive isEvent : event _vertex → event vertex → Prop :=
| IsEventEnter:
    ∀ _v v, isInt _v v → 0 ≤ v < n → isEvent (Enter _v) (Enter v)
| IsEventExit:
    ∀ _v v, isInt _v v → 0 ≤ v < n → isEvent (Exit _v) (Exit v)
| IsEventRediscover:
    ∀ _v v, isInt _v v → 0 ≤ v < n → isEvent (Rediscover _v) (Rediscover v).

Local Ltac destructEvent :=
  match goal with h: isEvent _ _ |- _ => destruction h end.

Local Hint Constructors isEvent : marble.

(* -------------------------------------------------------------------------- *)

(* Local lemmas and hints. *)

Local Lemma trivia marked0 marked1 v :
  marked1 ≡ {[v]} ∪ marked0 →
  marked0 ∪ {[v]} ≡ marked1.
Proof using. clear- marked0. set_solver. Qed.
Local Hint Resolve trivia : marble.

(* -------------------------------------------------------------------------- *)

(* The weight of an array [m] is defined as the number of unmarked
   vertices in this array. It is a natural number. This number is
   used to establish the termination of the algorithm. *)

Local Definition unmarked (b : bool) : nat :=
  if b then 0 else 1.

Local Definition weight m : nat :=
  sum_with unmarked m.

(* Marking an unmarked vertex decreases the weight of the array. *)

Local Lemma marking_decreases_weight m _v :
  (_v <? length m)%uint63 = true →
  get m _v = false →
  (weight (set m _v true) < weight m)%nat.
Proof using.
  unfold weight. intros Hv Hget.
  (* This is a bit ugly. *)
  set (v := (φ _v)%uint63).
  assert (unsigned v). { unfold v. lia. }
  assert (isInt _v v).  { eapply introIsInt. reflexivity. }
  assert (Hvalid: valid v (to_list m))
    by eauto using ltb_length_spec with typeclass_instances.
  rewrite !sum_with_spec.
  erewrite set_spec by eauto.
  generalize (sum_list_with_insert unmarked v (to_list m) true Hvalid).
  erewrite <- get_spec by eauto.
  rewrite Hget.
  simpl unmarked.
  lia. (* ouf *)
Qed.

(* The marks array evolves along the following relation. *)

Local Definition mlt m1 m2 :=
  (weight m1 < weight m2)%nat.

Local Definition mle m1 m2 :=
  (weight m1 ≤ weight m2)%nat.

Declare Scope marks_scope.
Delimit Scope marks_scope with marks.
Infix "≤" := mle (at level 70) : marks_scope.
Infix "<" := mlt (at level 70) : marks_scope.

Section M.
Open Scope marks_scope.

Local Lemma mle_refl m : m ≤ m.
Proof using. unfold mle. lia. Qed.

Local Lemma mle_trans {m1 m2 m3} : m1 ≤ m2 → m2 ≤ m3 → m1 ≤ m3.
Proof using. unfold mle. lia. Qed.

Local Lemma mlt_mle_trans {m1 m2 m3} : m1 < m2 → m2 ≤ m3 → m1 < m3.
Proof using. unfold mle, mlt. lia. Qed.

Local Lemma mle_mlt_trans {m1 m2 m3} : m1 ≤ m2 → m2 < m3 → m1 < m3.
Proof using. unfold mle, mlt. lia. Qed.

Local Lemma mlt_mle_incl {m1 m2} : m1 < m2 → m1 ≤ m2.
Proof using. unfold mle, mlt. lia. Qed.

Local Lemma wf_mlt : well_founded mlt.
Proof using.
  eapply wf_projected with (f := weight); [| eapply Wf_nat.lt_wf ].
  intros m1 m2. unfold mlt. intro. assumption.
Qed.

End M.

(* Rocq 9.1: explicitly instantiating [init] may be necessary to avoid
   divergence when Rocq type-checks the definition of [traverse]. *)

Local Instance inhabited_bool : Inhabited bool.
Proof using. econstructor. exact true. Defined.

(* -------------------------------------------------------------------------- *)

(* [isMarks m marked] means that the Boolean array [m] represents the set
   of vertices [marked]. *)

Open Scope Z_scope.

Local Definition isMarks m marked :=
  ∃ bs,
  isArray m bs ∧
  len bs = n ∧
  ∀ v, 0 ≤ v < n → isBool1 (bs !!! v) (v ∈ marked).

Local Ltac introMarks :=
  eexists; split; [| split]; [ isArray | list; tc | ].

Local Ltac destructMarks :=
  match goal with h: isMarks _ _ |- _ =>
    generalize h; intro; (* keep a copy *)
    let bs := fresh "bs" in
    destruct h as (bs & ? & ? & ?)
  end.

Local Lemma isMarks_intro m :
  isArray m (listz.init n (λ _, false)) →
  (0 ≤ n)%Z →
  isMarks m ∅.
Proof using. clear -n.
  intros. introMarks. intros. list.
  assert (∀ v, 0 ≤ v < n → v ∉ (∅ : vertices)) by set_solver.
  tc.
Qed.

Local Instance isBool_get_mark m marked :
  ∀Int _v v,
  0 ≤ v < n →
  isMarks m marked →
  isBool1 (get m _v) (v ∈ marked).
Proof using.
  intros. destructMarks.
  assert (fact: wp (get m _v) (eq (bs !!! v))).
  { wp_get b. eauto. }
  rewrite wp_iff in fact.
  rewrite <- fact. tc.
Qed.

Local Lemma mark_self marked v : v ∈ {[v]} ∪ marked.
Proof using. clear -marked. set_solver. Qed.

Local Hint Resolve mark_self : marble.

Local Lemma mark_unaffected marked v v' :
  v ≠ v' →
  v' ∈ {[v]} ∪ marked ↔ v' ∈ marked.
Proof using. clear -marked. set_solver. Qed.

Local Lemma isMarks_set m marked :
  isMarks m marked →
  ∀Int _v v,
  0 ≤ v < n →
  v ∉ marked →
  isMarks (set m _v true) ({[v]} ∪ marked).
Proof using. clear -m.
  intros. destructMarks.
  (* Switch to [wp] style *)
  assert (Hm': wp (set m _v true) (λ m, isMarks m ({[v]} ∪ marked))).
  { wp_set. introMarks. intros v' ?. case_lookup_insert.
    + subst v'. tc.
    + rewrite mark_unaffected by assumption. tc. }
  rewrite wp_iff in Hm'. assumption.
Qed.

(* -------------------------------------------------------------------------- *)

(* Hints and tactics used in the proofs of [visit] and [traverse]. *)

Local Lemma app_nil_r_sym {A} (rs : list A) : rs = rs ++ [].
Proof. symmetry. apply app_nil_r. Qed.
Local Hint Resolve app_nil_r app_nil_r_sym : marble.

Local Definition wf_init := (@wf_init _ E).
Local Hint Resolve wf_init wf_step : marble.

Local Hint Resolve
  enter_increases_height
  horizontal_marked_grows
  horizontal_same_edges
  horizontal_same_edges0
  horizontal_same_height
  horizontal_same_height0
: marble.

Local Ltac clarify :=
  case_decide; first [ length in *; lengths; lia | tauto | idtac ].

Local Ltac permitted :=
  match goal with |- context [len ?σ = 1] =>
    destruct (decide (len σ = 1)); list; try solve [ lia | assumption ]
  end.

Local Hint Extern 1 (permitted _) => permitted : marble.

(* Hack: the presence of [complete_nonempty] causes [unpack] to diverge,
   as it is an existential assertion, and is not cleared by [destruct].
   To work around this problem, we redefine [unpack] as follows. *)
Local Ltac unpack ::=
  clear complete_nonempty; repeat unpack1.

(* -------------------------------------------------------------------------- *)

(* The state of the depth-first search algorithm is a pair [(m, u)] where
   [m] is the marks array and [u] is a user state of arbitrary type [U]. *)

(* At this point we open a subsection, where we place parameters that
   depend on the type [U]. *)

Section U.

(* The user state. *)

Context {U : Type}.
Implicit Type u : U.

(* A state [s] is a pair [(m, u)]. *)

Local Notation S := (marks * U)%type.
Implicit Type s : S.

(* -------------------------------------------------------------------------- *)

(* We now make a series of definitions that play a role in the proof
   of termination of the recursive function [visit]. *)

(* The ordering is extended to states. *)

Local Definition slt s1 s2 :=
  let (m1, _) := s1 in let (m2, _) := s2 in (m1 < m2)%marks.

Local Definition sle s1 s2 :=
  let (m1, _) := s1 in let (m2, _) := s2 in (m1 ≤ m2)%marks.

Declare Scope state_scope.
Delimit Scope state_scope with state.
Infix "≤" := sle (at level 70) : state_scope.
Infix "<" := slt (at level 70) : state_scope.

Open Scope state_scope.

Local Lemma sle_refl s : s ≤ s.
Proof using. unfold sle. destruct s. eapply mle_refl. Qed.

Local Lemma sle_trans {s1 s2 s3} : s1 ≤ s2 → s2 ≤ s3 → s1 ≤ s3.
Proof using. unfold sle. destruct s1, s2, s3. eauto using mle_trans. Qed.

Local Lemma slt_sle_trans {s1 s2 s3} : s1 < s2 → s2 ≤ s3 → s1 < s3.
Proof using.
  unfold sle, slt. destruct s1, s2, s3. eauto using mlt_mle_trans.
Qed.

Local Lemma sle_slt_trans {s1 s2 s3} : s1 ≤ s2 → s2 < s3 → s1 < s3.
Proof using.
  unfold sle, slt. destruct s1, s2, s3. eauto using mle_mlt_trans.
Qed.

Local Lemma slt_sle_incl {s1 s2} : s1 < s2 → s1 ≤ s2.
Proof using.
  unfold sle, slt. destruct s1, s2. eauto using mlt_mle_incl.
Qed.

Local Lemma wf_slt : well_founded slt.
Proof using.
  eapply wf_projected with (f := fst); [| eapply wf_mlt ].
  intros (m1 & u1) (m2 & u2). unfold slt. intro. assumption.
Qed.

(* [sbeyond s] is the type of a state [s'] such that [s' ≤ s] holds. *)

Local Definition sbeyond s :=
  { s' | s' ≤ s }.

(* [srefl s] is the state [s] at type [beyond s]. *)

Local Definition srefl s : sbeyond s.
Proof using.
  unfold sbeyond. exists s. eapply sle_refl.
Defined.

(* [strans], an identity function on states, proves that if [s1 ≤ s2] holds,
   and a state [s0] is beyond [s1], then [s0] is also beyond [s2]. *)

Local Definition strans {s1 s2} : s1 ≤ s2 → sbeyond s1 → sbeyond s2.
Proof using.
  intros ow12 (s0 & ow01). exists s0. eauto using sle_trans.
Defined.

(* [strans] is an identity functions, so, while reasoning via [wpd]
   judgements, it has no effect. *)

Local Lemma wpd_strans {s1 s2} (a : sbeyond s1) (pf : s1 ≤ s2) Q :
  wpd a Q →
  wpd (strans pf a) Q.
Proof using.
  unfold strans, wpd. destruct a. simpl. eauto.
Qed.

(* [transform] applies a transformation [f] to the component [u] in
   a composite state of the form [((m', u'), ow)]. *)

Local Definition transform {s} (f : U → U) : sbeyond s → sbeyond s.
Proof using.
  intros ((m' & u') & ow).
  exists (do u' ← f u' ; (m', u')). assumption.
Defined.

(* A reasoning rule for [transform]. *)

Local Lemma wpd_transform {s} f (s' : sbeyond s) Q :
  wpd s' (λ '(m', u'), wp (do u' ← f u' ; (m', u')) Q) →
  wpd (transform f s') Q.
Proof using.
  unfold transform. destruct s' as ((m' & u') & ?). eauto.
Qed.

(* [decrease] constructs a strict ordering witness, expressing the idea
   that if the vertex [_v] is unmarked in the state [s], which is the pair
   [(m, u)], then marking [_v] produces a new state of smaller weight. *)

Local Lemma decrease s m _v u u' :
  s = (m, u) →
  (_v <? length m)%uint63 = true →
  get m _v = false →
  (set m _v true, u') < s.
Proof using.
  intros -> Hv Hget.
  unfold slt, mlt.
  eauto using marking_decreases_weight.
Qed.

Local Opaque transform.

Local Hint Resolve sle_slt_trans : marble.

(* -------------------------------------------------------------------------- *)

(* The user function [hook _e u] is invoked when an event is observed,
   that is, when a vertex is entered or exited. It receives an event [_e]
   and a user state [u] and returns an updated user state. *)

(* If the user needs to observe only one kind of event, they can provide
   a hook that ignores the other kind. *)

Variable hook : event _vertex → U → U.

(* The user's loop invariant appears a precondition and a postcondition of
   the function [hook]. As usual (iteration.v), it relates a producer
   state [γ] and a user state [u]. *)

Variable inv : ghost → U → Prop.

(* We use the loop invariant [inv] in calls to [foreach_start] and
   [foreach_successor], whose specification requires [inv] to be
   compatible with extensional equality of sets. (This requirement is
   hidden in the definition of [ITER_SET].) Therefore we must impose
   this requirement. *)

Variable compatible_inv :
  Proper ((@equiv _ equiv_state) ==> eq ==> iff) inv.

(* The invariant must hold initially. *)

Variable u0 : U.
Variable initialization : inv γ0 u0.

(* The specification of the user function [hook] states that [hook] can
   expect the invariant [inv γ u] to hold; can expect to observe an event
   [e] such that [step γ e γ'] holds; and must update the user state to a
   new state [u'] such that [inv γ' u'] holds. Furthermore, the user can
   expect [wf γ], which implies [wf γ'], and [perm γ'], which implies
   [perm γ]. *)

Variable wp_hook :
  ∀ γ γ' u,
  inv γ u →
  wf γ →
  ∀ _e e,
  isEvent _e e →
  step γ e γ' →
  perm γ' →
  wp (hook _e u) (λ u', inv γ' u').

(* From the user's point of view, the loop invariant [inv γ u] is a
   concrete logical proposition that is preserved at each step. From the
   producer's point of view (that is, our point of view, here), [inv γ u]
   is an abstract assertion. It keeps track of the connection between the
   ghost state [γ] and the user state [u], which exists at runtime.
   Because we receive [inv γ u] and must establish [inv γ' u'], [inv] can
   be understood both as a permission and as an obligation to invoke the
   user function [hook] so as to emit a certain sequence of observable
   events. *)

(* -------------------------------------------------------------------------- *)

(* The main recursive function: [visit].  *)

(* [visit] expects a state [s], a vertex [_v], and a proof that [s] is
   accessible. It is defined by structural recursion on [ACC]. *)

(* [visit s _v ACC] produces a result of type [sbeyond s], that is, a new
   state [s'] such that [s' ≤ s] holds. This information is required,
   while iterating on the successors of a state, to prove that every call
   to [visit] in this sequence is permitted. *)

(* To iterate on the successors, we use a simply-typed iteration function.
   This requires us to package [visit] as a function whose argument state
   and result state have the same type, and which does not require [ACC].
   Fortunately, this is possible! *)

Local Fixpoint visit s _v (ACC : Acc slt s) : sbeyond s :=
  (* Destruct [s] as a pair [m, u] while keeping track of the equation. *)
  match s as b return s = b → _ with (m, u) => λ Hsmu,
  (* Test whether this vertex is valid. *)
  IFC (_v <? length m)%uint63 THEN λ Hv,
  (* Test whether this vertex is marked. *)
  IFC get m _v THEN λ _,
    (* It is marked: invoke [hook] to signal a rediscovery. *)
    transform (hook (Rediscover _v)) (srefl s)
  ELSE λ Hunmarked,
    (* Mark this vertex. *)
    let m' := set m _v true in
    (* Invoke [hook] to signal that we are entering [_v]. *)
    do u' ← hook (Enter _v) u ;
    (* Construct an updated state. *)
    let s' := (m', u') in
    (* Construct a witness of the assertion [s' < s]. *)
    let ow : s' < s := decrease s m _v u u' Hsmu Hv Hunmarked in
    (* Visit the successors of [v]. *)
    (* The loop body is a function of type [sbeyond s' → vertex → sbeyond s'],
       which can be passed to [foreach_successor]. Because [ACC] is at
       hand, any call to [visit] on a state that is smaller than [s] is
       permitted. Thus the loop body does not need an accessibility
       witness as an argument. Its free variables are [visit] and [ACC]. *)
    do sow'' ← foreach_successor (srefl s') _v (
      λ (sow'' : sbeyond s') _w ,
        let (s'', ow'') := sow'' in
        strans ow'' (visit s'' _w (Acc_inv ACC (sle_slt_trans ow'' ow)))
    ) ;
    (* Invoke [hook] to signal that we are exiting [_v]. *)
    do sow'' ← transform (hook (Exit _v)) sow'' ;
    strans (slt_sle_incl ow) sow''
  ELSE λ _,
     (* This vertex is out-of-bounds. Ignore it. This lets us prove
        termination without imposing any conditions on the vertices
        that we receive. *)
    srefl s
  end eq_refl.

(* In an earlier version of this code, we did not test whether [v] is
   valid. Instead, we relied on the hypothesis [default m = true], which
   implies that if [v] is out-of-bounds then it is considered marked
   already. This would force us to establish and keep track of the
   invariant [default m = true]. It was a bit cumbersome and inelegant,
   as we usually never access the default element of an array and never
   need to keep track of its value. Furthermore, this approach led us to
   a situation where Rocq's type-checker would not terminate. Therefore
   we have abandoned it. *)

(* -------------------------------------------------------------------------- *)

(* Once the termination of [visit] has been established, one can define a
   simplified version of it, which does not need an accessibility witness,
   and whose result type is just [S]. *)

Local Definition visit' s _v : S :=
  do sow ← visit s _v (wf_slt s) ;
  proj1_sig sow.
  (* TODO would like to use [Acc_intro_generator] here, but this
          causes divergence at Qed in the lemma [wp_visit']. *)

(* -------------------------------------------------------------------------- *)

(* [traverse] is the main function of the depth-first search
   algorithm. It traverses the graph with initial user state [u0]. *)

(* The number of vertices is given by [_n].
   The start vertices are given by [foreach_start].
   The successors of a vertex are given by [foreach_successor].
   The algorithm emits events by invoking [hook]. *)

Definition traverse : S :=
  (* Allocate an array of Boolean marks. *)
  do m0 ←  @init bool inhabited_bool _n (λ _i, false) ;
  (* Visit the start vertices. *)
  foreach_start (m0, u0) visit'.

(* -------------------------------------------------------------------------- *)

(* The postcondition of [visit]. *)

(* [visit_post γ started examined s'] means that, starting from the ghost
   state [γ], the runtime state [s'] is a correct final state and
   corresponds to some ghost state [γ'] that is horizontally related with
   the ghost state [γ]. Furthermore, in the move from [γ] to [γ'], the
   vertices in the list [started] have been added to the component [rs] of
   the ghost state, and (at least) the vertices in the set [examined] have
   been added to the component [marked] of the ghost state. *)

(* The order of the conjuncts in [visit_post] matters. When proving a a
   goal of the form [visit_post ...], the final state [(m', u')] is known;
   from it, via [inv γ' u'], we deduce how to instantiate [γ'], and via
   [isMarks m' marked'], how to instantiate [marked']. The rest is
   checked. *)

Local Definition visit_post γ started examined s' :=
  let '(rs, marked, σ) := γ in
  let '(m', u') := s' in
  ∃ rs' marked' σ' γ',
  inv γ' u' ∧
  wf γ' ∧
  perm γ' ∧
  horizontal γ γ' ∧
  isMarks m' marked' ∧
  γ' = (rs', marked', σ') ∧
  rs' = rs ++ started ∧
  examined ⊆ marked'.

(* The following tactics introduce and eliminate [visit_post]. *)

Local Ltac intro_visit_post :=
  match goal with |- visit_post ?γ _ _ _  =>
  (* If there is an equation [γ = (rs, marked, σ)] in the context,
     rewrite in the goal so as to allow unfolding [visit_post];
     then unfold and rewrite in the other direction so as to keep
     the name [γ]. *)
  try match goal with h: γ = _ |- _ =>
    rewrite h; unfold visit_post; rewrite <- h
  end;
  do 4 eexists; pack; [
    (* inv      *) eassumption
  | (* wf       *) eauto 3 with marble
  | (* perm     *) eauto 3 with marble
  | (* horiz    *) eauto 3 with horizontal marble
  | (* isMarks  *) eassumption
  | (* equality *) eauto 3
  | (* rs *)       list; eauto 3 with marble
  | (* subset   *) set_solver
  ]
  end.

Local Ltac elim_visit_post rs' marked' σ' γ' :=
  (* Again, if we have either [γ = ...] or [γ := ...] in the context,
     we use [rewrite] or [unfold] to expand γ and allow unfolding,
     then we undo this action so as to keep the name γ. *)
  match goal with
  | hv: visit_post ?γ _ _ _, h: ?γ = _ |- _ =>
      rewrite h in hv;
      unfold visit_post in hv;
      destruct hv as (rs' & marked' & σ' & γ' & hv);
      list in hv;
      rewrite <- ?h in hv;
      unpack in hv
  | hv: visit_post ?γ _ _ _ |- _ =>
      unfold γ in hv; (* in case we have [γ := ...] *)
      unfold visit_post in hv;
      destruct hv as (rs' & marked' & σ' & γ' & hv);
      list in hv;
      fold γ in hv;
      unpack in hv
  | hv: visit_post ?γ _ _ _ |- _ =>
      unfold visit_post in hv;
      destruct hv as (rs' & marked' & σ' & γ' & hv);
      list in hv;
      unpack in hv
  end.

(* The specification of [visit]. *)

(* Because the result type of [visit] is a subset type,
   instead of [wp], we use the judgement [wpd]. *)

(* [permitted (rs ++ started)] implies [perm γ]. *)

Local Lemma wpd_visit s (ACC : Acc slt s) :
  ∀ m u _v v rs marked σ γ started,
  s = (m, u) →
  γ = (rs, marked, σ) →
  inv γ u →
  wf γ →
  isMarks m marked →
  isInt _v v →
  0 ≤ v < n →
  edge (top σ) v →
  started = (if decide (len σ = 1) then {[v]} else []) →
  permitted (rs ++ started) →
  wpd (visit s _v ACC) (λ s', visit_post γ started {[v]} s').
Proof.
  clear dependent foreach_start start_respects_bound.
  by dependent induction on s ACC. intros s ? ?.
  intros. subst s. simpl visit.
  destructMarks. arrays.
  assert (1 ≤ len σ)%Z by eauto using wf_nonempty.
  assert (perm γ).
  { subst γ; eauto using permitted_prefix. }
  (* Because we require [v < n], the first branch of this conditional
     construct must be taken. The second branch is dead. *)
  eapply wpd_IFC; [ tc | intros | lia ].
  (* The second conditional construct tests whether [v] is marked. *)
  eapply wpd_IFC; [ tc | intros | intros ].
  (* Case: [v] is marked already. *)
  {
    (* Emit a [Rediscover] event. *)
    set (rs' := rs ++ started).
    set (γ' := (rs', marked, σ)).
    assert (step γ (Rediscover v) γ').
    { subst γ γ' started rs'. econstructor; try clarify; tc. }
    eapply wpd_transform.
    eapply wpd_exist; eapply wp_ret.
    (* Invoke [hook]. *)
    wp_op wp_hook shadowing: u.
    wp_ret.
    intro_visit_post.
  }
  (* Case: [v] is unmarked. *)
  assert (Hm': isMarks (set m _v true) ({[v]} ∪ marked))
    by eauto using isMarks_set.
  revert Hm'.
  set (m' := set m _v true).
  set (rs' := rs ++ started).
  set (marked' := {[v]} ∪ marked).
  set (σ' := Frame (Some v) Empty :: σ).
  set (γ' := (rs', marked', σ')).
  intro.
  (* Emit an [Enter] event. *)
  assert (step γ (Enter v) γ').
  { subst γ γ' started rs' marked'.
    econstructor; try clarify; eauto 2 with marble set_solver. }
  assert (len σ' = len σ + 1) by tc.
  (* Invoke [hook]. *)
  wp_op wp_hook introducing: u'.
  assert ((m', u') < (m, u)).
  { eapply decrease; eauto. }
  (* We have [inv γ' u']. *)
  eapply wpd_wpd_bind_unary.
  (* We reach the loop on the successors of [v]. The goal must be changed
     from [wpd] to [wp], so that [wp_foreach_successor] can be used. *)
  rewrite wpd_wp.
  wp_op wp_foreach_successor with invariant: (
    λ examined (s'' : sbeyond (m', u')),
      visit_post γ' [] examined (proj1_sig s'')
  ).
  (* Compatibility. (This is a bit painful.) *)
  { intros examined1 examined2 ?. intros ((m'' & u'') & ?) ? <-. simpl.
    split; intros; unpack; pack; eauto with set_solver. }
  (* Initialization. *)
  { intro_visit_post. }
  (* Preservation. *)
  { wp_body examined0 examined1 ((m'' & u'') & ow'')
      introducing: (fun _ => intros w ??? _w ?).
    elim_visit_post rs'' marked'' σ'' γ''. subst rs''.
    assert (E v w) by set_solver.
    assert (edge (top σ') w) by eauto.
    assert (len σ'' = len σ') by tc.
    assert (2 ≤ len σ'')%Z by lia.
    (* We have [inv γ'' u'']. *)
    (* The successors of [v] that have been examined already form the
       set [examined0], a subset of [marked'']. The vertex [w], also
       a successor of [v], is about to be examined. *)
    (* Change the goal back into [wpd] format. *)
    eapply wp_wpd; [| eauto ].
    eapply wpd_strans.
    (* Use the induction hypothesis to justify calling [visit s'' _w]. *)
    eapply wpd_conseq.
    { eapply IH; tc. }
    (* Justify that this call establishes the loop invariant. *)
    cbv beta. intros (m''' & u''') ?.
    clarify. (* [len σ'' ≠ 1] *)
    elim_visit_post rs''' marked''' σ''' γ'''. subst rs'''.
    assert (marked'' ⊆ marked''') by tc.
    assert (horizontal γ' γ''') by eauto 2 using horizontal_transitive.
    intro_visit_post.
  }
  clear foreach_successor wp_foreach_successor IH. (* for clarity *)
  (* All successors of [v] have now been examined. *)
  intros ((m'' & u'') & ?). simpl proj1_sig.
  intros (examined & Hpost & Hexamined) ?.
  elim_visit_post rs'' marked'' σ'' γ''. subst rs''.
  (* The structure of the stack has been preserved. *)
  assert (∃ vs, σ'' = Frame (Some v) vs :: σ) as (vs & ?).
  { eauto using horizontal_populates_top_frame. }
  set (marked''' := marked'').
  set (σ''' := store v vs σ).
  set (γ''' := (rs', marked''', σ''')).
  (* We invoke the user function [hook] again. *)
  assert (step γ'' (Exit v) γ''').
  { subst γ'' γ'''. econstructor; eauto with set_solver. }
  eapply wpd_wpd_bind_unary.
  eapply wpd_transform.
  eapply wpd_exist; eapply wp_ret.
  wp_op wp_hook introducing: u'''.
  assert (marked' ⊆ marked'') by tc.
  (* Return. *)
  wp_ret; intro.
  eapply wpd_exist.
  wp_ret.
  intro_visit_post.
Qed.

(* A specification of [visit']. *)

Local Lemma wp_visit' :
  ∀ m u _v v rs marked σ γ started,
  γ = (rs, marked, σ) →
  inv γ u →
  wf γ →
  isMarks m marked →
  isInt _v v →
  0 ≤ v < n →
  edge (top σ) v →
  started = (if decide (len σ = 1) then {[v]} else []) →
  permitted (rs ++ started) →
  wp (visit' (m, u) _v) (λ s', visit_post γ started {[v]} s').
Proof.
  intros. unfold visit'. eapply wpd_visit; tc.
Qed.
  (* This [Qed] diverges if [Acc_intro_generator] is used
     in the definition of [visit']. *)

(* -------------------------------------------------------------------------- *)

(* As an exercise, we prove that [visit'] satisfies the desired fixed
   point equation. Most likely, we will NOT need this property. I am
   showing this proof for pedagogical purposes; it is super difficult
   if one does not approach it in exactly the right way. *)

(* Under [proj1_sig], the coercion [strans] vanishes. *)

Section FixedPoint.

Local Lemma proj1_sig_strans {s1 s2} (pf : s1 ≤ s2) (s0 : sbeyond s1) :
  proj1_sig (strans pf s0) = proj1_sig s0.
Proof using.
  destruct s0. eauto.
Qed.

(* Because [foreach_successor] is an unknown function, we must assume
   that it is parametric: that is, when applied to related arguments,
   it produces related results. *)

Hypothesis foreach_successor_parametric:
  ∀ {A1 A2} (A : A1 → A2 → Prop),
  ∀ (body1 : A1 → _vertex → A1) (body2 : A2 → _vertex → A2),
  ( ∀ a1 a2, A a1 a2 →
    ∀ _w,
    A (body1 a1 _w) (body2 a2 _w)
  ) →
  ∀ a1 a2, A a1 a2 →
  ∀ _v,
  A (foreach_successor a1 _v body1) (foreach_successor a2 _v body2).

(* [visit'] satisfies the desired fixed point equation: *)

Local Lemma visit_eq s ACC : ∀ _v,
  proj1_sig (visit s _v ACC) =
    let (m, u) := s in
    if (_v <? length m)%uint63 then
      do b ← get m _v ;
      if b then
        do u ← hook (Rediscover _v) u ;
        (m, u)
      else
        do m' ← set m _v true ;
        do u' ← hook (Enter _v) u ;
        let s' := (m', u') in
        do s' ← foreach_successor s' _v visit' ;
        let (m', u') := s' in
        do u' ← hook (Exit _v) u' ;
        (m', u')
    else
      s.
Proof using foreach_successor_parametric.
  by dependent induction on s ACC. intros s ? ?.
  intros. simpl visit.
  destruct s as (m & u).
  eapply IFC_if_dep; intro; [| solve [eauto] ].
  eapply IFC_if_dep; intro; [ solve [eauto] |].
  (* Eliminate [do m' ← ...], which appears only on one side. *)
  unfold bind at 4.
  eapply bind_eq_dep; [ eauto | intro u' ].
  eapply bind_eq_dep_dep.
  (* The loop. *)
  { eapply foreach_successor_parametric with (A :=
      λ (s1 : sbeyond (set m _v true, u')) (s2 : S),
          proj1_sig s1 = s2
    ); [| eauto ].
    intros (s'' & ow'') ?. simpl. intros <- _w.
    rewrite proj1_sig_strans.
    unfold visit'.
    unfold bind.
    set (ow := decrease (m, u) m _v u u' eq_refl pf1 pf2).
    (* The goal boils down to proving that the parameter [ACC] is
       computationally irrelevant; that is, it does not influence
       the first projection of the result of [visit]. *)
    unfold bind.
    do 2 rewrite IH by tc.
    reflexivity. }
  (* The code that follows the loop. *)
  intros (m'' & u'') ?. reflexivity.
Qed.

End FixedPoint.

(* -------------------------------------------------------------------------- *)

(* The postcondition of [traverse]. *)

(* When [traverse] terminates, all of the start vertices have been
   visited, in an order determined by the list [rs]; a set of vertices
   [marked] has been marked; and a DFS forest has been virtually
   constructed. (This forest does not exist at runtime.) *)

(* The description below repeats (in part) the definition of [wf].
   This is intended; thus, the postcondition of [traverse] can be
   understood without looking up the definition of [wf]. *)

Definition traverse_postcondition '(m, u) :=
  ∃ rs marked σ vs,
  (* The array [m] tells which vertices have been marked. *)
  isMarks m marked ∧
  (* The user invariant holds. *)
  inv (rs, marked, σ) u ∧
  (* The ghost stack [σ] stores the forest [vs]. *)
  σ = Frame None vs :: [] ∧
  (* [vs] is a DFS forest. *)
  dfs marked vs ∧
  (* [vs] is ordered by [rs]. *)
  ordered rs vs ∧
  (* The sequence [rs] has been produced by [foreach_start]. *)
  (* This implies [list_to_set rs ≡ start]. *)
  complete rs ∧
  (* The roots of the forest [vs] form a subset of the start vertices. *)
  roots vs ⊆ start ∧
  (* Every start vertex is marked. *)
  start ⊆ marked.

(* A specification of [traverse]. *)

Lemma wp_traverse :
  wp traverse (λ s', traverse_postcondition s').
Proof.
  intros. unfold traverse.
  wp_op (wp_init (λ _, false)) introducing: m.
  { intros. wp_ret. }
  assert (isMarks m ∅) by eauto using isMarks_intro with lia.
  (* In this loop on the start vertices, each vertex is both "started"
     (i.e., it is a start vertex) and "examined" (i.e., it is a vertex).
     This is visible in the loop invariant, where the list [started] is
     used to instantiate two parameters of [visit_post], namely
     [started] and [examined]. *)
  wp_op wp_foreach_start with invariant:
    (λ started s, visit_post γ0 started (list_to_set started) s).
  (* Initialization. *)
  { intro_visit_post. }
  (* Preservation. *)
  { clear dependent m.
    intros started0 started1 (m' & u') ?.
    intros _v v ? ? Hpermitted.
    subst started1.
    assert (v ∈ start).
    { apply permitted_spec in Hpermitted. set_solver. }
    elim_visit_post rs' marked' σ' γ'. subst rs'.
    assert (len σ' = 1) by tc.
    wp_op wp_visit' introducing: (m'' & u'').
    elim_visit_post rs'' marked'' σ'' γ''. clarify. subst rs''.
    assert (marked' ⊆ marked'') by tc.
    assert (horizontal γ0 γ'') by eauto 2 using horizontal_transitive.
    intro_visit_post. }
  (* Completion. *)
  { cbv beta. intros (m' & u') (started & ? & Hcomplete).
    elim_visit_post rs' marked' σ' γ'. subst rs' γ'.
    match goal with h: horizontal γ0 _ |- _ => destruction h end.
    simpl concat in *.
    destructWf.
    match goal with f: forest vertex |- _ => rename f into vs end.
    assert (Hfinished: list_to_set started ≡ start)
      by eauto using complete_spec.
    assert (roots vs ⊆ start).
    { rewrite <- Hfinished. eauto using ordered_subset. }
    do 4 eexists. pack; eauto 2 with marble set_solver. }
Qed.

End U.

(* -------------------------------------------------------------------------- *)

(* We now define [traverse_pre], a simplified version of [traverse].
   Instead of emitting several kinds of events, this function emits
   just vertex-entry events. Thus its [hook] function expects just a
   vertex as a parameter, as opposed to an event. *)

(* Because [traverse_pre] does not emit vertex-exit events, it is more
   efficient than [traverse]. It performs more tail calls and requires
   less stack space. *)

Section TraversePre.

Context {U : Type}.
Implicit Type u : U.

(* [hook_pre] passes [Enter] events on to [hook] and ignores other events. *)

Variable hook : _vertex → U → U.

Local Definition hook_pre _e u :=
  match _e with
  | Enter _v => hook _v u
  | _        => u
  end.

(* [plain_traverse_pre] is just [traverse] applied to [hook']. *)

Definition plain_traverse_pre :=
  @traverse U hook_pre.

(* By specializing [traverse] and [visit] for [hook_pre], we obtain code
   where the vertex-exit events disappear. In the extracted OCaml code,
   the call from [visit] to [foreach_successor] becomes a tail call. *)

Derive traverse_pre
  in (traverse_pre = plain_traverse_pre)
  as traverse_pre_eq.
Proof using.
  intros. unfold plain_traverse_pre, traverse, visit', visit, hook_pre.
  unfold traverse_pre; reflexivity.
Defined.

(* We do not state the most general specification of [traverse_pre].
   To reason about [traverse_pre], use [rewrite traverse_pre_eq]
   followed with [unfold plain_traverse_pre, hook_pre]; then reason
   using the lemma [wp_traverse]. *)

(* Thus, the user invariant must be as required by [wp_traverse].
   Bceause [Exit] events are not observable, the invariant must be
   preserved by [Exit] events. *)

(* -------------------------------------------------------------------------- *)

(* A simplified specification of [traverse_pre]. *)

(* This simplified specification does not guarantee that the vertices are
   produced in DFS pre-order. It guarantees that all reachable vertices
   are enumerated, without repetition, in an unspecified order. *)

(* As the producer state, we use a set of vertices. It is the set of
   vertices that have been examined so far. *)

Section SimplifiedSpec.

Variable inv : vertices → U → Prop.

Variable compatible_inv : Proper (equiv ==> eq ==> iff) inv.

Variable u0 : U.
Variable initialization : inv ∅ u0.

Variable wp_hook :
  ∀ examined0 examined1 u,
  inv examined0 u →
  ∀ _v v,
  isInt _v v →
  0 ≤ v < n →
  v ∉ examined0 →
  examined0 ∪ {[v]} ≡ examined1 →
  examined1 ⊆ closure start →
  wp (hook _v u) (λ u', inv examined1 u').

Local Ltac proveInv :=
  match goal with h: inv ?marked ?u |- inv ?marked' ?u =>
    assert (marked' ≡ marked) as -> by set_solver;
    exact h
  end.

Lemma wp_traverse_pre_simplified :
  wp (traverse_pre u0) (λ '(m', u'),
    ∃ marked',
    isMarks m' marked' ∧
    inv marked' u' ∧
    (* The marked vertices are exactly the reachable vertices. *)
    marked' ≡ closure start
  ).
Proof.
  intros.
  rewrite traverse_pre_eq. unfold plain_traverse_pre.
  wp_op wp_traverse with invariant: (λ γ u,
    let '(rs, marked, σ) := γ in inv marked u
  ).
  (* Compatibility. (This is a bit painful.) *)
  { intros ((rs1 & marked1) & σ1) ((rs2 & marked2) & σ2) Hequiv.
    unfold equiv in Hequiv. hnf in Hequiv. unpack in Hequiv.
    intros u'' ? <-.
    split; intros; unpack; pack; eauto; set_solver. }
  (* Preservation. *)
  { intros γ0 γ1 u Hinv Hwf0 _e e Hevent Hstep Hperm.
    assert (Hwf1: wf γ1) by eauto using wf_step.
    destruct γ0 as ((rs0 & marked0) & σ0).
    destruct γ1 as ((rs1 & marked1) & σ1).
    apply permitted_spec in Hperm.
    assert (reaches E start marked1).
    { generalize (wf_reaches Hwf1 eq_refl); intro. set_solver. }
    destructEvent; destructStep; unfold hook_pre; try solve [ wp_ret ].
    (* Only the case of an [Enter] event is nontrivial. *)
    wp_op wp_hook introducing: u'.
    assumption. }
  (* Completion. *)
  { cbv beta. intros (m' & u') (marked' & σ' & vs & ?). unpack.
    pack; eauto using omarked_is_closure_start. }
Qed.

End SimplifiedSpec.
End TraversePre.

(* -------------------------------------------------------------------------- *)

(* We now define [traverse_post], a simplified version of [traverse].
   Instead of emitting several kinds of events, this function emits
   just vertex-exit events. Thus its [hook] function expects just a
   vertex as a parameter, as opposed to an event. *)

Section TraversePost.

Context {U : Type}.
Implicit Type u : U.

(* [hook_post] passes [Exit] events on to [hook]
   and ignores other events. *)

Variable hook : _vertex → U → U.

Local Definition hook_post _e u :=
  match _e with
  | Exit  _v => hook _v u
  | _        => u
  end.

(* [plain_traverse_post] is just [traverse] applied to [hook_post]. *)

Definition plain_traverse_post u :=
  @traverse U hook_post u.

(* By specializing [traverse] and [visit] for [hook_post], we obtain code
   where the vertex-entry events disappear. *)

Derive traverse_post
  in (∀ u, traverse_post u = plain_traverse_post u)
  as traverse_post_eq.
Proof using.
  intros. unfold plain_traverse_post, traverse, visit', visit, hook_post.
  unfold traverse_post; reflexivity.
Defined.

(* We do not state the most general specification of [traverse_post].
   To reason about [traverse_post], use [rewrite traverse_post_eq]
   followed with [unfold plain_traverse_post, hook_post]; then reason
   using the lemma [wp_traverse]. *)

(* Thus, the user invariant must be as required by [wp_traverse].
   Bceause [Enter] events are not observable, the invariant must be
   preserved by [Enter] events. *)

End TraversePost.

(* -------------------------------------------------------------------------- *)

(* [traverse_pre'] is a simplified version of [traverse_pre] where we
   return just the final user state [u], not the marks array [m]. *)

Definition traverse_pre' {U} hook (u : U) : U :=
  do (m, u) ← traverse_pre hook u ;
  u.

(* Although dropping [m] may seem silly, this allows us to give a
   specification of [traverse_pre'] as a higher-order iteration function.
   This specification is an instance of [ITER_SET_UNIQUE]. It states
   that [traverse_pre'] enumerates the reachable vertices of the graph [E],
   without repetition, in an unspecified order. *)

Lemma wp_traverse_pre' :
  ∀ {U} (hook : _vertex → U → U),
  ITER_SET_UNIQUE
    ∅ (closure start)
    (λ v u Q, ∀ _v, isInt _v v → 0 ≤ v < n → wp (hook _v u) Q)
    (λ u Q, wp (traverse_pre' hook u) Q).
Proof.
  intros. ITER. unfold traverse_pre'.
  wp_op wp_traverse_pre_simplified with invariant: inv.
  (* Preservation. *)
  { intros. wp_op Hbody.
    + set_solver.
    + cbv beta. eauto. }
  (* Completion. *)
  { clear dependent s.
    cbv beta. intros (m & u) (marked' & ?). unpack.
    wp_ret. }
Qed.

(* -------------------------------------------------------------------------- *)

(* Lists of vertices. *)

(* TODO move elsewhere *)
Local Notation isListIntU := (Forall2 (λ _v v, isIntU _v v)).

(* -------------------------------------------------------------------------- *)

(* [list_rev_post] traverses the graph and constructs a list of the reachable
   vertices, in reverse postorder. That is, a vertex is pushed onto the list
   when it is exited, and it is pushed in front of the list. *)

Definition plain_list_rev_post : list _vertex :=
  do (m, _vs) ← traverse_post (λ _v _vs, _v :: _vs) [] ;
  _vs.

Derive list_rev_post
  in (list_rev_post = plain_list_rev_post)
  as list_rev_post_eq.
Proof using.
  intros. unfold plain_list_rev_post, traverse_post.
  unfold list_rev_post; reflexivity.
Defined.

(* The specification of [list_rev_post]. *)

Lemma wp_list_rev_post :
  wp list_rev_post (λ _vs, ∃ marked vs,
    dfs marked vs ∧
    roots vs ⊆ start ∧
    marked ≡ closure start ∧
    isListIntU _vs (rev (postorder vs))
  ).
Proof.
  rewrite list_rev_post_eq. unfold plain_list_rev_post.
  rewrite traverse_post_eq. unfold plain_traverse_post.
  generalize unsigned_max_array_length; intro.
  wp_op wp_traverse with invariant: (λ γ _vs,
    let (marked, σ) := γ in
    isListIntU _vs (rev (postorder_stack σ))
  ).
  (* Compatibility. *)
  { intros ((rs0 & marked0) & σ) ((rs1 & marked1) & σ') Hequiv.
    unfold equiv in Hequiv. hnf in Hequiv. unpack. subst σ'.
    intros _vs ? <-. tauto. }
  (* Initialization. *)
  { unfold γ0. simpl. tc. }
  (* Preservation. *)
  { intros ((rs & marked) & σ) ((rs' & marked') & σ') _vs Hinv Hwf.
    intros _e e Hevent Hstep Hperm.
    destructEvent; destructStep; unfold hook_post; wp_ret.
    (* [Enter]. *)
    { simpl. list. assumption. }
    (* [Exit]. *)
    { destructWf.
      erewrite postorder_stack_store by eauto.
      rewrite !rev_app_distr. simpl. list.
      simpl in Hinv. rewrite rev_app_distr in Hinv.
      tc. }}
  (* Completion. *)
  { intros (m & _vs).
    unfold traverse_postcondition.
    intros (rs' & marked' & σ' & vs & Hpost). unpack.
    subst σ'. simpl in Hpost0.
    wp_ret. pack; eauto using omarked_is_closure_start. }
Qed.

(* -------------------------------------------------------------------------- *)

(* The function [group] performs a depth-first traversal and constructs
   an array that maps each vertex [v] to the root of the tree where the
   vertex [v] appears in the DFS forest. *)

Section Group.

(* The array [_group] maps each vertex to the root of its DFS tree.
   This array is initialized during the traversal. *)

(* The optional vertex [_root] is the last encountered root vertex.
   The special value [none], which has type [_vertex] but is not a
   valid vertex, is used as a sentinel. When [_root] is [none], we
   are the top level. When [_root] is a valid vertex, we are not at
   the top level, and [_root] is the root of the current tree. *)

(* Another approach would be to maintain the length of the ghost stack
   at runtime. This approach has downsides, though: it adds one word
   to the state, and it requires arguing that overflow is impossible,
   which in turn requires bounding the length of the stack. *)

(* Our state is a tuple [G (_group, _root)]. *)

Notation _none := _n.
Notation none := n.

Inductive gstate :=
| G : array int → int → gstate.

Implicit Type _group : array int.
Implicit Type g : gstate.

Section Code.
Open Scope uint63.

Definition plain_group : array int :=
  do _group ← make _n 0 ; (* dummy *)
  do _root ← _none ;
  do g ← G _group _root ;
  let hook _e g :=
    let '(G _group _root) := g in
    match _e with
    | Enter _v =>
        (* If there was no current root then we are entering a new tree,
           whose root is [_v]. *)
        do _root ← if _root =? _none then _v else _root ;
        (* Record that [_v] belongs in a tree whose root is [_root]. *)
        do _group ← set _group _v _root ;
        G _group _root
    | Exit _v =>
        (* If the current root was [_v] then we are leaving a tree. *)
        do _root ← if _root =? _v then _none else _root ;
        G _group _root
    | Rediscover _ =>
        g
    end
  in
  do (m, g) ← traverse hook g ;
  let '(G _group _) := g in
  _group.

Derive group
  in (group = plain_group)
  as group_eq.
Proof using.
  intros. unfold plain_group, traverse, visit', visit.
  unfold group; reflexivity.
Defined.

End Code.

(* This definition states that [root] keeps correct track of the
   bottom vertex of the (ghost) stack [σ]. *)

Local Definition correct σ root :=
  if decide (len σ = 1) then root = none else bottom σ = Some root.

(* An auxiliary lemma: during a traversal, if the stack has a bottom
   vertex (i.e., if the stack currently has height greater than 1)
   then this vertex is a valid vertex. Therefore it is not [n],
   which we use to encode "no vertex". *)

Local Lemma wf_bottom_valid rs marked σ v :
  wf (rs, marked, σ) →
  permitted rs →
  bottom σ = Some v →
  0 ≤ v < n.
Proof.
  intros Hwf Hperm Hbottom.
  (* [v] is marked. *)
  generalize (wf_bottom_marked Hwf); intro Hbm.
  rewrite Hbottom in Hbm. simpl in Hbm.
  (* Every marked vertex is reachable. *)
  generalize (wf_reaches Hwf eq_refl); intro Hreaches.
  apply permitted_spec in Hperm.
  (* Therefore [v] is reachable. *)
  assert (v ∈ closure start) by set_solver.
  (* Therefore [v] is part of the universe. *)
  assert (v ∈ universe).
  { eauto using closure_start_subset_universe with set_solver. }
  (* The result follows by definition of the universe. *)
  set_solver.
Qed.

(* As a consequence, while [group] is running, the conditions
   [len σ = 1] and [root = none] are equivalent. That is, the
   test [root = none] is a correct way of determining whether
   we are currently at the top level. *)

Local Lemma toplevel_test rs marked σ root :
  wf (rs, marked, σ) →
  permitted rs →
  correct σ root →
  (len σ = 1 ↔ root = none).
Proof.
  unfold correct. intros Hwf Hperm Hinv. split; intro Heq;
    (destruct (decide (len σ = 1)); try tauto).
  (* The nontrivial subgoal is to prove that [root = none] implies
     [len σ = 1]. We have [bottom σ = Some root] and [root = none],
     so the bottom vertex of the stack is invalid. Contradiction. *)
  assert (0 ≤ root < none) by eauto using wf_bottom_valid.
  lia.
Qed.

(* [root] is correctly initialized. *)

Local Lemma correct_init : correct [Frame None Empty] none.
Proof. unfold correct. reflexivity. Qed.

(* [root] is correctly updated when a vertex is entered. *)

Local Lemma correct_enter rs marked σ v rs' marked' σ' root root' :
  wf (rs, marked, σ) →
  permitted rs →
  step (rs, marked, σ) (Enter v) (rs', marked', σ') →
  correct σ root →
  root' = (if decide (root = none) then v else root) →
  (* len σ' = 1 ∧ *)
  correct σ' root'.
Proof.
  unfold correct. intros Hwf Hperm Hstep Hcorrect Hroot'.
  assert (fact: len σ = 1 ↔ root = none) by eauto using toplevel_test.
  destructStep. subst root'. wf_nonempty.
  erewrite bottom_eq by eauto using wf_step.
  destruct (decide (root = none));
  destruct (decide (len σ = 1)); try tauto; length;
  destruct (decide (len σ + 1 = 1)); try lia; eauto.
Qed.

(* If [σ] is nonempty then [correct σ root] implies that [bottom σ]
   is [Some root]. *)

Local Lemma correct_nonempty rs marked σ v ws σ0 root :
  σ = Frame (Some v) ws :: σ0 →
  wf (rs, marked, σ) →
  correct σ root →
  bottom σ = Some root.
Proof.
  unfold correct. intros -> ? Hcorrect. length in Hcorrect.
  destructWf.
  destruct (decide (len σ0 + 1 = 1)); try lia.
  assumption.
Qed.

(* [root] is correctly updated when a vertex is exited. *)

Local Lemma correct_exit rs marked v ws σ σ0 σ' root root' :
  σ = Frame (Some v) ws :: σ0 →
  wf (rs, marked, σ) →
  correct σ root →
  σ' = store v ws σ0 →
  (root' = if decide (root = v) then none else root) →
  correct σ' root'.
Proof.
  intros ? Hwf Hcorrect ? Hroot'.
  assert (Hbottom: bottom σ = Some root)
    by eauto using correct_nonempty.
  unfold correct. subst.
  rewrite bottom_store, length_store. length.
  erewrite bottom_eq in Hbottom by eauto.
  destruct (decide (len σ0 = 1)).
  (* Case: [σ] has height 1. Then [v] must be [root]. *)
  { destruct (decide (root = v)); [| congruence ].
    reflexivity. }
  (* Case: [σ] has height greater than 1. Then [v] cannot be [root]. *)
  { assert (v ≠ root) by eauto using wf_top_ne_bottom.
    destruct (decide (root = v)); [ congruence |].
    assumption. }
Qed.

Local Hint Resolve correct_init correct_enter correct_exit : marble.

(* A specialized version of the lemma by the same name in dfs.v. *)

(* The lemma there represents a root map ρ as a function, whereas
   we represent it here as a list. *)

Lemma isRootMapStack_update rs marked σ ρ ρ' σ' v root' :
  isRootMapStack (λ v, ρ !!! v) σ →
  ρ' = <[v:=root']> ρ →
  valid v ρ →
  σ' = Frame (Some v) Empty :: σ →
  wf (rs, marked, σ') →
  correct σ' root' →
  isRootMapStack (λ v, ρ' !!! v) σ'.
Proof.
  intros. subst. eapply isRootMapStack_update; intros; tc; list;
    eauto using correct_nonempty.
Qed.

Local Hint Resolve
  isRootMapStack_init
  isRootMapStack_update
  isRootMapStack_store
  isRootMapStack_completion
: marble.

(* The specification of [group]. *)

Lemma wp_group :
  wp group (λ _group,
    (* [group] performs a depth-first traversal, building a (ghost)
       forest [vs]. *)
    ∃ marked vs ρ ,
    dfs marked vs ∧
    roots vs ⊆ start ∧
    start ⊆ marked ∧
    (* Furthermore, [group] returns an array [_group], whose length
       is [n], mapping every vertex to the root of its tree in the
       forest [vs]. *)
    rich.isArray isInt _group ρ ∧
    len ρ = n ∧
    isRootMap (λ v, ρ !!! v) vs
  ).
Proof.
  assert (unsigned n) by (arrays; lia).
  rewrite group_eq. unfold plain_group.
  wp_op (rich.wp_make isInt) introducing: _group.
  wp_bind_eq.
  wp_bind_eq.
  wp_op wp_traverse with invariant: (λ γ g,
    let '(rs, marked, σ) := γ in
    let '(G _group _root) := g in
    ∃ ρ root,
    rich.isArray isInt _group ρ ∧
    len ρ = n ∧
    isRootMapStack (λ v, ρ !!! v) σ ∧
    isInt _root root ∧
    unsigned root ∧
    correct σ root
  ).
  (* Compatibility. *)
  { intros ((rs0 & marked0) & σ) ((rs1 & marked1) & σ') Hequiv.
    unfold equiv in Hequiv. hnf in Hequiv. unpack. subst σ'.
    intros _vs ? <-. tauto. }
  (* Initialization. *)
  { simpl. pack; tc; length; tc. }
  (* Preservation. *)
  { clear dependent _group.
    intros ((rs & marked) & σ) ((rs' & marked') & σ').
    intros (_group & _root) Hinv Hwf.
    destruct Hinv as (ρ & root & Hinv). unpack in Hinv.
    intros _e e Hevent Hstep Hperm.
    assert (permitted rs) by eauto using step_prefix, permitted_prefix_of.
    assert (fact: len σ = 1 ↔ root = none) by eauto using toplevel_test.
    destructEvent; destructStep.
    (* Case [Enter]. *)
    {
      (* The definition of [root']. *)
      set (root' := if decide (root = none) then v else root).
      simple eapply @wp_bind with (P := λ _root',
        isInt _root' root' ∧ unsigned root'
      ).
      { wp_ret. unfold root'.
        destruct (decide (root = none));
        destruct (_root =? _none)%uint63 eqn:?;
        eauto with lia; exfalso; rewrite isInt_def in *; lia. }
      intros _root' (? & ?).
      (* Update the array [_group]. *)
      wp_op rich.wp_set shadowing: _group.
      assert (len (<[v:=root']> ρ) = n) by (length; eauto).
      (* Return. *)
      wp_ret. pack; eauto using wf_step with marble. (* TODO slow *)
    }
    (* Case [Exit]. *)
    {
      match goal with foo: stack vertex |- _ => rename foo into σ end.
      (* The definition of [root']. *)
      set (root' := if decide (root = v) then none else root).
      simple eapply @wp_bind with (P := λ _root',
        isInt _root' root' ∧ unsigned root'
      ).
      { wp_ret. unfold root'.
        destruct (decide (root = v));
        destruct (_root =? _v)%uint63 eqn:?;
        eauto with lia; exfalso; rewrite isInt_def in *; lia. }
      intros _root' (? & ?).
      (* Deductions. *)
      destructWf.
      length in *. destruct (decide (len σ + 1 = 1)); [ lia |].
      assert (root ≠ none) by lia. (* aha! *)
      (* Return. *)
      wp_ret.
      pack; eauto with marble.
    }
    (* Case [Rediscover]. *)
    { wp_ret. pack; eauto. }
  }
  (* Completion. *)
  { clear dependent _group.
    intros (m & [_group _root]) (rs' & marked' & σ' & vs & Hm & Hpost).
    unpack in Hpost. subst σ'.
    wp_ret. pack; tc. }
Qed.

End Group.

(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)

(* We now define a second copy of our DFS algorithm, this time in CPS style.  *)

(* The algorithm is essentially the same as earlier, but the traversal order
   is not exactly the same. Because the successors of each vertex are PUSHED
   onto the continuation in the order determined by [foreach_successor],
   they are EXAMINED in the reverse order. *)

(* This version of the code produces a cascade of events, that is, a lazy
   list of events, where each event is produced on demand, when requested by
   the consumer. Thus, the traversal can be interrupted and resumed by the
   consumer. *)

(* Because the cascade internally reads and updates an array [m], it must be
   considered linear. That is, a cascade MUST NOT be resumed several times.   *)

(* -------------------------------------------------------------------------- *)

(* Because (as explained above) the successors of each vertex are examined
   in reverse order, we have to reverse the way in which we use [complete]
   in our specifications. *)

(* [complete rs] is replaced with [complete (rev rs)]. *)

(* [permitted rs] is replaced with: [rev rs] is a SUFFIX of a complete
   enumeration of the start vertices. *)

(* This is a bit messy, but, up to these changes, the proofs go through
   without deep trouble. *)

Definition permitted_rev rs :=
  ∃ rs', complete (rs' ++ rev rs).

Local Notation perm_rev γ :=
  (permitted_rev (history γ)).

Local Lemma permitted_rev_nil : permitted_rev [].
Proof.
  destruct complete_nonempty as (rs & Hcomplete).
  unfold permitted_rev. exists rs. list. eauto.
Qed.

Local Lemma permitted_rev_prefix rs1 rs2 :
  permitted_rev (rs1 ++ rs2) → permitted_rev rs1.
Proof.
  unfold permitted_rev. intros (rs' & ?).
  rewrite rev_app_distr in *. rewrite app_assoc in *. eauto.
Qed.

Local Hint Rewrite
  @rev_app_distr
  @rev_involutive
: ulist clist.

(* -------------------------------------------------------------------------- *)

(* Cascades. *)

(* A cascade is a finite sequence of events,
   which are produced on demand. *)

(* It is isomorphic to the type [Seq.t] in OCaml's standard library. *)

(* The type of cascades, as well as the predicates that describe cascades,
   could be parameterized with the type of events and with the labeled
   transition system that describes the production of events. For now,
   we do not introduce this parameterization. *)

Inductive head :=
| Event : event _vertex → (unit → head) → head
| Done  : head.

Definition cascade :=
  unit → head.

(* [isCascade c γ] and [isHead h γ] mean that the cascade [c] or the head
   [h] represents a path, through the labeled transition system, from the
   state [γ] to a final state. The transition system is defined by:
   - the initial state [γ0];
   - the transition relation [step],
     which is further constrained by [wf] and by [permitted];
   - the final state property [horizontal γ0 _],
     which is further constrained by [wf] and by [complete]. *)

Inductive isHead : head → ghost → Prop :=
| isHeadEvent :
    ∀ γ _e e γ' c ,
    isEvent _e e →
    wf γ →
    step γ e γ' →
    perm_rev γ' →
    wp (c()) (λ h, isHead h γ') → (* [isCascade c γ'] *)
    isHead (Event _e c) γ
| isHeadDone :
    ∀ γ,
    wf γ →
    horizontal γ0 γ →
    complete (rev (history γ)) →
    isHead Done γ.

Definition isCascade (c : cascade) (γ : ghost) :=
  wp (c()) (λ h, isHead h γ).

(* -------------------------------------------------------------------------- *)

(* In the CPS-style algorithm, there is no user state [u : U] and no user
   invariant [inv]. They are not needed, since the user is in control and
   can write loops (if desired) outside of our view. *)

(* Therefore, a runtime state of the algorithm need not be a pair [(m, u)].
   It is just an array [m] of Boolean marks. *)

(* The following definitions are used to justify termination. They are
   similar to those given earlier, but concern [m] instead of [(m, u)]. *)

Open Scope marks_scope.

Local Definition mbeyond m :=
  { m' | m' ≤ m }.

(* [mrefl m] is [m] at type [mbeyond m]. *)

Local Definition mrefl m : mbeyond m.
Proof using.
  unfold mbeyond. exists m. eapply mle_refl.
Defined.

(* [mtrans], an identity function, proves that if [m1 ≤ m2] holds,
   and [m0] is beyond [m1], then [m0] is also beyond [m2]. *)

Local Definition mtrans {m1 m2} : m1 ≤ m2 → mbeyond m1 → mbeyond m2.
Proof using.
  intros ow12 (m0 & ow01). exists m0. eauto using mle_trans.
Defined.

(* -------------------------------------------------------------------------- *)

(* The code of the CPS-style DFS algorithm. *)

(* The answer type is [head]. Thus, instead of returning a result of type
   [mbeyond m], the recursive function [visit_cps] expects a continuation
   of type [mbeyond m → head] and returns an answer of type [head]. *)

(* There is no user function [hook]. Instead, to emit an event [_e], we
   return [Event (_e, k)], where [k] is the current continuation. Thus,
   the traversal is suspended and can be resumed by the user. *)

(* The function [visit_cps] is tail-recursive, and the continuation [k]
   can be viewed as a stack, which exists at runtime. Wrapping [k] in a
   λ-abstraction, so as to construct a new continuation, amounts to
   pushing data onto the stack. Applying [k] amounts to popping. This
   formulation is somewhat remarkable: even though an explicit stack is
   used, there is no need to argue about the size of the stack. The
   termination argument is the same as in the previous version of the
   code, and relies solely on the number of marked vertices. *)

(* In the code in direct style, the loop on the successors of [v] would
   EXAMINE each successor [w] in turn. (The state of that loop was the
   marks array, of type [below s].) Here, in contrast, the loop PUSHES
   each successor [w] in turn onto the continuation. (The state of this
   loop is the continuation, of type [mbelow m → head].) Therefore, here,
   the successors are examined in reverse order. This is still a valid DFS
   traversal; but [visit] and [visit_cps] do not construct the same DFS
   forest. *)

Local Fixpoint visit_cps m _v (ACC : Acc mlt m) (k : mbeyond m → head) : head :=
  IFC (_v <? length m)%uint63 THEN λ Hv,
  IFC get m _v THEN λ _,
    Event (Rediscover _v) @@ λ '(),
    k (mrefl m)
  ELSE λ Hunmarked,
    let m' := set m _v true in
    (* Emit an [Enter] event. *)
    Event (Enter _v) @@ λ '(),
    let ow : m' < m := marking_decreases_weight m _v Hv Hunmarked in
    (* Construct a continuation that emits an [Exit] event
       and returns by invoking [k]. Name it [k], too. *)
    let k (mow'' : mbeyond m') :=
      do mow'' ← mow'' ;
      Event (Exit _v) @@ λ '(),
      k (mtrans (mlt_mle_incl ow) mow'')
    in
    (* [push k _w] pushes the vertex [w] onto [k]. *)
    let push (k : mbeyond m' → head) _w : mbeyond m' → head :=
      λ mow'',
        let (m'', ow'') := mow'' in
        visit_cps m'' _w (Acc_inv ACC (mle_mlt_trans ow'' ow)) @@ λ mow'',
        k (mtrans ow'' mow'')
    in
    (* Push every successor [w] of [v] onto the continuation. *)
    do k ← foreach_successor k _v push ;
    (* Then, run (return to) this continuation. *)
    k (mrefl m')
  ELSE λ _,
    k (mrefl m).

(* [visit_cps'] is a simply-typed wrapper for [visit_cps]. *)

Local Definition visit_cps' m _v (k : marks → head) : head :=
  visit_cps m _v
    (Acc_intro_generator 64 wf_mlt m)
    (λ mow, k (proj1_sig mow)).

(* [traverse_cps] is the entry point of the traversal. *)

Definition traverse_cps : cascade :=
  (* Allocate an array of Boolean marks. *)
  do m ←  init _n (λ _i, false) ;
  (* Construct a trivial continuation. *)
  do k ← λ m, Done ;
  (* Push the start vertices onto this continuation. *)
  do k ← foreach_start k (λ k _v, λ m, visit_cps' m _v k) ;
  (* Wrap this continuation as a cascade, hiding [m]. *)
  λ '(), k m.

(* -------------------------------------------------------------------------- *)

(* A technical lemma about sets. *)

(* Because this lemma involves a double negation, it requires membership in
   a set to be decidable. *)

Context `{!RelDecision (∈@{vertices})}.

Local Lemma technical pushed0 pushed1 marked0 marked1 v w :
  pushed0 ∪ {[w]} ≡ pushed1 →
  successors v ∖ pushed1 ⊆ marked0 →
  marked0 ⊆ marked1 →
  {[w]} ⊆ marked1 →
  successors v ∖ pushed0 ⊆ marked1.
Proof using RelDecision0. clear- RelDecision0.
  (* Strangely enough, [set_solver] proves this goal, but, in an earlier
     version of this file, was unable to prove a similar goal.
     Furthermore, in the context where this lemma is applied,
     [set_solver] is unable to solve this goal. *)
  set_solver.
Qed.

(* -------------------------------------------------------------------------- *)

(* In direct style, we defined [visit_post], the postcondition of [visit].
   In CPS style, instead, we define [isCont], the precondition of the
   continuation of [visit_cps]. It expresses the same information. *)

(* [isCont k γ started examined] means that the continuation [k] can be
   applied to a marks array [m'] provided [m'] corresponds to a ghost
   state [γ'] such that [γ] and [γ'] are related by [horizontal] and such
   that, in the state [γ'], the start vertices in the list [started] have
   been visited, and the vertices in the set [examined] have been marked. *)

(* In [isCont], the argument of the continuation [k], a marks array, has
   type [mbeyond m]. *)

Local Definition isCont {m} (k : mbeyond m → head) γ started examined :=
  let '(rs, marked, σ) := γ in
  ∀ m' pf rs' marked' σ' γ',
  wf γ' →
  perm_rev γ' →
  horizontal γ γ' →
  isMarks m' marked' →
  γ' = (rs', marked', σ') →
  rs' = rs ++ started →
  examined ⊆ marked' →
  wp (k (exist m' pf)) (λ h, isHead h γ').

(* [isCont'] is a variant of [isCont] where the continuation [k] has a
   simple type, that is, the marks array has type [marks]. *)

Local Definition isCont' (k : marks → head) γ started examined :=
  let '(rs, marked, σ) := γ in
  ∀ m' rs' marked' σ' γ',
  wf γ' →
  perm_rev γ' →
  horizontal γ γ' →
  isMarks m' marked' →
  γ' = (rs', marked', σ') →
  rs' = rs ++ started →
  examined ⊆ marked' →
  wp (k m') (λ h, isHead h γ').

Local Hint Resolve mle_mlt_trans : marble.

(* The specification of [visit_cps]. *)

Local Lemma wp_visit_cps m (ACC : Acc mlt m) :
  ∀ _v v (k : mbeyond m → head) rs marked σ γ started,
  wf γ →
  perm_rev γ →
  isMarks m marked →
  γ = (rs, marked, σ) →
  isInt _v v →
  0 ≤ v < n →
  edge (top σ) v →
  started = (if decide (len σ = 1) then {[v]} else []) →
  permitted_rev (rs ++ started) →
  isCont k γ started {[v]} →
  wp (visit_cps m _v ACC k) (λ h, isHead h γ).
Proof.
  clear dependent foreach_start start_respects_bound.
  by dependent induction on m ACC. intros m ? ?.
  intros. wp_last Hcont.
  simpl visit_cps.
  destructMarks. arrays.
  assert (1 ≤ len σ)%Z by eauto using wf_nonempty.
  assert (perm_rev γ).
  { unfold perm_rev; subst γ. eauto using permitted_rev_prefix. }
  wp_if; [| lia].
  wp_if.
  (* Case: [v] is marked already. *)
  { clear foreach_successor wp_foreach_successor IH.
    (* Emit a [Rediscover] event. *)
    set (rs' := rs ++ started).
    set (γ' := (rs', marked, σ)).
    assert (step γ (Rediscover v) γ').
    { subst γ γ' started rs'. econstructor; try clarify; tc. }
    assert (wf γ') by tc.
    wp_ret. eapply isHeadEvent; tc.
    (* Invoke [k]. *)
    unfold mrefl. subst γ.
    wp_op Hcont; eauto with horizontal set_solver.
  }
  (* Case: [v] is unmarked. *)
  assert (Hm': isMarks (set m _v true) ({[v]} ∪ marked))
    by eauto using isMarks_set.
  revert Hm'.
  set (m' := set m _v true).
  set (rs' := rs ++ started).
  set (marked' := {[v]} ∪ marked).
  set (σ' := Frame (Some v) Empty :: σ).
  set (γ' := (rs', marked', σ')).
  intro.
  (* Emit an [Enter] event. *)
  assert (step γ (Enter v) γ').
  { subst γ γ' started rs' marked'.
    econstructor; try clarify; eauto 2 with marble set_solver. }
  assert (len σ' = len σ + 1) by tc.
  wp_ret. eapply isHeadEvent; tc.
  assert (m' < m).
  { eapply marking_decreases_weight; eauto. }
  (* We reach the loop on the successors of [v]. *)
  (* The loop invariant requires a little thought. As the loop progresses,
     the set [pushed] grows from ∅ to [successors v]. The current state of
     the loop is a continuation [k]. Initially, [k] is a continuation that
     expects all vertices to have been examined: it satisfies the formula
     [isCont k γ' [] (successors v)]. At the end, [k] is a continuation
     that needs no vertices to have been examined: it satisfies the
     formula [isCont k γ' [] ∅]. Therefore the loop invariant should be
     [isCont k γ' [] examined] where [examined] is [successors v ∖ pushed]. *)
  wp_op wp_foreach_successor with invariant: (
    λ pushed (k : mbeyond m' → head),
      let examined := successors v ∖ pushed in
      isCont k γ' [] examined
  ).
  (* Compatibility. (This is a bit painful.) *)
  { intros pushed1 pushed2 ?. intros k' ? <-.
    split; intros; unpack; pack; eauto; set_solver. }
  (* Initialization. *)
  (* In this subgoal, [pushed] is empty, so [examined] is [successors v].
     Therefore we are reasoning about the continuation that is invoked
     AFTER all successors have been examined. This corresponds to the code
     that would FOLLOW the loop in direct style. *)
  { clear foreach_successor wp_foreach_successor IH. (* for clarity *)
    unfold isCont, γ'. fold γ'.
    intros m'' ? rs'' marked'' σ'' γ''. intros. subst rs''.
    wp_bind_eq.
    (* The structure of the ghost stack has been preserved. *)
    assert (∃ vs, σ'' = Frame (Some v) vs :: σ) as (vs & ?).
    { eauto using horizontal_populates_top_frame. }
    set (marked''' := marked'').
    set (σ''' := store v vs σ).
    set (γ''' := (rs', marked''', σ''')).
    (* Emit an [Exit] event. *)
    assert (step γ'' (Exit v) γ''').
    { subst γ'' γ'''. list. econstructor; eauto with set_solver. }
    assert (wf γ''') by tc.
    assert (marked' ⊆ marked'') by tc.
    wp_ret. eapply isHeadEvent; tc.
    (* Invoke [k]. *)
    unfold mtrans. subst γ.
    wp_op Hcont; eauto with horizontal set_solver. }
  (* Preservation. *)
  { wp_body pushed0 pushed1 k''
      introducing: (fun _ => intros w ???; intros _w ?).
    (* The loop body constructs and returns a new continuation. *)
    wp_ret. unfold isCont. unfold γ'; fold γ'. list.
    intros m'' ? rs'' marked'' σ'' γ''. intros. subst rs''.
    (* We are now looking at a recursive call. The state at this point is
       described by [γ'']. The vertex [w], a successor of [v], is about to
       be examined. *)
    assert (E v w) by set_solver.
    assert (edge (top σ') w) by eauto.
    assert (len σ'' = len σ') by tc. (* [len σ'' ≠ 1] *)
    assert (2 ≤ len σ'')%Z by lia.
    wp_op IH; tc; destruct (decide (len σ'' = 1)); try lia; list.
    { eauto using permitted_rev_prefix. }
    clear wp_foreach_successor IH. (* for clarity *)
    (* There remains to argue that [isCont ...] implies [isCont ...]. *)
    (* In other words, we must argue that the recursive call has
       re-established the loop invariant. *)
    unfold γ', isCont in Hinv. fold γ' in Hinv.
    subst γ''. unfold isCont, mtrans.
    intros m''' ? rs''' marked''' σ''' γ'''. intros. subst rs'''.
    assert (marked'' ⊆ marked''') by tc.
    assert (horizontal γ' γ''') by eauto 2 using horizontal_transitive.
    eapply Hinv; eauto using technical. }
  (* Completion. *)
  (* [pushed] is [successors v], so [examined] is empty. *)
  { clear foreach_successor wp_foreach_successor IH. (* for clarity *)
    cbv beta zeta. intros k' (pushed & Hk' & Hpushed).
    (* There remains to argue that [isCont ...] implies [isCont ...]. *)
    assert (wf γ') by tc.
    assert (horizontal γ' γ') by eauto with horizontal.
    eapply Hk'; eauto using app_nil_r_sym with set_solver. }
Qed.

(* The specification of [visit_cps']. *)

Local Lemma wp_visit_cps' m _v v (k : marks → head) rs marked σ γ started :
  wf γ →
  perm_rev γ →
  isMarks m marked →
  γ = (rs, marked, σ) →
  isInt _v v →
  0 ≤ v < n →
  edge (top σ) v →
  started = (if decide (len σ = 1) then {[v]} else []) →
  permitted_rev (rs ++ started) →
  isCont' k γ started {[v]} →
  wp (visit_cps' m _v k) (λ h, isHead h γ).
Proof.
  intros. subst γ. unfold visit_cps'.
  wp_op wp_visit_cps; last eauto.
  (* There remains to argue that [isCont' ...] implies [isCont ...]. *)
  unfold isCont, isCont' in *. simpl proj1_sig.
  eauto.
Qed.

(* The specification of [traverse_cps]. *)

(* The postcondition is simple: [traverse_cps] returns a cascade of events
   that obeys the labeled transition system defined by the initial state
   [γ0], the relation [step], and the predicate [horizontal γ0], which
   identifies the final states. *)

Lemma wp_traverse_cps :
  wp traverse_cps (λ c, isCascade c γ0).
Proof.
  intros. unfold traverse_cps.
  wp_op (wp_init (λ _, false)) introducing: m.
  { intros. wp_ret. }
  assert (isMarks m ∅) by eauto using isMarks_intro with lia.
  (* Build the final continuation. *)
  eapply wp_bind with (P := λ k,
    ∀ started, complete (rev started) →
    isCont' k γ0 started start
  ).
  { wp_ret. intros started Hstarted.
    unfold isCont'. unfold γ0; fold γ0. simpl. intros. subst.
    wp_ret. eapply isHeadDone; assumption. }
  intros k Hk.
  (* Push the start vertices onto the continuation. *)
  (* The loop invariant, specialized with [pushed := ∅], matches the
     specification of the final continuation that we have given above.
     This loop invariant is a bit subtle. We do not know, ahead of time,
     in what order the start vertices will be produced by [foreach_start].
     At a given point in time, we do have access to the list of start
     vertices already produced; it is the list [pushed]. We quantify over
     all possible orders in which the remaining start vertices might be
     produced: this is the list [started]. This quantification is subject
     to the constraint that [pushed ++ rev started] is a complete
     enumeration of the start vertices. *)
  wp_op wp_foreach_start with invariant: (λ pushed k,
    ∀ started,
    complete (pushed ++ rev started) →
    isCont' k γ0 started (start ∖ list_to_set pushed)
  ).
  (* Initialization. *)
  { unfold γ0, isCont' in *. intros. list in *.
    eapply Hk; eauto with set_solver. }
  (* Preservation. *)
  { wp_body pushed0 pushed1 k''
      introducing: (fun _ => intros _v v ?? Hpermitted).
    subst pushed1.
    assert (v ∈ start).
    { apply permitted_spec in Hpermitted. set_solver. }
    (* The loop body constructs and returns a new continuation. *)
    wp_ret. intros started Hstarted. list in Hstarted.
    unfold isCont'. unfold γ0; fold γ0.
    intros m' rs' marked' σ' γ'. simpl. intros. subst rs'.
    assert (len σ' = 1) by tc.
    wp_op wp_visit_cps'; eauto.
    { clarify. list.
      (* To prove that [started ++ {[v]}] is reverse permitted,
         we use the fact that [{[v]} ++ rev started] is a suffix
         of a complete list. *)
      unfold permitted_rev. list. eauto. }
    (* There remains to argue that [isCont' ...] implies [isCont' ...]. *)
    unfold isCont' in *.
    unfold γ0 in Hinv; fold γ0 in Hinv.
    match goal with h: γ' = _ |- _ => rewrite h; rewrite <- h end.
    clarify. list.
    intros m'' rs'' marked'' σ'' γ''. intros. subst rs''.
    assert (horizontal γ0 γ'') by eauto 2 using horizontal_transitive.
    assert (marked' ⊆ marked'') by tc.
    assert (complete (pushed0 ++ rev (started ++ {[v]}))).
    { list. assumption. }
    eapply Hinv; eauto with set_solver. }
  (* Completion. *)
  { intros k' (pushed & Hk' & Hcomplete).
    wp_ret. unfold isCascade.
    assert (perm_rev γ0).
    { unfold perm_rev, γ0. eapply permitted_rev_nil. }
    assert (complete (pushed ++ rev [])).
    { list. assumption. }
    eapply Hk'; eauto using wf_init with horizontal set_solver. }
Qed.

End G.

(* -------------------------------------------------------------------------- *)
