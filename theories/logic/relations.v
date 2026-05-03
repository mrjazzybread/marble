(* This library defines some vocabulary about relations, which can also be
   understood as vocabulary about graphs, since a graph *is* a relation on
   vertices.

   We begin with the idea of the image of a set under a relation: [image],
   [into], [closed]. We continue with the idea of paths and reflexive
   transitive closure: [path], [closure], [reaches]. Then, we prove some
   properties about the reverse of a relation: [flip], the intersection of a
   relation and its reverse: [scc], and the strongly connected component of
   a vertex: [component]. *)

(* We write [V : Type] for a type of vertices and [E : V → V → Prop] for a
   relation on vertices. *)

From stdpp Require Import sets propset.
Local Notation set := propset.
From marble Require Import tactics sets.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)

(* Abbreviations for the most common properties of relations. *)

(* These notions are also defined in [Coq.Relations.Relation_Definitions].
   However, notations seem to be preferable to definitions, as definitions
   are not properly unfolded during proof search. *)

(* Reflexivity. *)

Notation reflexive E := (∀ v, E v v).

(* Symmetry. *)

Notation symmetric E := (∀ v w, E v w -> E w v).

(* Transitivity. *)

Notation transitive E := (∀ v w x, E v w -> E w x -> E v x).

(* -------------------------------------------------------------------------- *)

(* [image], [into], [outof], [closed]. *)

Section Image.

Variable V : Type.
Variable E : V → V → Prop.

Implicit Types vs ws : set V.

(* The image of a set under a relation. *)

Definition image vs : set V :=
  {[w | ∃ v, v ∈ vs ∧ E v w]}.

(* The predicate [into vs ws] means that the image of the set [vs]
   under the successor relation lies in the set [ws]. *)

Notation into vs ws :=
  (image vs ⊆ ws).

(* [outof vs ws] means that the image of [vs] contains [ws]. *)

Notation outof vs ws :=
  (ws ⊆ image vs).

(* [closed vs] means that set [vs] is closed under successors. *)

Notation closed vs :=
  (into vs vs).

(* -------------------------------------------------------------------------- *)

(* Properties of [image]. *)

(* This lemma characterizes membership in an image. *)

Lemma elem_of_image w vs :
  w ∈ image vs ↔ ∃ v, v ∈ vs ∧ E v w.
Proof. unfold image. elem. tauto. Qed.

Lemma elem_of_image_singleton w v :
  w ∈ image {[v]} ↔ E v w.
Proof.
  rewrite elem_of_image.
  split.
  + intros (? & ? & ?). elem in *. subst. assumption.
  + intros. exists v. elem. eauto.
Qed.

(* The larger the set, the larger its image. *)

Lemma image_covariant vs ws : vs ⊆ ws → image vs ⊆ image ws.
Proof. set_solver. Qed.

Global Instance : Proper (subseteq ==> subseteq) image.
Proof. repeat intro. set_solver. Qed.

Global Instance : Proper (equiv ==> equiv) image.
Proof. repeat intro. set_solver. Qed.

(* The image of a union is the union of the images. *)

Lemma image_union vs1 vs2 :
  image (vs1 ∪ vs2) ≡ image vs1 ∪ image vs2.
Proof. set_solver. Qed.

(* The image of the empty set is empty. *)

Lemma image_empty :
  image ∅ ≡ ∅.
Proof. set_solver. Qed.

Lemma prove_image_empty vs : image ∅ ⊆ vs.
Proof. set_solver. Qed.

(* If [E] is reflexive, then [image] is increasing. *)

Lemma image_increasing vs : reflexive E → vs ⊆ image vs.
Proof. set_solver. Qed.

(* If [E] is transitive, then [image] is idempotent (one way). *)

Lemma image_idempotent_1 vs :
  transitive E → image (image vs) ⊆ image vs.
Proof. set_solver. Qed.

(* If [E] is reflexive, then [image] is idempotent (the other way). *)

Lemma image_idempotent_2 vs :
  reflexive E → image vs ⊆ image (image vs).
Proof. set_solver. Qed.

(* -------------------------------------------------------------------------- *)

(* Properties of [closed]. *)

(* An edge cannot leave a closed set. *)

Lemma use_closed vs v w : closed vs → E v w → v ∈ vs → w ∈ vs.
Proof. set_solver. Qed.

(* If [rs] is a subset of [vs] and [vs] is closed, then [image rs]
   is also a subset of [vs]. *)

Lemma prove_subset_image_left rs vs : rs ⊆ vs → closed vs → image rs ⊆ vs.
Proof. set_solver. Qed.

(* The union of two closed sets is closed. *)

Lemma prove_closed_union vs ws :
  closed vs → closed ws → closed (vs ∪ ws).
Proof. set_solver. Qed.

End Image.

Local Hint Rewrite
  @elem_of_image_singleton
  @elem_of_image
: elem_of.

Notation into E vs ws :=
  (image E vs ⊆ ws).

Notation outof E vs ws :=
  (ws ⊆ image E vs).

Notation closed E vs :=
  (into E vs vs).

(* -------------------------------------------------------------------------- *)

(* We now consider two relations [E1] and [E2] and examine how
   [image], [into], and [closed] behave when one moves from one
   relation to another. *)

Section VarianceWithRespectToE.

Variable V : Type.
Variable E1 E2 : V → V → Prop.

(* We assume that [E2] contains [E1]. *)

Variable subrel : ∀ v w, E1 v w → E2 v w.

Lemma image_covariant_E vs : image E1 vs ⊆ image E2 vs.
Proof. set_solver. Qed.

Lemma into_contravariant_E vs ws : into E2 vs ws → into E1 vs ws.
Proof. set_solver. Qed.

End VarianceWithRespectToE.

Global Instance Proper_image' {V} :
  Proper (subrelation ==> equiv ==> subseteq) (@image V).
Proof. repeat intro. set_solver. Qed.

Global Instance Proper_image'' {V} :
  Proper (relation_equivalence ==> equiv ==> equiv) (@image V).
Proof.
  intros E1 E2 Hrequiv.
  assert (H12: subrelation E1 E2).
  { apply subrelation_partial_order. symmetry. assumption. }
  assert (H21: subrelation E2 E1).
  { apply subrelation_partial_order. assumption. }
  repeat intro. set_solver.
  (* not sure why this works, while [rewrite] doesn't *)
Qed.

(* -------------------------------------------------------------------------- *)

(* [path], [closure], [reaches], [scc], [component]. *)

Section PathsAndClosure.

Variable V : Type.
Variable E : V → V → Prop.

(* -------------------------------------------------------------------------- *)

(* Paths. *)

(* A path in the graph. *)

(* This is the reflexive-transitive closure of the relation [E]. *)

Inductive path : V → V → Prop :=
| PathNil:
    ∀ x,
    path x x
| PathCons:
    ∀ x y z,
    E x y →
    path y z →
    path x z.

Hint Constructors path : path.

Lemma path_transitive: transitive path.
Proof. induction 1; eauto with path. Qed.

Hint Resolve path_transitive : path.

(* A path cannot escape a closed set. *)

Lemma no_escape vs :
  closed E vs → ∀ v w, path v w → v ∈ vs → w ∈ vs.
Proof.
  induction 2; intros; eauto using use_closed.
Qed.

(* Being closed under edges is equivalent to being closed under paths. *)

Lemma closed_path_closed_E vs :
  closed path vs →
  closed E vs.
Proof.
  intros. eapply into_contravariant_E; [| eauto ]. eauto with path.
Qed.

Lemma closed_E_closed_path vs :
  closed E vs →
  closed path vs.
Proof.
  intros.
  eapply prove_subset; intros.
  elem in *. unpack.
  eauto using no_escape.
Qed.

Lemma closed_path vs :
  closed path vs ↔ closed E vs.
Proof.
  split; eauto using closed_path_closed_E, closed_E_closed_path.
Qed.

(* -------------------------------------------------------------------------- *)

(* Closure. *)

(* The closure of [vs] is its image under the relation [path]. *)

Notation closure vs :=
  (image path vs).

(* We write [reaches vs ws] if every element of [ws] can be reached from
   some element of [vs], i.e., [ws] is contained in the closure of
   [vs]. This can also be viewed as an extension of the [path] predicate
   to a (disjunctive) set of source vertices and a (conjunctive) set of
   target vertices. *)

Notation reaches vs ws :=
  (ws ⊆ closure vs).

(* The relation [reaches] is reflexive. *)

Lemma reaches_reflexive vs : reaches vs vs.
Proof. eauto using image_increasing with path. Qed.

(* Every set reaches its closure. *)

Goal ∀ vs, reaches vs (closure vs).
Proof. eauto using reaches_reflexive. Qed.

(* A closure is closed. *)

Lemma closed_closure vs :
  closed path (closure vs).
Proof.
  eauto using image_idempotent_1 with path.
Qed.

(* If a closed set [ws] contains [vs],
   then it also contains [closure vs]. *)

Lemma prove_closure_subset vs ws :
  vs ⊆ ws →
  closed path ws →
  closure vs ⊆ ws.
Proof. set_solver. Qed.

(* The image of [vs] is a subset of its closure. *)

Lemma prove_image_subset_closure vs :
  image E vs ⊆ closure vs.
Proof.
  eauto using image_covariant_E with path.
Qed.

(* The above lemma can also be read as: a set reaches its own image. *)

Goal ∀ vs, reaches vs (image E vs).
Proof.
  exact prove_image_subset_closure.
Qed.

(* The relation [reaches] is transitive. *)

Lemma reaches_transitive xs ys zs :
  reaches xs ys →
  reaches ys zs →
  reaches xs zs.
Proof.
  generalize (@closed_closure xs). set_solver.
Qed.

(* Every set reaches the empty set. *)

Goal ∀ vs, reaches vs ∅.
Proof. set_solver. Qed.

(* Every set reaches itself (and every subset of itself). *)

Lemma prove_reaches_self vs ws :
  ws ⊆ vs → reaches vs ws.
Proof.
  eauto using subset_transitive, image_increasing with path.
Qed.

(* The singleton [v] reaches the singleton [w] if and only if there
   is a path of [v] to [w]. This is stated by the following two lemmas. *)

Lemma reaches_singleton_singleton v w :
  reaches {[v]} {[w]} ↔ path v w.
Proof. set_solver. Qed.

Lemma prove_reaches_singleton_singleton v w :
  E v w →
  reaches {[v]} {[w]}.
Proof.
  rewrite reaches_singleton_singleton. eauto with path.
Qed.

(* Special cases of [reaches_contravariant]. *)

Lemma prove_reaches_union_left_1 vs1 vs2 ws :
  reaches vs1 ws →
  reaches (vs1 ∪ vs2) ws.
Proof. set_solver. Qed.

Lemma prove_reaches_union_left_2 vs1 vs2 ws :
  reaches vs2 ws →
  reaches (vs1 ∪ vs2) ws.
Proof. set_solver. Qed.

(* -------------------------------------------------------------------------- *)

(* The relation [scc] is the intersection of [path E] and its reverse.
   Less abstractly put, [scc v w] holds if and only if there is a path
   from [v] to [w] and back. *)

Definition scc v w :=
  path v w ∧ path w v.

(* The strongly connected component of [v]. *)

Definition component v :=
  {[ w | scc v w ]}.

(* Membership in a component. *)

Lemma elem_of_component v w :
  w ∈ component v ↔ scc v w.
Proof. set_solver. Qed.

(* [scc] is an equivalence relation. *)

Lemma scc_reflexive: reflexive scc.
Proof. unfold scc. eauto with path. Qed.

Lemma scc_symmetric: symmetric scc.
Proof. unfold scc. intuition eauto. Qed.

Lemma scc_transitive: transitive scc.
Proof. unfold scc. intuition eauto with path. Qed.

(* The following two lemmas unfold the definition of [scc]. *)

Lemma use_scc_left v w : scc v w → path v w.
Proof. inversion 1; auto. Qed.

Lemma use_scc_right v w : scc v w → path w v.
Proof. inversion 1; auto. Qed.

(* The strongly connected component of [v] is a subset of the closure
   of the singleton {[v]}. *)

Lemma prove_component_subset_closure v :
  component v ⊆ closure {[v]}.
Proof.
  unfold component, scc.
  eapply prove_subset; intros w ?.
  elem in *.
  set_solver.
Qed.

End PathsAndClosure.

Hint Rewrite
  @elem_of_component
: elem_of.

Notation closure E vs :=
  (image (path E) vs).

Notation reaches E vs ws :=
  (ws ⊆ closure E vs).

(* -------------------------------------------------------------------------- *)

(* Define hint databases. *)

Hint Constructors path : path.

Hint Resolve
  path_transitive
: path.

Hint Resolve
  scc_reflexive
  scc_symmetric
  scc_transitive
: scc.

Hint Unfold scc : scc.

Hint Resolve
  reaches_reflexive
  prove_subset_empty_left
  prove_subset_union_left
  prove_image_subset_closure
: reaches.

Hint Resolve
  closed_path_closed_E
  closed_E_closed_path
: closed.

(* -------------------------------------------------------------------------- *)

Section MoreVarianceWithRespectToE.

Variable V : Type.
Variable E1 E2 : V → V → Prop.

(* We assume that [E2] contains [E1]. *)

Variable subrel : ∀ v w, E1 v w → E2 v w.

Lemma path_covariant_E v w :
  path E1 v w → path E2 v w.
Proof.
  induction 1; eauto with path.
Qed.

Lemma component_covariant_E v :
  component E1 v ⊆ component E2 v.
Proof.
  eapply prove_subset. intros w.
  unfold component. elem.
  unfold scc. intuition auto using path_covariant_E.
Qed.

End MoreVarianceWithRespectToE.

(* -------------------------------------------------------------------------- *)

(* We now prove properties that involve both [E] and [flip E]. *)

Section Flip.

Variable V : Type.
Variable E : V → V → Prop.

(* [path] and [flip] commute. *)

Lemma prove_path_flip v w :
  path E v w →
  path (flip E) w v.
Proof.
  induction 1; eauto with path.
Qed.

Lemma use_path_flip v w :
  path (flip E) w v →
  path E v w.
Proof.
  induction 1; eauto with path.
Qed.

Lemma path_flip v w :
  flip (path E) v w ↔ path (flip E) v w.
Proof.
  split.
  + eauto using prove_path_flip.
  + unfold flip. eauto using use_path_flip.
Qed.

Lemma path_flip_equiv :
  relation_equivalence
    (flip (path E))
    (path (flip E)).
Proof. repeat intro. eapply path_flip. Qed.

Lemma prove_closed_path_complement vs :
  closed (path E) vs →
  closed (path (flip E)) (⊤ ∖ vs).
Proof.
  intros.
  rewrite <- path_flip_equiv.
  set_solver.
Qed.

(* The strongly connected components are the same with respect to [E]
   and with respect to [flip E]. *)

Lemma scc_flip v w :
  scc (flip E) v w ↔ scc E v w.
Proof.
  unfold scc. rewrite <- !path_flip. unfold flip. tauto.
Qed.

Lemma scc_flip_equiv :
  relation_equivalence
    (scc (flip E))
    (scc E).
Proof. repeat intro. eapply scc_flip. Qed.

Lemma component_flip v:
  component (flip E) v ≡ component E v.
Proof.
  unfold component.
  eapply prove_equiv. intro w.
  elem. eapply scc_flip.
Qed.

(* As a corollary, the strongly connected component of [v] is a subset
   of both the closure of [v] w.r.t. [E] and the closure of [v] w.r.t.
   [flip E]. *)

Lemma prove_component_subset_closure_flip v :
  component E v ⊆ closure (flip E) {[v]}.
Proof.
  intros.
  rewrite <- component_flip.
  eapply prove_component_subset_closure.
Qed.

(* In fact, it is exactly the intersection of these two sets. *)

Lemma prove_intersection_subset_component v :
  closure E {[v]} ∩ closure (flip E) {[v]} ⊆ component E v.
Proof.
  intros.
  eapply prove_subset; intros w.
  rewrite elem_of_intersection. intros (? & ?).
  elem. rewrite !elem_of_image_singleton in *.
  unfold scc. eauto using use_path_flip.
Qed.

(* If [vs] is closed under successor
   then its complement is closed under predecessor. *)

Lemma prove_closed_complement vs :
  closed E vs →
  closed (flip E) (⊤ ∖ vs).
Proof. set_solver. (* wow *) Qed.

Lemma use_closed_complement `{!RelDecision (∈@{set V})} vs :
  closed (flip E) (⊤ ∖ vs) →
  closed E vs.
Proof.
  intros.
  assert (fact: closed E (⊤ ∖ (⊤ ∖ vs))) by set_solver.
  rewrite double_complement in fact by assumption.
  assumption.
Qed.

Lemma closed_complement `{!RelDecision (∈@{set V})} vs :
  closed (flip E) (⊤ ∖ vs) ↔
  closed E vs.
Proof.
  split; eauto using prove_closed_complement, use_closed_complement.
Qed.

End Flip.

Section Again.

Variable V : Type.
Variable E : V → V → Prop.

Lemma closed_complement' `{!RelDecision (∈@{set V})} vs :
  closed E (⊤ ∖ vs) ↔
  closed (flip E) vs.
Proof.
  change E with (flip (flip E)) at 1.
  eauto using closed_complement.
Qed.

End Again.
