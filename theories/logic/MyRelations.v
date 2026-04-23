(* This library defines some vocabulary about relations. We begin with the
   idea of the image of a set under a relation: [image], [into], [closed].
   We continue with the idea of paths and reflexive-transitive closure:
   [path], [closure], [reaches]. Then, we introduce the reverse of a
   relation: [reverse], and the intersection of a relation and its reverse:
   [scc]. *)

From stdpp Require Import sets propset.
Local Notation set := propset.

From marble Require Import tactics.

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

(* Some lemmas about sets. *)

(* TODO move? *)

Section Sets.

(* A type of elements. *)

Variable V : Type.

Implicit Types vs ws : set V.

Lemma prove_subset vs ws : (∀ v, v ∈ vs → v ∈ ws) → vs ⊆ ws.
Proof. set_solver. Qed.

Lemma prove_equiv vs ws : (∀ v, v ∈ vs ↔ v ∈ ws) → vs ≡ ws.
Proof. set_solver. Qed.

Lemma subset_transitive vs ws zs :
  vs ⊆ ws → ws ⊆ zs → vs ⊆ zs.
Proof. set_solver. Qed.

Lemma subset_antisymmetric vs ws :
  vs ⊆ ws → ws ⊆ vs → vs ≡ ws.
Proof. set_solver. Qed.

Lemma prove_subset_empty_left vs : ∅ ⊆ vs.
Proof. set_solver. Qed.

Lemma prove_subset_union_left vs1 vs2 ws :
  vs1 ⊆ ws -> vs2 ⊆ ws -> vs1 ∪ vs2 ⊆ ws.
Proof. set_solver. Qed.

Lemma prove_subset_diff_union vs ws : (ws ∪ vs) ∖ ws ⊆ vs.
Proof. set_solver. Qed.

Lemma prove_subset_union_diff `{!RelDecision (∈@{set V})} vs ws :
  vs ⊆ (vs ∖ ws) ∪ ws.
Proof. rewrite difference_union. set_solver. Qed.

Lemma prove_subset_intersection_right vs vs1 vs2 :
  vs ⊆ vs1 -> vs ⊆ vs2 -> vs ⊆ vs1 ∩ vs2.
Proof. set_solver. Qed.

End Sets.

Local Hint Rewrite
  @elem_of_PropSet
  @not_elem_of_PropSet
: sets.

Local Ltac sets :=
  autorewrite with sets in *.

(* -------------------------------------------------------------------------- *)

(* In this section, we fix a relation [E]. *)

Section Relations.

(* A type of elements. *)

Variable V : Type.

Implicit Types vs ws : set V.

(* A relation. *)

Variable E : V → V → Prop.

(* The image of a set under a relation. *)

Definition image vs : set V :=
  {[w | ∃ v, v ∈ vs /\ E v w]}.

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

(* This lemma proves membership in an image. *)

Lemma prove_member_image v vs w : v ∈ vs → E v w → w ∈ image vs.
Proof. set_solver. Qed.

(* This lemma characterizes membership in an image. *)

Lemma elem_of_image w vs :
  w ∈ image vs ↔ ∃ v, v ∈ vs /\ E v w.
Proof. unfold image. sets. tauto. Qed.

Lemma elem_of_image_singleton w v :
  w ∈ image {[v]} ↔ E v w.
Proof.
  unfold image. sets. split.
  + intros (? & ? & ?). rewrite elem_of_singleton in *. subst. assumption.
  + intros. exists v. rewrite elem_of_singleton. eauto.
Qed.

(* [image] is compatible with set equivalence. *)

Global Instance : Proper (equiv ==> equiv) image.
Proof.
  intros vs ws Hequiv.
  eapply prove_equiv. intro v. rewrite !elem_of_image.
  split; intros (w & ? & ?); exists w.
  + rewrite <- Hequiv. eauto.
  + rewrite Hequiv. eauto.
Qed.

(* The larger the set, the larger its image. *)

Lemma image_covariant vs ws : vs ⊆ ws → image vs ⊆ image ws.
Proof. set_solver. Qed.

(* The image of a union is the union of the images. This is stated
   by the following two lemmas. *)

Lemma prove_subset_image_union_left vs1 vs2 :
  image (vs1 ∪ vs2) ⊆ image vs1 ∪ image vs2.
Proof. set_solver. Qed.

Lemma prove_subset_image_union_right vs1 vs2 :
  image vs1 ∪ image vs2 ⊆ image (vs1 ∪ vs2).
Proof. set_solver. Qed.

(* The image of the empty set is empty. *)

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

(* This lemma exploits membership in an image. *)

Lemma use_member_image_singleton v w : w ∈ image {[v]} → E v w.
Proof. set_solver. Qed.

(* -------------------------------------------------------------------------- *)

(* Properties of [into]. *)

(* [into vs ws] is contravariant in [vs]. *)

Lemma into_contravariant vs1 vs2 ws :
  into vs1 ws → vs2 ⊆ vs1 → into vs2 ws.
Proof. set_solver. Qed.

(* In order to prove that [image vs] is empty, one must establish
   that an element of [vs] has no successor. *)

Lemma prove_into_empty vs :
  (∀ v w, v ∈ vs → ¬ E v w) → into vs ∅.
Proof. set_solver. Qed.

(* Union in the left-hand side of [into] can be decomposed. *)

Lemma prove_into_union_left vs1 vs2 ws :
  into vs1 ws → into vs2 ws → into (vs1 ∪ vs2) ws.
Proof. set_solver. Qed.

(* This is a variant of the above lemma, where the union in the
   left-hand side is not explicitly apparent, but is created via
   [prove_subset_union_diff]. *)

Lemma prove_into_union_diff `{!RelDecision (∈@{set V})} vs1 vs2 ws :
  into (vs1 ∖ vs2) ws →
  into vs2 ws →
  into vs1 ws.
Proof.
  eauto using
    into_contravariant, prove_into_union_left, prove_subset_union_diff.
Qed.

(* This property is currently unused. *)

Goal (* use_into_union_left *)
  ∀ vs1 vs2 ws,
  into (vs1 ∪ vs2) ws →
  into vs1 ws ∧
  into vs2 ws.
Proof. set_solver. Qed.

(* -------------------------------------------------------------------------- *)

(* Properties of [closed]. *)

(* The empty set is closed. *)

Goal closed ∅.
Proof. set_solver. Qed.

(* A set whose image is empty is closed. *)

Goal ∀ vs, image vs ⊆ ∅ → closed vs.
Proof. set_solver. Qed.

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

End Relations.

Local Hint Rewrite
  @elem_of_image
: sets.

(* -------------------------------------------------------------------------- *)

(* Repeat the notations defined in the above section. *)

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

(* A type of elements. *)

Variable V : Type.

(* Two relations. *)

Variable E1 E2 : V → V → Prop.

(* We assume that [E2] contains [E1]. *)

Variable subrel :
  ∀ v w, E1 v w → E2 v w.

Lemma image_covariant_E vs : image E1 vs ⊆ image E2 vs.
Proof. set_solver. Qed.

Lemma into_contravariant_E vs ws : into E2 vs ws → into E1 vs ws.
Proof. set_solver. Qed.

End VarianceWithRespectToE.

(* -------------------------------------------------------------------------- *)

(* Create a hint database. *)

(* TODO *)
Hint Resolve
image_covariant
prove_image_empty
image_increasing
image_covariant_E
prove_into_union_left
: myrelations.

(* -------------------------------------------------------------------------- *)

(* In this section, we again fix a relation [E], and define paths,
   closedness, and closure. *)

Section PathsAndClosure.

(* A type of elements, or vertices. *)

Variable V : Type.

(* A successor (or edge) relation. *)

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

(* Being closed under edges is equivalent to being closed under paths.
   This is stated by the following two lemmas. *)

(* TODO prove that [path . path = path] *)

Lemma closed_path_closed_E vs :
  closed path vs →
  closed E vs.
Proof.
  intros. eapply into_contravariant_E; [ | eauto ]. eauto with path.
Qed.

Lemma closed_E_closed_path vs :
  closed E vs →
  closed path vs.
Proof.
  intros.
  eapply prove_subset; intros.
  sets. unpack.
  match goal with h: path _ _ |- _ => induction h end;
  eauto using use_closed.
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
Proof. set_solver. Qed.

(* A closure is closed. *)

Lemma closed_closure vs :
  closed path (closure vs).
Proof.
  eauto using image_idempotent_1 with path.
Qed.

(* If a closed set [ws] contains [vs],
   then it also contains [closure vs]. *)

Lemma prove_subset_closure vs ws :
  vs ⊆ ws →
  closed path ws →
  closure vs ⊆ ws.
Proof. set_solver. Qed.

(* The image of [vs] is a subset of its closure. *)

Lemma prove_subset_image_closure vs :
  image E vs ⊆ closure vs.
Proof.
  eauto using image_covariant_E with path.
Qed.

(* The above lemma can also be read as: a set reaches its own image. *)
Goal ∀ vs, reaches vs (image E vs).
Proof.
  exact prove_subset_image_closure.
Qed.

(* The relation [reaches] is transitive. *)

Lemma reaches_transitive:
  ∀ xs ys zs,
  reaches xs ys →
  reaches ys zs →
  reaches xs zs.
Proof.
  intros.
  etransitivity; [ eauto |].
  eapply prove_subset_image_left; [ eauto | ].
  eapply closed_closure.
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

(* A larger source set reaches at least as much as a smaller one. *)

Lemma reaches_contravariant vs1 vs2 ws :
  reaches vs1 ws → vs1 ⊆ vs2 → reaches vs2 ws.
Proof. set_solver. Qed.

Goal
  ∀ vs ws1 ws2,
  reaches vs ws1 →
  ws2 ⊆ ws1 →
  reaches vs ws2.
Proof. set_solver. Qed.

Goal
  ∀ vs ws1 ws2,
  reaches vs ws1 →
  reaches vs ws2 →
  reaches vs (ws1 ∪ ws2).
Proof. set_solver. Qed.

(* The singleton [v] reaches the singleton [w] if and only if there
   is a path of [v] to [w]. This is stated by the following two lemmas. *)

Lemma reaches_singleton_singleton v w :
  reaches {[v]} {[w]} ↔ path v w.
Proof. set_solver. Qed.

Lemma prove_reaches_singleton_singleton v w :
  path v w → reaches {[v]} {[w]}.
Proof. set_solver. Qed.

Lemma use_reaches_singleton_singleton v w :
  reaches {[v]} {[w]} →
  path v w.
Proof. set_solver. Qed.

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
  path v w /\ path w v.

(* The strongly connected component of [v]. *)

Definition component v :=
  {[ w | scc v w ]}.

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
   of the singleton [v]. *)

Lemma prove_subset_scc_closure v :
  component v ⊆ closure {[v]}.
Proof.
  unfold component.
  eapply prove_subset; intros.
  sets.
  exists v. split; [ set_solver |].
  eauto using use_scc_left.
Qed.

End PathsAndClosure.

(* -------------------------------------------------------------------------- *)

(* Repeat the notations defined above. *)

Notation closure E vs :=
  (image (path E) vs).

Notation reaches E vs ws :=
  (ws ⊆ closure E vs).

(* -------------------------------------------------------------------------- *)

(* Define hint databases. *)

Hint Constructors path : path.

Hint Resolve
  path_transitive
  use_scc_left
  use_scc_right
: path.

Hint Resolve
  scc_reflexive
  scc_symmetric
  scc_transitive
: scc.

Hint Resolve
  reaches_reflexive
  prove_subset_empty_left
  prove_subset_union_left
  prove_subset_image_closure
: reaches.

Hint Unfold scc : scc.

Hint Resolve
  closed_path_closed_E
  closed_E_closed_path
: closed.

(* -------------------------------------------------------------------------- *)

Section MoreVarianceWithRespectToE.

(* A type of elements. *)

Variable V : Type.

(* Two relations. *)

Variable E1 E2 : V → V → Prop.

(* We assume that [E2] contains [E1]. *)

Variable subrel :
  ∀ v w, E1 v w → E2 v w.

Lemma path_covariant_E v w :
  path E1 v w → path E2 v w.
Proof.
  induction 1; eauto with path.
Qed.

Lemma component_covariant_E v :
  component E1 v ⊆ component E2 v.
Proof.
  eapply prove_subset. intros w.
  unfold component. sets.
  unfold scc. intuition auto using path_covariant_E.
Qed.

End MoreVarianceWithRespectToE.

(* -------------------------------------------------------------------------- *)

(* We now prove properties that involve both [E] and [flip E]. *)

Section Reverse.

(* A type of elements, or vertices. *)

Variable V : Type.

(* A successor (or edge) relation. *)

Variable E : V → V → Prop.

(* [path] and [reverse] commute. *)

Lemma prove_path_reverse v w :
  path E v w →
  path (flip E) w v.
Proof.
  induction 1; eauto with path.
Qed.

Lemma use_path_reverse v w :
  path (flip E) w v →
  path E v w.
Proof.
  induction 1; eauto with path.
Qed.

Lemma path_reverse v w :
  flip (path E) v w ↔ path (flip E) v w.
Proof.
  split.
  + eauto using prove_path_reverse.
  + unfold flip. eauto using use_path_reverse.
Qed.

(* Reverse is involutive. *)

Lemma reverse_involutive v w :
  flip (flip E) v w ↔ E v w.
Proof.
  unfold flip. tauto.
Qed.

(* The strongly connected components are the same with respect to [E]
   and with respect to [flip E]. *)

Lemma scc_reverse v w :
  scc (flip E) v w ↔ scc E v w.
Proof.
  unfold scc. rewrite <- !path_reverse. unfold flip. tauto.
Qed.

Lemma component_reverse v:
  component (flip E) v ≡ component E v.
Proof.
  unfold component.
  eapply prove_equiv. intro w.
  sets.
  eapply scc_reverse.
Qed.

(* As a corollary, the strongly connected component of [v] is a subset
   of both the closure of [v] w.r.t. [E] and the closure of [v] w.r.t.
   [flip E]. *)

Lemma prove_subset_scc_reverse_closure v :
  component E v ⊆ closure (flip E) {[v]}.
Proof.
  intros.
  rewrite <- component_reverse.
  eapply prove_subset_scc_closure.
Qed.

(* In fact, it is exactly the intersection of these two sets. *)

Lemma prove_subset_intersection_scc v :
  closure E {[v]} ∩ closure (flip E) {[v]} ⊆ component E v.
Proof.
  intros.
  eapply prove_subset; intros w.
  rewrite elem_of_intersection. intros (? & ?).
  unfold component. autorewrite with sets.
  rewrite !elem_of_image_singleton in *.
  eauto using use_path_reverse with scc.
Qed.

(* If [vs] is closed under successor, then its complement is closed
   under predecessor. *)

Lemma prove_closed_complement vs :
  closed E vs →
  closed (flip E) (⊤ ∖ vs).
Proof. set_solver. (* wow *) Qed.

End Reverse.

Lemma prove_closed_path_complement {V} (E : V → V → Prop) vs :
  closed (path E) vs →
  closed (path (flip E)) (⊤ ∖ vs).
Proof.
  intros.
  eapply prove_closed_complement.
  eapply into_contravariant_E; [| eassumption].
  eauto using use_path_reverse.
Qed.
