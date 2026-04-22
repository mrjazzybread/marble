(* This library defines some vocabulary about relations. We begin with the
   idea of the image of a set under a relation: [image], [into], [closed].
   We continue with the idea of paths and reflexive-transitive closure:
   [path], [closure], [reaches]. Then, we introduce the reverse of a
   relation: [reverse], and the intersection of a relation and its reverse:
   [scc]. *)

Set Implicit Arguments.
From marble.logic Require Import MySets.

(* ---------------------------------------------------------------------------- *)

(* In this section, we fix a relation [E]. *)

Section Relations.

  (* A type of elements. *)
  Variable V : Type.

  (* A relation. *)
  Variable E : V -> V -> Prop.

  (* The image of a set under a relation. *)
  Definition image (vs : set V) : set V :=
    fun w => exists v, member v vs /\ E v w.

  (* The predicate [into vs ws] means that the image of the set [vs]
     under the successor relation lies in the set [ws]. *)
  Notation into vs ws :=
    (subset (image vs) ws).

  (* Symmetrically, [outof vs ws] means that the image of [vs] contains [ws]. *)
  Notation outof vs ws :=
    (subset ws (image vs)).

  (* The predicate [closed vs] means that set [vs] is closed under
     successor. *)
  Notation closed vs :=
    (into vs vs).

(* ---------------------------------------------------------------------------- *)

  (* Properties of [image]. *)

  (* This lemma proves membership in an image. *)
  Lemma prove_member_image:
    forall v vs w,
    member v vs ->
    E v w ->
    member w (image vs).
  Proof.
    unfold image. mysets.
  Qed.

  (* We do not define a lemma [use_member_image], because it would almost
     always be used in a forward manner, and that would not be very
     convenient. Instead, we directly define a tactic. *)

  Ltac use_member_image_k k :=
    match goal with
    | h: member _ (image _) |- _ =>
        generalize (use_member h); clear h; intros [ ? [ ? ? ]]
    | _ =>
        k tt
    end.

  Ltac use_member_image :=
    repeat (use_member_image_k idtac).

  (* The larger the set, the larger its image. *)
  Lemma image_covariant:
    forall vs ws,
    subset vs ws ->
    subset (image vs) (image ws).
  Proof.
    intros.
    eapply prove_subset; intros.
    use_member_image.
    eauto using prove_member_image with st mysets.
  Qed.

  (* The image of a union is the union of the images. This is stated
     by the following two lemmas. *)
  Lemma prove_subset_image_union_left:
    forall vs1 vs2,
    subset
      (image (union vs1 vs2))
      (union (image vs1) (image vs2)).
  Proof.
    intros.
    eapply prove_subset; intros.
    use_member_image.
    use_member_union;
    eauto using prove_member_image with mysets.
  Qed.

  Lemma prove_subset_image_union_right:
    forall vs1 vs2,
    subset
      (union (image vs1) (image vs2))
      (image (union vs1 vs2)).
  Proof.
    intros.
    eapply prove_subset_union_left;
    eapply prove_subset;
    eauto using image_covariant with st mysets.
  Qed.

  (* The image of the empty set is empty. *)
  Lemma prove_image_empty:
    forall vs,
    subset (image empty_) vs.
  Proof.
    intros.
    eapply prove_subset; intros.
    use_member_image.
    exfalso. mysets.
  Qed.

  (* If [E] is reflexive, then [image] is increasing. *)
  Lemma image_increasing:
    reflexive E ->
    forall vs,
    subset vs (image vs).
  Proof.
    eauto using prove_subset, prove_member_image.
  Qed.

  (* If [E] is transitive, then [image] is idempotent (one way). *)
  Lemma image_idempotent_1:
    transitive E ->
    forall vs,
    subset (image (image vs)) (image vs).
  Proof.
    intros. eapply prove_subset; intros.
    use_member_image.
    eauto using prove_member_image.
  Qed.

  (* If [E] is reflexive, then [image] is idempotent (the other way). *)
  Lemma image_idempotent_2:
    reflexive E ->
    forall vs,
    subset (image vs) (image (image vs)).
  Proof.
    eauto using image_covariant, image_increasing.
  Qed.

  (* This lemma exploits membership in an image. *)
  Lemma use_member_image_singleton:
    forall v w,
    member w (image (singleton v)) ->
    E v w.
  Proof.
    intros. use_member_image. simplify_sets. assumption.
  Qed.

(* ---------------------------------------------------------------------------- *)

  (* Properties of [into]. *)

  (* [into vs ws] is contravariant in [vs]. *)
  Lemma into_contravariant:
    forall vs1 vs2 ws,
    into vs1 ws ->
    subset vs2 vs1 ->
    into vs2 ws.
  Proof.
    eauto using image_covariant with st.
  Qed.

  (* [into vs ws] is covariant in [ws]. *)
  Goal
    forall vs ws1 ws2,
    into vs ws1 ->
    subset ws1 ws2 ->
    into vs ws2.
  Proof.
    eauto with st.
  Qed.

  (* Note that [prove_image_empty] proves [into empty_ vs]. *)
  Goal
    forall vs,
    into empty_ vs.
  Proof.
    eapply prove_image_empty.
  Qed.

  (* In order to prove that [image vs] is empty, one must establish
     that an element of [vs] has no successor. *)

  Lemma prove_into_empty:
    forall vs,
    (forall v w, member v vs -> ~ E v w) ->
    into vs empty_.
  Proof.
    unfold not. intros. eapply prove_subset; intros. exfalso. use_member_image. eauto.
  Qed.

  (* Union in the left-hand side of [into] can be decomposed. *)
  Lemma prove_into_union_left:
    forall vs1 vs2 ws,
    into vs1 ws ->
    into vs2 ws ->
    into (union vs1 vs2) ws.
  Proof.
    eauto using prove_subset_image_union_left with st mysets.
  Qed.

  (* This is a variant of the above lemma, where the union in the left-hand side
     is not explicitly apparent, but is created via [prove_subset_union_diff]. *)
  Lemma prove_into_union_diff:
    forall vs1 vs2 ws,
    into (diff vs1 vs2) ws ->
    into vs2 ws ->
    into vs1 ws.
  Proof.
    eauto using into_contravariant, prove_into_union_left, prove_subset_union_diff.
  Qed.

  (* This property is currently unused. *)
  Goal (* use_into_union_left *)
    forall vs1 vs2 ws,
    into (union vs1 vs2) ws ->
    into vs1 ws /\
    into vs2 ws.
  Proof.
    intros; split;
    eauto using prove_subset_image_union_right with st mysets.
  Qed.

(* ---------------------------------------------------------------------------- *)

  (* Properties of [closed]. *)

  (* The empty set is closed. *)
  Goal
    closed empty_.
  Proof.
    eapply prove_image_empty.
  Qed.

  (* A set whose image is empty is closed. *)
  Goal
    forall vs,
    subset (image vs) empty_ ->
    closed vs.
  Proof.
    eauto with st mysets.
  Qed.

  (* An edge cannot leave a closed set. *)
  Lemma use_closed:
    forall vs,
    closed vs ->
    forall v w,
    E v w ->
    member v vs ->
    member w vs.
  Proof.
    eauto using prove_member_image with st.
  Qed.

  (* If [rs] is a subset of [vs] and [vs] is closed, then [image rs]
     is also a subset of [vs]. *)
  Lemma prove_subset_image_left:
    forall rs vs,
    subset rs vs ->
    closed vs ->
    subset (image rs) vs.
  Proof.
    eauto using image_covariant with st.
  Qed.

  (* The union of two closed sets is closed. *)
  Lemma prove_closed_union:
    forall vs ws,
    closed vs ->
    closed ws ->
    closed (union vs ws).
  Proof.
    intros. eapply prove_into_union_left; eauto with st mysets.
  Qed.

End Relations.

(* ---------------------------------------------------------------------------- *)

(* Repeat the notations and tactics defined in the above section. *)

Ltac use_member_image_k k :=
  match goal with
  | h: member _ (image _ _) |- _ => (* note: [image] now has two parameters *)
      generalize (use_member h); clear h; intros [ ? [ ? ? ]]
  | _ =>
      k tt
  end.

Ltac use_member_image :=
  repeat (use_member_image_k idtac).

Notation into E vs ws :=
  (subset (image E vs) ws).

Notation outof E vs ws :=
  (subset ws (image E vs)).

Notation closed E vs :=
  (into E vs vs).

(* ---------------------------------------------------------------------------- *)

(* Define more tactics. *)

(* This tactic applies [use_member_image_singleton] in a forward manner. *)
Ltac use_member_image_singleton_k k :=
  match goal with
  | h: member ?w (image _ (singleton _)) |- _ =>
      generalize (use_member_image_singleton h); clear h; intro; try (subst w)
  | _ =>
      k tt
  end.

(* ---------------------------------------------------------------------------- *)

(* We now consider two relations [E1] and [E2] and examine how [image], [into],
   and [closed] behave when one moves from one relation to another. *)

Section VarianceWithRespectToE.

  (* A type of elements. *)
  Variable V : Type.

  (* Two relations. *)
  Variable E1 E2 : V -> V -> Prop.

  (* We assume that [E2] contains [E1]. *)
  Variable subrel :
    forall v w, E1 v w -> E2 v w.

  Lemma image_covariant_E:
    forall vs : set V,
    subset (image E1 vs) (image E2 vs).
  Proof.
    intros. eapply prove_subset; intros.
    use_member_image.
    eauto using prove_member_image.
  Qed.

  Lemma into_contravariant_E:
    forall vs ws,
    into E2 vs ws ->
    into E1 vs ws.
  Proof.
    eauto using subset_transitive, image_covariant_E.
  Qed.

  Goal
    forall vs,
    closed E2 vs ->
    closed E1 vs.
  Proof.
    eauto using into_contravariant_E.
  Qed.

End VarianceWithRespectToE.

(* ---------------------------------------------------------------------------- *)

(* Create a hint database. *)

Hint Resolve
image_covariant
prove_image_empty
image_increasing
image_covariant_E
prove_into_union_left
: myrelations.

(* ---------------------------------------------------------------------------- *)

(* In this section, we again fix a relation [E], and define paths, closedness,
   and closure. *)

Section PathsAndClosure.

  (* A type of elements, or vertices. *)
  Variable V : Type.

  (* A successor (or edge) relation. *)
  Variable E : V -> V -> Prop.

(* ---------------------------------------------------------------------------- *)

  (* Paths. *)

  (* A path in the graph. *)
  (* This is the reflexive-transitive closure of the relation [E]. *)
  Inductive path : V -> V -> Prop :=
  | PathNil:
      forall x,
      path x x
  | PathCons:
      forall x y z,
      E x y ->
      path y z ->
      path x z.

  Hint Constructors path : path.

  Goal
    reflexive path.
  Proof.
    eauto with path.
  Qed.

  Lemma path_transitive:
    transitive path.
  Proof.
    induction 1; eauto with path.
  Qed.

  Hint Resolve path_transitive : path.

  (* Being closed under edges is equivalent to being closed under paths.
     This is stated by the following two lemmas. *)
  Lemma closed_path_closed_E:
    forall vs,
    closed path vs ->
    closed E vs.
  Proof.
    intros. eapply into_contravariant_E; [ | eauto ]. eauto with path.
  Qed.

  Lemma closed_E_closed_path:
    forall vs,
    closed E vs ->
    closed path vs.
  Proof.
    intros. eapply prove_subset; intros.
    use_member_image.
    match goal with h: path _ _ |- _ => induction h end;
    eauto using use_closed.
  Qed.

(* ---------------------------------------------------------------------------- *)

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
    (subset ws (closure vs)).

  (* The relation [reaches] is reflexive. *)
  Lemma reaches_reflexive:
    forall vs,
    reaches vs vs.
  Proof.
    eauto with path myrelations.
  Qed.

  (* Every set reaches its closure. *)
  Goal
    forall vs,
    reaches vs (closure vs).
  Proof.
    intros. eapply subset_reflexive.
  Qed.

  (* A closure is closed. *)
  Lemma closed_closure:
    forall vs,
    closed path (closure vs).
  Proof.
    eauto using image_idempotent_1 with path.
  Qed.

  (* If a closed set [ws] contains [vs], then it also contains [closure vs]. *)
  Lemma prove_subset_closure:
    forall vs ws,
    subset vs ws ->
    closed path ws ->
    subset (closure vs) ws.
  Proof.
    eauto with st myrelations.
  Qed.

  (* The image of [vs] is a subset of its closure. *)
  Lemma prove_subset_image_closure:
    forall vs,
    subset (image E vs) (closure vs).
  Proof.
    eauto with myrelations path.
  Qed.

  (* The above lemma can also be read as: a set reaches its own image. *)
  Goal
    forall vs,
    reaches vs (image E vs).
  Proof.
    exact prove_subset_image_closure.
  Qed.

  (* The relation [reaches] is transitive. *)
  Lemma reaches_transitive:
    forall xs ys zs,
    reaches xs ys ->
    reaches ys zs ->
    reaches xs zs.
  Proof.
    intros.
    eapply subset_transitive; [ eauto | ].
    eapply prove_subset_image_left; [ eauto | ].
    eapply closed_closure.
  Qed.

  (* Every set reaches the empty set. *)
  Goal
    forall vs,
    reaches vs empty_.
  Proof.
    intros. eapply prove_subset_empty_left.
  Qed.

  (* Every set reaches itself (and every subset of itself). *)
  Lemma prove_reaches_self:
    forall vs ws,
    subset ws vs ->
    reaches vs ws.
  Proof.
    eauto with st myrelations path.
  Qed.

  (* A larger source set reaches at least as much as a smaller one. *)
  Lemma reaches_contravariant:
    forall vs1 vs2 ws,
    reaches vs1 ws ->
    subset vs1 vs2 ->
    reaches vs2 ws.
  Proof.
    eauto with st myrelations.
  Qed.

  Goal
    forall vs ws1 ws2,
    reaches vs ws1 ->
    subset ws2 ws1 ->
    reaches vs ws2.
  Proof.
    eauto with st.
  Qed.

  Goal
    forall vs ws1 ws2,
    reaches vs ws1 ->
    reaches vs ws2 ->
    reaches vs (union ws1 ws2).
  Proof.
    eauto with mysets.
  Qed.

  (* The singleton [v] reaches the singleton [w] if and only if there
     is a path of [v] to [w]. This is stated by the following two lemmas. *)
  Lemma prove_reaches_singleton_singleton:
    forall v w,
    path v w ->
    reaches (singleton v) (singleton w).
  Proof.
    intros.
    eapply prove_member.
    exists v. eauto with mysets.
  Qed.

  Lemma use_reaches_singleton_singleton:
    forall v w,
    reaches (singleton v) (singleton w) ->
    path v w.
  Proof.
    intros.
    use_member_image_singleton_k idtac.
    assumption.
  Qed.

  (* The following two lemmas are special cases of [reaches_contravariant]. *)
  Lemma prove_reaches_union_left_1:
    forall vs1 vs2 ws,
    reaches vs1 ws ->
    reaches (union vs1 vs2) ws.
  Proof.
    eauto using reaches_contravariant, prove_subset_union_right_1, subset_reflexive.
  Qed.

  Lemma prove_reaches_union_left_2:
    forall vs1 vs2 ws,
    reaches vs2 ws ->
    reaches (union vs1 vs2) ws.
  Proof.
    eauto using reaches_contravariant, prove_subset_union_right_2, subset_reflexive.
  Qed.

(* ---------------------------------------------------------------------------- *)

  (* The reverse of the relation [E]. *)

  Definition reverse v w :=
    E w v.

  (* The relation [scc] is the intersection of [path E] and its reverse. Less
     abstractly put, [scc v w] holds if and only if there is a path from
     [v] to [w] and back. *)

  Definition scc v w :=
    path v w /\ path w v.

  (* [scc] is an equivalence relation. *)
  Lemma scc_reflexive:
    reflexive scc.
  Proof.
    unfold scc. eauto with path.
  Qed.

  Lemma scc_symmetric:
    symmetric scc.
  Proof.
    unfold scc. intuition eauto.
  Qed.

  Lemma scc_transitive:
    transitive scc.
  Proof.
    unfold scc. intuition eauto with path.
  Qed.

  (* The following two lemmas unfold the definition of [scc]. *)
  Lemma use_scc_left:
    forall v w,
    scc v w ->
    path v w.
  Proof.
    inversion 1; auto.
  Qed.

  Lemma use_scc_right:
    forall v w,
    scc v w ->
    path w v.
  Proof.
    inversion 1; auto.
  Qed.

  (* The strongly connected component of [v] is a subset of the closure
     of the singleton [v]. *)
  Lemma prove_subset_scc_closure:
    forall v,
    subset
      (scc v)
      (closure (singleton v)).
  Proof.
    intros.
    eapply prove_subset; intros.
    eapply prove_member_image; [ eapply subset_reflexive | ].
    eapply use_scc_left.
    eapply use_member; eauto.
  Qed.

End PathsAndClosure.

(* ---------------------------------------------------------------------------- *)

(* Repeat the notations defined above. *)

Notation closure E vs :=
  (image (path E) vs).

Notation reaches E vs ws :=
  (subset ws (closure E vs)).

(* ---------------------------------------------------------------------------- *)

(* Define hint databases. *)

Hint Constructors path : path.

Hint Resolve path_transitive use_scc_left use_scc_right : path.

Hint Resolve scc_reflexive scc_symmetric scc_transitive : scc.

Hint Resolve reaches_reflexive prove_subset_empty_left
prove_subset_union_left prove_subset_image_closure : reaches.

Hint Unfold scc : scc.

Hint Resolve closed_path_closed_E closed_E_closed_path : closed.

(* ---------------------------------------------------------------------------- *)

Section MoreVarianceWithRespectToE.

  (* A type of elements. *)
  Variable V : Type.

  (* Two relations. *)
  Variable E1 E2 : V -> V -> Prop.

  (* We assume that [E2] contains [E1]. *)
  Variable subrel :
    forall v w, E1 v w -> E2 v w.

  Lemma path_covariant_E:
    forall v w,
    path E1 v w ->
    path E2 v w.
  Proof.
    induction 1; eauto with path.
  Qed.

  Lemma scc_covariant_E:
    forall v,
    subset (scc E1 v) (scc E2 v).
  Proof.
    unfold scc. intros. eapply prove_subset_directly. intuition auto using path_covariant_E.
  Qed.

End MoreVarianceWithRespectToE.

(* ---------------------------------------------------------------------------- *)

(* We now prove properties that involve both [E] and [reverse E], whence the
   need to open a new section. *)

Section Reverse.

  (* A type of elements, or vertices. *)
  Variable V : Type.

  (* A successor (or edge) relation. *)
  Variable E : V -> V -> Prop.

  (* [path] and [reverse] commute. *)
  Lemma prove_path_reverse:
    forall v w,
    path E v w ->
    path (reverse E) w v.
  Proof.
    induction 1; eauto with path.
  Qed.

  Lemma use_path_reverse:
    forall v w,
    path (reverse E) w v ->
    path E v w.
  Proof.
    induction 1; eauto with path.
  Qed.

  Lemma path_reverse:
    reverse (path E) = path (reverse E).
  Proof.
    extensionality v. extensionality w.
    apply prop_ext; split; intros.
    eauto using prove_path_reverse.
    unfold reverse. eauto using use_path_reverse.
  Qed.

  (* Reverse is involutive. *)
  Lemma reverse_involutive:
    reverse (reverse E) = E.
  Proof.
    unfold reverse.
    extensionality v. extensionality w.
    apply prop_ext. tauto.
  Qed.

  (* The strongly connected components are the same with respect to [E]
     and with respect to [reverse E]. *)
  Lemma scc_reverse:
    scc (reverse E) = scc E.
  Proof.
    unfold scc.
    extensionality v. extensionality w.
    apply prop_ext.
    intuition eauto using use_path_reverse, prove_path_reverse.
  Qed.

  (* As a corollary, the strongly connected component of [v] is a subset
     of both the closure of [v] w.r.t. [E] and the closure of [v] w.r.t.
     [reverse E]. *)
  Lemma prove_subset_scc_reverse_closure:
    forall v,
    subset
      (scc E v)
      (closure (reverse E) (singleton v)).
  Proof.
    intros.
    rewrite <- scc_reverse.
    eapply prove_subset_scc_closure.
  Qed.

  (* In fact, it is exactly the intersection of these two sets. *)
  Lemma prove_subset_intersection_scc:
    forall v,
    subset
      (intersection
        (closure E (singleton v))
        (closure (reverse E) (singleton v))
      )
      (scc E v).
  Proof.
    intros. eapply prove_subset; intros. simplify_sets. eapply prove_member.
    eauto 6 using use_reaches_singleton_singleton, use_path_reverse with scc.
  Qed.

  (* If [vs] is closed under successor, then its complement is closed
     under predecessor. *)
  Lemma prove_closed_complement:
    forall vs,
    closed E vs ->
    closed (reverse E) (complement vs).
  Proof.
    intros ? hcvs. eapply prove_subset; intros v ?. use_member_image.
    eapply prove_member_complement. intro hv.
    match goal with h: member ?x (complement ?vs) |- _ =>
      assert (member x vs); [ eauto using use_closed | ]
    end.
    mysets.
  Qed.

End Reverse.

Lemma prove_closed_path_complement:
  forall (V : Type) (E : V -> V -> Prop),
  forall vs,
  closed (path E) vs ->
  closed (path (reverse E)) (complement vs).
Proof.
  intros. rewrite <- path_reverse. eauto using prove_closed_complement.
Qed.

(* ---------------------------------------------------------------------------- *)

(* Update the tactic [simplify_sets] by composing all of the forward tactics
   introduced so far. *)

Ltac simplify_sets ::=
  repeat (
    simplify_sets_k ltac:(fun _ =>
    use_member_image_singleton_k ltac:(fun _ =>
    use_member_image_k ltac:(fun _ =>
    idtac)))).
