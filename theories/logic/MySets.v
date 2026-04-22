(* This library offers an encoding of (finite or infinite) sets as
   characteristic predicates, that is, as functions of type [V -> Prop],
   where [V] is the type of the elements. There is nothing deep in it.
   Nevertheless, it is very useful, because it allows one to work in
   the ``point-free'' style of set theory. *)

Set Implicit Arguments.
(* The axiom [classic] is used in only one lemma, where we wish to
   prove that an element lies either inside or outside of a subset. *)
From Stdlib Require Export Classical.
(* Functional extensionality and propositional extensionality are
   used in order to establish that the subset relation is antisymmetric.
   This saves us the trouble of working with an equivalence relation
   over sets. *)
From Stdlib Require Export Logic.FunctionalExtensionality.
From Stdlib Require Import ClassicalFacts.
Axiom prop_ext: prop_extensionality.
From Stdlib Require Import Lia.
From Stdlib Require Import Wellfounded.Inclusion.
From Stdlib Require Import Wf_nat.
From marble.logic Require Import MyWf.
(* For rewriting. *)
From Stdlib Require Import Program.Basics. (* [flip], [impl] *)
From Stdlib Require Export Setoids.Setoid. (* required for [rewrite] *)
From Stdlib Require Export Classes.Morphisms.

(* ---------------------------------------------------------------------------- *)

(* Abbreviations for the most common properties of relations. *)

(* These notions are also defined in [Coq.Relations.Relation_Definitions].
   However, notations seem to be preferable to definitions, as definitions
   are not properly unfolded during proof search. *)

(* Reflexivity. *)
Notation reflexive E := (forall v, E v v).

(* Symmetry. *)
Notation symmetric E := (forall v w, E v w -> E w v).

(* Transitivity. *)
Notation transitive E := (forall v w x, E v w -> E w x -> E v x).

(* ---------------------------------------------------------------------------- *)

(* An encoding of (finite or infinite) sets as characteristic predicates. *)

(* This encoding has a few fairly pleasing properties: 1- it is concise and
   natural; 2- by expanding away all definitions, a statement about sets is
   translated to a formula which [intuition eauto] can often prove. This is
   the tactic [mysets]. *)

Section Sets.

  (* A type of elements. *)
  Variable V : Type.

  (* A set is encoded as a characteristic predicate. *)
  Definition set :=
    V -> Prop.

  (* The empty set. *)
  Definition empty : set :=
    fun v => False.

  (* Singleton. *)
  Definition singleton w : set :=
    fun v => v = w.

  (* Union. *)
  Definition union (vs ws : set) : set :=
    fun v => vs v \/ ws v.

  (* Intersection. *)
  Definition intersection (vs ws : set) : set :=
    fun v => vs v /\ ws v.

  (* Complement. *)
  Definition complement (vs : set) : set :=
    fun v => ~ vs v.

  (* Difference. *)
  Notation diff vs ws :=
    (intersection vs (complement ws)).

  (* The subset relation. *)
  Definition subset (vs ws : set) :=
    forall v, vs v -> ws v.

  Definition strict_subset vs ws :=
    subset vs ws /\ ~ subset ws vs.

  Definition strict_superset vs ws :=
    strict_subset ws vs.

  (* Membership could be defined directly as [vs v], but is defined here
     in terms of [subset], so as to reduce the number of notions and make
     our lemmas about [subset] more easily applicable. *)
  Notation member v vs :=
    (subset (singleton v) vs).

  (* The universe. *)
  Definition universe : set :=
    fun v => True.

  (* The following tactic is (hopefully) very powerful. *)
  Ltac mysets := unfold universe, strict_superset, strict_subset,
    subset, complement, intersection, union, singleton, empty in *;
    try solve [ intros; tauto | eauto | intuition (subst; eauto) ].

(* ---------------------------------------------------------------------------- *)

  (* The following lemmas are not part of the hint database. *)

  (* This lemma eliminates [member]. *)
  Lemma use_member:
    forall vs v,
    member v vs ->
    vs v.
  Proof.
    mysets.
  Qed.

  (* This lemma introduces [member]. *)
  Lemma prove_member:
    forall (vs : set) v,
    vs v ->
    member v vs.
  Proof.
    mysets.
  Qed.

  (* This lemma introduces [subset] directly, without going through [member]. *)
  Lemma prove_subset_directly:
    forall vs ws : set,
    (forall v, vs v -> ws v) ->
    subset vs ws.
  Proof.
    mysets.
  Qed.

  (* This lemma introduces [subset]. *)
  Lemma prove_subset:
    forall vs ws : set,
    (forall v, member v vs -> member v ws) ->
    subset vs ws.
  Proof.
    intros. eapply prove_subset_directly.
    intros. eapply use_member.
    eauto using prove_member.
  Qed.

  (* Set inclusion is transitive. *)
  Lemma subset_transitive:
    forall vs ws xs : set,
    subset vs ws ->
    subset ws xs ->
    subset vs xs.
  Proof.
    mysets.
  Qed.

  (* Thanks to our definition of [member] as a notation, the above lemma
     also proves the following. *)
  Goal
    forall v vs ws,
    member v vs ->
    subset vs ws ->
    member v ws.
  Proof.
    eauto using subset_transitive.
  Qed.

  (* This lemma is the contrapositive of the above assertion. *)
  Lemma prove_not_member_via_subset:
    forall v vs ws,
    ~ member v vs ->
    subset ws vs ->
    ~ member v ws.
  Proof.
    mysets.
  Qed.

  (* This lemma reverses a disjointness assertion expressed in terms
     of [subset] and [complement]. It can be interpreted as the symmetry
     of disjointness. *)
  Lemma contrapose_subset_complement_right:
    forall vs ws,
    subset vs (complement ws) ->
    subset ws (complement vs).
  Proof.
    mysets.
  Qed.

  Lemma contrapose_subset_complement_left:
    forall vs ws,
    subset (complement vs) ws ->
    subset (complement ws) vs.
  Proof.
    intros ? ? h v. generalize (h v). mysets.
  Qed.

  (* This lemma exploits the fact that an element is a member of a union. *)
  Lemma use_member_union:
    forall v vs1 vs2,
    member v (union vs1 vs2) ->
    member v vs1 \/ member v vs2.
  Proof.
    intros ? ? ? h. destruct (use_member h); mysets.
  Qed.

(* ---------------------------------------------------------------------------- *)

  (* The following lemmas are used in a forward manner as part of the
     tactic [simplify_sets]. *)

  (* This lemma exploits a [subset] assertion whose left-hand side is a union. *)
  Lemma use_subset_union_left:
    forall vs1 vs2 ws,
    subset (union vs1 vs2) ws ->
    subset vs1 ws /\
    subset vs2 ws.
  Proof.
    mysets.
  Qed.

  (* This lemma exploits a membership assertion whose argument is a complement. *)
  Lemma use_member_complement:
    forall v vs,
    member v (complement vs) ->
    ~ member v vs.
  Proof.
    mysets.
  Qed.

  (* This lemma exploits a membership assertion whose argument is a singleton. *)
  Lemma use_member_singleton:
    forall v w,
    member v (singleton w) ->
    v = w.
  Proof.
    mysets.
  Qed.

  (* This lemma exploits the fact that a set is a subset of an intersection. *)
  Lemma use_subset_intersection_right:
    forall vs vs1 vs2,
    subset vs (intersection vs1 vs2) ->
    subset vs vs1 /\ subset vs vs2.
  Proof.
    mysets.
    (* Why does [intuition eauto] fail? *)
    intros ? ? ? h. split; intros v ?; generalize (h v); intros [ ? ? ]; eauto.
  Qed.

(* ---------------------------------------------------------------------------- *)

  (* The following lemmas are part of the hint database. *)

  (* Set inclusion is reflexive. *)
  Lemma subset_reflexive:
    forall vs : set,
    subset vs vs.
  Proof.
    mysets.
  Qed.

  (* Thanks to our definition of [member] as a notation, the above lemma
     lemma also proves the following. *)
  Goal
    forall v,
    member v (singleton v).
  Proof.
    eauto using subset_reflexive.
  Qed.

  (* The empty set is a subset of every set. *)
  Lemma prove_subset_empty_left:
    forall vs,
    subset empty vs.
  Proof.
    mysets.
  Qed.

  (* The following two lemmas prove a [subset] assertion whose right-hand
     side is a union, in the easy case where the left-hand side is a subset
     of one of the members of the union. Note that we could also state just
     [subset vs (union vs ws2)], and rely on transitivity. This seems better,
     as it should often allow us to save an explicit use of transitivity. We
     can still prove [subset vs (union vs ws2)] by relying on reflexivity. *)
  Lemma prove_subset_union_right_1:
    forall vs ws1 ws2,
    subset vs ws1 ->
    subset vs (union ws1 ws2).
  Proof.
    mysets.
  Qed.

  Lemma prove_subset_union_right_2:
    forall vs ws1 ws2,
    subset vs ws2 ->
    subset vs (union ws1 ws2).
  Proof.
    mysets.
  Qed.

  (* The following lemma proves a [subset] assertion whose left-hand side
     is a union. *)
  Lemma prove_subset_union_left:
    forall vs1 vs2 ws,
    subset vs1 ws ->
    subset vs2 ws ->
    subset (union vs1 vs2) ws.
  Proof.
    mysets.
  Qed.

  (* This lemma proves that some set is a subset of an intersection. *)
  Lemma prove_subset_intersection_right:
    forall vs vs1 vs2,
    subset vs vs1 ->
    subset vs vs2 ->
    subset vs (intersection vs1 vs2).
  Proof.
    mysets.
  Qed.

  (* The following lemma proves a [subset] assertion between two complements. *)
  Lemma prove_subset_complement:
    forall vs ws,
    subset vs ws ->
    subset (complement ws) (complement vs).
  Proof.
    mysets.
  Qed.

  (* The following lemma exploits a [subset] assertion between two complements. *)
  Lemma use_subset_complement:
    forall vs ws,
    subset (complement ws) (complement vs) ->
    subset vs ws.
  Proof.
    intros ? ? h v. generalize (h v). unfold complement. tauto.
  Qed.

  (* The following lemma proves a membership assertion whose right-hand
     side is a complement. *)
  Lemma prove_member_complement:
    forall v vs,
    ~ member v vs ->
    member v (complement vs).
  Proof.
    unfold subset, complement, singleton, not.
    intros ? ? h. intros. subst.
    eapply h. intros. subst.
    assumption.
  Qed.

  (* This lemma proves that an element is not a member of a union. *)
  Lemma prove_not_member_union:
    forall x vs ws,
    ~ member x vs ->
    ~ member x ws ->
    ~ member x (union vs ws).
  Proof.
    intros. intro h. destruct (use_member_union h); eauto.
  Qed.

  (* The next two lemmas prove that [intersection vs ws] is a subset
     of [vs] and of [ws]. *)
  Lemma prove_subset_intersection_left_1:
    forall vs ws,
    subset (intersection vs ws) vs.
  Proof.
    mysets.
  Qed.

  Lemma prove_subset_intersection_left_2:
    forall vs ws,
    subset (intersection vs ws) ws.
  Proof.
    mysets.
  Qed.

  (* The universe is universal. *)
  Lemma universal_universe:
    forall vs,
    subset vs universe.
  Proof.
    mysets.
  Qed.

  (* The following lemma proves a [subset] assertion between two [diff] expressions. *)
  Lemma prove_subset_diff:
    forall us vs ws,
    subset vs ws ->
    subset (diff us ws) (diff us vs).
  Proof.
    mysets.
  Qed.

(* ---------------------------------------------------------------------------- *)

  (* The following lemmas are (again) not part of the hint database. *)

  (* This lemma proves that an element of [vs] is either outside [ws]
     or in [ws]. *)
  Lemma prove_subset_union_diff:
    forall vs ws,
    subset vs (union (diff vs ws) ws).
  Proof.
    intros.
    eapply prove_subset; intros.
    destruct (classic (member v ws)).
    mysets.
    eapply prove_subset_union_right_1.
    eapply prove_subset_intersection_right.
    eauto.
    eapply prove_member_complement.
    eauto.
  Qed.

  (* This lemma proves that adding [ws] and taking it away produces
     a smaller set. *)
  Lemma prove_subset_diff_union:
    forall vs ws,
    subset (diff (union ws vs) ws) vs.
  Proof.
    mysets.
  Qed.

  Lemma prove_subset_by_narrowing:
    forall vs ws1 ws2,
    subset vs (union ws1 ws2) ->
    subset vs (complement ws1) ->
    subset vs ws2.
  Proof.
    eauto using prove_subset_diff_union, prove_subset_intersection_right,
      subset_transitive.
  Qed.

  (* Union is covariant. *)
  Lemma union_covariant:
    forall vs1 vs2 ws1 ws2,
    subset vs1 vs2 ->
    subset ws1 ws2 ->
    subset (union vs1 ws1) (union vs2 ws2).
  Proof.
    mysets.
  Qed.

  (* Intersection is covariant. *)
  Lemma intersection_covariant:
    forall vs1 vs2 ws1 ws2,
    subset vs1 vs2 ->
    subset ws1 ws2 ->
    subset (intersection vs1 ws1) (intersection vs2 ws2).
  Proof.
    mysets.
  Qed.

  (* This lemma establishes an upper bound for an intersection. *)
  Lemma prove_subset_intersection_left:
    forall vs1 vs vs2,
    subset vs2 (complement vs1) ->
    forall ws1 ws2,
    subset ws1 (union vs1 vs) ->
    subset ws2 (union vs vs2) ->
    subset (intersection ws1 ws2) vs.
  Proof.
    (* Ideally, a SAT solver would prove this... *)
    intros ? ? ? f ? ? f1 f2. eapply prove_subset. intros ? h.
    destruct (use_subset_intersection_right h) as [ h1 h2 ]. clear h.
    (* One step. *)
    destruct (use_member_union (subset_transitive h1 f1)); [ | mysets ].
    (* One symmetric step. *)
    destruct (use_member_union (subset_transitive h2 f2)); [ mysets | ].
    (* Contradiction. *)
    exfalso. mysets.
  Qed.

  (* If two sets are subsets of one another, then they are equal.
     We could work without this property, but it can be convenient. *)
  Lemma subset_antisymmetric:
    forall vs ws,
    subset vs ws ->
    subset ws vs ->
    vs = ws.
  Proof.
    unfold subset.
    intros. extensionality x.
    apply prop_ext. split; auto.
  Qed.

(* ---------------------------------------------------------------------------- *)

(* The following equalities are used as rewrite rules by [rewrite_sets]. *)

  (* [empty] is a neutral element for [union]. *)
  Lemma union_empty_left:
    forall vs,
    union empty vs = vs.
  Proof.
    intros. eapply subset_antisymmetric; mysets.
  Qed.

  Lemma union_empty_right:
    forall vs,
    union vs empty = vs.
  Proof.
    intros. eapply subset_antisymmetric; mysets.
  Qed.

  Lemma union_universe_left:
    forall vs,
    union universe vs = universe.
  Proof.
    intros. eapply subset_antisymmetric; mysets.
  Qed.

  Lemma union_universe_right:
    forall vs,
    union vs universe = universe.
  Proof.
    intros. eapply subset_antisymmetric; mysets.
  Qed.

  Lemma intersection_universe_left:
    forall vs,
    intersection universe vs = vs.
  Proof.
    intros. eapply subset_antisymmetric; mysets.
  Qed.

  Lemma intersection_universe_right:
    forall vs,
    intersection vs universe = vs.
  Proof.
    intros. eapply subset_antisymmetric; mysets.
  Qed.

  (* [empty] is an absorbing element for [intersection]. *)
  Lemma intersection_empty_left:
    forall vs,
    intersection empty vs = empty.
  Proof.
    intros. eapply subset_antisymmetric; mysets.
  Qed.

  Lemma intersection_empty_right:
    forall vs,
    intersection vs empty = empty.
  Proof.
    intros. eapply subset_antisymmetric; mysets.
  Qed.

  (* [diff universe] is [complement]. *)
  Lemma diff_universe:
    forall vs,
    diff universe vs = complement vs.
  Proof.
    intros. eapply subset_antisymmetric; mysets.
  Qed.

  (* The complement of the universe is the empty set. *)
  Lemma complement_universe:
    complement universe = empty.
  Proof.
    intros. eapply subset_antisymmetric; mysets.
  Qed.

  Lemma complement_empty:
    complement empty = universe.
  Proof.
    intros. eapply subset_antisymmetric; mysets.
  Qed.

  Lemma complement_union:
    forall vs ws,
    complement (union vs ws) = intersection (complement vs) (complement ws).
  Proof.
    intros. eapply subset_antisymmetric; mysets.
  Qed.

  Lemma complement_intersection:
    forall vs ws,
    complement (intersection vs ws) = union (complement vs) (complement ws).
  Proof.
    intros. eapply subset_antisymmetric; mysets.
  Qed.

  (* Complement is its own inverse. *)

  Lemma complement_complement:
    forall vs,
    complement (complement vs) = vs.
  Proof.
    intros. eapply subset_antisymmetric; mysets.
  Qed.

(* ---------------------------------------------------------------------------- *)

(* More equalities, NOT used by [rewrite_sets]. *)

  (* The complement of a difference is, etc. *)

  Lemma complement_diff:
    forall vs ws,
    complement (diff vs ws) = union (complement vs) ws.
  Proof.
    intros. eapply subset_antisymmetric; mysets.
  Qed.

  (* Union is associative. *)
  Lemma union_associative:
    forall xs ys zs,
    union xs (union ys zs) = union (union xs ys) zs.
  Proof.
    intros. eapply subset_antisymmetric; mysets.
  Qed.

  (* Intersection is associative. *)
  Lemma intersection_associative:
    forall xs ys zs,
    intersection xs (intersection ys zs) = intersection (intersection xs ys) zs.
  Proof.
    intros. eapply subset_antisymmetric; mysets.
  Qed.

  (* An intersection can be simplified when one operand contains the other. *)

  Lemma simplify_intersection_left:
    forall vs ws,
    subset vs ws ->
    intersection vs ws = vs.
  Proof.
    intros. eapply subset_antisymmetric; mysets.
  Qed.

  Lemma simplify_intersection_right:
    forall vs ws,
    subset ws vs ->
    intersection vs ws = ws.
  Proof.
    intros. eapply subset_antisymmetric; mysets.
  Qed.

  (* The following lemma exploits a [subset] assertion between two [diff] expressions. *)
  Lemma use_subset_diff:
    forall us vs ws,
    subset (diff us ws) (diff us vs) ->
    subset (intersection us vs) (intersection us ws).
  Proof.
    intros ? ? ? h1. eapply prove_subset. intros ? h2.
    destruct (use_subset_intersection_right h2) as [ h2a h2b ]. clear h2.
    eapply prove_subset_intersection_right.
    { eauto. }
    { destruct (classic (member v ws)); [ eauto | exfalso ].
      assert (h3: member v (diff us vs)). { eauto using subset_transitive, prove_subset_intersection_right, prove_member_complement. }
      destruct (use_subset_intersection_right h3) as [ h3a h3b ]. clear h3.
      mysets. }
  Qed.

  Lemma use_subset_diff_when_included:
    forall us vs ws,
    subset (diff us ws) (diff us vs) ->
    subset ws us ->
    subset vs us ->
    subset vs ws.
  Proof.
    intros ? ? ? h hws hvs.
    generalize (use_subset_diff h). intro hh.
    do 2 rewrite simplify_intersection_right in hh by eauto.
    assumption.
  Qed.

(* ---------------------------------------------------------------------------- *)

  (* The strict subset relation. *)

  Lemma prove_strict_subset:
    forall vs ws,
    subset vs ws ->
    forall w,
    member w ws ->
    ~ member w vs ->
    strict_subset vs ws.
  Proof.
    mysets.
  Qed.

  Lemma strict_subset_transitive_1:
    forall xs ys zs,
    strict_subset xs ys ->
    subset ys zs ->
    strict_subset xs zs.
  Proof.
    mysets.
  Qed.

  Lemma strict_subset_transitive_2:
    forall xs ys zs,
    subset xs ys ->
    strict_subset ys zs ->
    strict_subset xs zs.
  Proof.
    mysets.
  Qed.

  Lemma strict_subset_implies_subset:
    forall vs ws,
    strict_subset vs ws ->
    subset vs ws.
  Proof.
    mysets.
  Qed.

  Lemma contrapose_strict_subset_complement:
    forall vs ws,
    strict_subset vs (complement ws) ->
    strict_subset ws (complement vs).
  Proof.
    unfold strict_subset.
    intros ? ? [ h1 h2 ]; split.
    eauto using contrapose_subset_complement_right.
    eauto using contrapose_subset_complement_left.
  Qed.

  Lemma prove_strict_subset_complement:
    forall vs ws,
    strict_subset vs ws ->
    strict_subset (complement ws) (complement vs).
  Proof.
    unfold strict_subset.
    intros ? ? [ ? ? ]; split.
    eauto using prove_subset_complement.
    eauto using use_subset_complement.
  Qed.

  Lemma prove_strict_subset_diff:
    forall zone vs ws,
    strict_superset ws vs ->
    subset ws zone ->
    strict_subset (diff zone ws) (diff zone vs).
  Proof.
    intros ? ? ? [ ? ? ]. split.
    { eauto using prove_subset_diff. }
    { intro.
      assert (subset ws vs).
      { eapply use_subset_diff_when_included; eauto using subset_transitive. }
      tauto. }
  Qed.

End Sets.

(* ---------------------------------------------------------------------------- *)

(* Repeat some of the notations defined in the above section. Define notations
   for the polymorphic constants. *)

Notation empty_ := (@empty _).

Notation universe_ := (@universe _).

Notation member v vs :=
  (subset (singleton v) vs).

Notation diff vs ws :=
  (intersection vs (complement ws)).

Notation insert w vs :=
  (union (singleton w) vs).

Notation delete vs v :=
  (diff vs (singleton v)).

(* ---------------------------------------------------------------------------- *)

(* Repeat the tactic defined in the above section. *)

Ltac mysets := unfold universe, strict_superset, strict_subset,
  subset, complement, intersection, union, singleton, empty in *;
  try solve [ intros; tauto | eauto | intuition (subst; eauto) ].

(* ---------------------------------------------------------------------------- *)

(* Construct the hint database. *)

Hint Resolve
subset_reflexive
prove_subset_empty_left
prove_subset_union_right_1
prove_subset_union_right_2
prove_subset_union_left
prove_subset_intersection_right
prove_member_complement
prove_subset_complement
prove_not_member_union
prove_subset_intersection_left_1
prove_subset_intersection_left_2
universal_universe
prove_subset_diff
: mysets.

Hint Extern 0 (_ = _) => eapply subset_antisymmetric : mysets.

(* Transitivity is used only on demand, as it can be costly. *)

Hint Resolve
subset_transitive
: st.

(* Rewriting rules. *)

Hint Rewrite
union_empty_left
union_empty_right
union_universe_left
union_universe_right
intersection_empty_left
intersection_empty_right
intersection_universe_left
intersection_universe_right
diff_universe (* TEMPORARY redundant with intersection_universe *)
complement_universe
complement_empty
complement_union
complement_intersection
complement_complement
:
mysets.

(* ---------------------------------------------------------------------------- *)

(* Define the forward tactic. *)

(* This version is in continuation-passing style, for extensibility. *)

Ltac simplify_sets_k k :=
  match goal with
  | h: subset (union _ _) _ |- _ =>
      generalize (use_subset_union_left h); clear h; intros [ ? ? ]
  | h: member _ (complement _) |- _ =>
      generalize (use_member_complement h); clear h; intros ?
  | h: member ?v (singleton ?w) |- _ =>
      generalize (use_member_singleton h); clear h; intros ?; subst v
  | h: subset _ (intersection _ _) |- _ =>
      generalize (use_subset_intersection_right h); clear h; intros [ ? ? ]
  | _ =>
      k tt
  end.
  (* TEMPORARY use_subset_complement, use_subset_diff could be included here;
     plus, could autorewrite with simplification equations *)

(* This version is closed, for direct use. *)

Ltac simplify_sets :=
  repeat (simplify_sets_k idtac).

(* This tactic introduces a case split, which is why it is not part
   of [simplify_sets_k] above. *)

Ltac use_member_union :=
  match goal with
  | h: member _ (union _ _) |- _ =>
      generalize (use_member_union h); clear h; intros [ ? | ? ]
  end.

(* This tactic uses rewrite rules. *)

Ltac rewrite_sets :=
  autorewrite with mysets in *.

(* ---------------------------------------------------------------------------- *)

(* A connection between lists and sets. *)

From Stdlib Require Import List.

Section Lists.

  Variable V : Type.

  (* The support of a list is the set of its elements. *)

  Fixpoint lsupport (vs : list V) : set V :=
    match vs with
    | nil =>
        empty_
    | v :: vs =>
        insert v (lsupport vs)
    end.

  (* An alternate definition. *)

  Lemma lsupport_In:
    forall v vs,
    member v (lsupport vs) <-> In v vs.
  Proof.
    induction vs; simpl.
    mysets.
    split.
    intros. use_member_union.
      simplify_sets. eauto.
      rewrite <- IHvs. eauto.
    mysets.
  Qed.

  (* Support commutes with concatenation. *)

  Lemma lsupport_concat:
    forall vs ws,
    lsupport (vs ++ ws) = union (lsupport vs) (lsupport ws).
  Proof.
    induction vs; simpl; intros.
    eauto with mysets.
    rewrite IHvs. eapply union_associative.
  Qed.

  (* Support commutes with reversal. *)

  Lemma lsupport_rev:
    forall vs,
    lsupport (rev vs) = lsupport vs.
  Proof.
    induction vs; simpl; intros.
    eauto.
    rewrite lsupport_concat. rewrite IHvs. simpl. eauto 10 with mysets.
  Qed.

(* ---------------------------------------------------------------------------- *)

  (* Finiteness. *)

  Inductive finite : set V -> Prop :=
  | Finite:
      forall lvs vs,
      subset vs (lsupport lvs) ->
      finite vs.

  (* Finiteness is preserved by the set operations. *)

  Lemma finite_empty:
    finite empty_.
  Proof.
    apply Finite with (lvs := nil). simpl. eauto with mysets.
  Qed.

  Lemma finite_singleton:
    forall v,
    finite (singleton v).
  Proof.
    intro. apply Finite with (lvs := v :: nil). simpl. eauto with mysets.
  Qed.

  Lemma finite_union:
    forall vs ws,
    finite vs ->
    finite ws ->
    finite (union vs ws).
  Proof.
    inversion 1 as [ lvs ]; inversion 1 as [ lws ]; subst.
    apply Finite with (lvs := lvs ++ lws). rewrite lsupport_concat. eauto with mysets.
  Qed.

  Lemma finite_subset:
    forall vs ws,
    finite ws ->
    subset vs ws ->
    finite vs.
  Proof.
    inversion 1 as [ lws ]; intros; subst.
    apply Finite with (lvs := lws). eauto with st.
  Qed.

  Lemma finite_intersection_1:
    forall vs ws,
    finite vs ->
    finite (intersection vs ws).
  Proof.
    eauto using finite_subset, prove_subset_intersection_left_1.
  Qed.

  Lemma finite_intersection_2:
    forall vs ws,
    finite ws ->
    finite (intersection vs ws).
  Proof.
    eauto using finite_subset, prove_subset_intersection_left_2.
  Qed.

  Lemma use_finite_universe:
    finite universe_ ->
    forall vs,
    finite vs.
  Proof.
    eauto using universal_universe, finite_subset.
  Qed.

  (* [cardinal vs n] means that the cardinal of [vs] is at most [n]. *)

  Inductive cardinal : set V -> nat -> Prop :=
  | Cardinal:
      forall lvs n vs,
      subset vs (lsupport lvs) ->
      length lvs = n ->
      cardinal vs n.

  Lemma cardinal_finite:
    forall vs n,
    cardinal vs n ->
    finite vs.
  Proof.
    inversion 1; subst.
    econstructor. eauto.
  Qed.

  Lemma cardinal_empty:
    cardinal empty_ 0.
  Proof.
    apply Cardinal with (lvs := nil); eauto with mysets.
  Qed.

  Lemma cardinal_singleton:
    forall v,
    cardinal (singleton v) 1.
  Proof.
    intro. apply Cardinal with (lvs := v :: nil); simpl; eauto with mysets.
  Qed.

  Lemma cardinal_union:
    forall vs1 n1 vs2 n2,
    cardinal vs1 n1 ->
    cardinal vs2 n2 ->
    cardinal (union vs1 vs2) (n1 + n2).
  Proof.
    inversion 1 as [ lvs1 ]; inversion 1 as [ lvs2 ]; subst.
    apply Cardinal with (lvs := lvs1 ++ lvs2).
      rewrite lsupport_concat. eauto with mysets.
      eapply length_app.
  Qed.

  Lemma cardinal_subset:
    forall ws n vs,
    cardinal ws n ->
    subset vs ws ->
    cardinal vs n.
  Proof.
    inversion 1 as [ lws ]; intros; subst.
    apply Cardinal with (lvs := lws); eauto with st.
  Qed.

  Lemma cardinal_lsupport:
    forall lvs,
    cardinal (lsupport lvs) (length lvs).
  Proof.
    induction lvs; simpl.
    eauto using cardinal_empty.
    replace (S (length lvs)) with (1 + length lvs) by lia.
    eauto using cardinal_union, cardinal_singleton.
  Qed.

  Lemma finite_cardinal:
    forall vs,
    finite vs ->
    exists n,
    cardinal vs n.
  Proof.
    inversion 1 as [ lvs ]; subst.
    exists (length lvs). eauto using cardinal_subset, cardinal_lsupport.
  Qed.

  Lemma cardinal_intersection_1:
    forall vs ws n,
    cardinal vs n ->
    cardinal (intersection vs ws) n.
  Proof.
    eauto using cardinal_subset, prove_subset_intersection_left_1.
  Qed.

  Lemma cardinal_intersection_2:
    forall vs ws n,
    cardinal ws n ->
    cardinal (intersection vs ws) n.
  Proof.
    eauto using cardinal_subset, prove_subset_intersection_left_2.
  Qed.

  Lemma use_cardinal_universe:
    forall n,
    cardinal universe_ n ->
    forall vs,
    cardinal vs n.
  Proof.
    eauto using universal_universe, cardinal_subset.
  Qed.

  Lemma cardinal_strict_subset_preliminary:
    forall lws vs,
    subset vs (lsupport lws) ->
    ~ subset (lsupport lws) vs ->
    length lws > 0 /\ cardinal vs (length lws - 1).
  Proof.
    induction lws as [| w lws ]; simpl; intros.
    (* The base case is impossible. *)
    exfalso. eauto with mysets.
    (* Inductive case. *)
    split. lia.
    destruct (classic (member w vs)).
    (* Sub-case: [w] is a member of [vs]. *)
    (* Then, we can remove [w] from the set [vs], and apply the induction
       hypothesis. *)
    assert (f1: subset (delete vs w) (lsupport lws)).
      eapply subset_transitive; [ eapply intersection_covariant | ].
        eassumption.
        eapply subset_reflexive.
      solve [ mysets ].
    assert (f2: ~ subset (lsupport lws) (delete vs w)).
      solve [ eauto using prove_subset_intersection_left_2 with st mysets ].
    destruct (IHlws _ f1 f2).
    replace (length lws - 0) with ((length lws - 1) + 1) by lia.
    (* The result follows. *)
    eapply cardinal_subset; [ | eapply prove_subset_union_diff with (ws := singleton w) ].
    solve [ eauto using cardinal_union, cardinal_singleton ].
    (* Sub-case: [w] is not a member of [vs]. *)
    (* Then, we do not need the induction hypothesis. The remainder of
       the list, [lws], covers the set [vs], and is strictly shorter
       than the original list. *)
    apply Cardinal with (lvs := lws); [ | lia ].
    eapply prove_subset_by_narrowing; eauto using contrapose_subset_complement_right with mysets.
  Qed.

  Lemma cardinal_strict_subset:
    forall ws n vs,
    cardinal ws n ->
    strict_subset vs ws ->
    n > 0 /\
    cardinal vs (n - 1).
  Proof.
    destruct 1 as [ lws ]; destruct 1 as [ ? ? ]; intros; subst.
    eapply cardinal_strict_subset_preliminary; eauto with st.
  Qed.

  Lemma use_cardinal_empty:
    forall vs,
    cardinal vs 0 ->
    subset vs empty_.
  Proof.
    inversion 1 as [ lvs ]; subst.
    destruct lvs. assumption. discriminate.
  Qed.

  Lemma contradict_strict_subset_empty_right:
    forall vs : set V,
    ~ strict_subset vs empty_.
  Proof.
    intro. intro h. inversion h; subst. eauto with mysets.
  Qed.

  (* The strict subset relation, restricted to finite sets, is well-founded,
     even if the universe is infinite. *)

  Lemma wf_strict_subset_when_finite:
    well_founded (fun vs ws : set V => strict_subset vs ws /\ finite ws).
  Proof.
    (* The argument is, if [vs] is a strict subset of [ws] and [ws] is
       finite, then the cardinal of [vs] is less than the cardinal of [ws]. *)
    eapply wf_simulation with (R := cardinal); [ | | eapply lt_wf ].
    (* Check that we have a simulation. *)
    { intros ? ? ? hc [ hs ? ].
      destruct (cardinal_strict_subset hc hs) as [ ? ? ].
      eexists. split. eauto. lia. }
    (* Check that every finite set has a well-defined cardinal. *)
    { intuition eauto using finite_cardinal. }
  Qed.

  (* As a corollary, if the universe is finite, the strict subset relation
     is well-founded. *)

  Lemma wf_strict_subset:
    finite universe_ ->
    well_founded (fun vs ws : set V => strict_subset vs ws).
  Proof.
    intros. eapply wf_incl; [ repeat intro | eapply wf_strict_subset_when_finite ]. simpl.
    eauto using finite_subset, universal_universe.
  Qed.

  (* If the universe is finite, the strict superset relation is well-founded. *)

  Lemma wf_strict_superset:
    finite universe_ ->
    well_founded (@strict_superset V).
  Proof.
    intro.
    eapply wf_simulation_functional with (F := @complement V); [ | eauto using wf_strict_subset ].
    unfold strict_superset. eauto using prove_strict_subset_complement.
  Qed.

  (* Even in the absence of a finiteness assumption about the universe, the
     strict superset relation, restricted to a finite zone, is well-founded. *)

  Lemma wf_strict_superset_when_finite:
    forall zone,
    finite zone ->
    well_founded (fun vs ws => strict_superset vs ws /\ subset vs zone).
  Proof.
    intros ? hz.
    eapply wf_simulation_functional with (F := fun vs => diff zone vs);
      [ | eapply wf_strict_subset_when_finite ].
    intuition eauto using prove_strict_subset_diff, finite_subset with mysets.
  Qed.

(* ---------------------------------------------------------------------------- *)

  (* Infiniteness and cofiniteness. *)

  Definition infinite vs :=
    ~ (finite vs).

  Definition cofinite vs :=
    finite (complement vs).

  (* The universe is cofinite. *)

  Lemma cofinite_universe:
    cofinite universe_.
  Proof.
    unfold cofinite. rewrite complement_universe. eapply finite_empty.
  Qed.

  (* If the universe is infinite, then every cofinite set is nonempty. *)

  Lemma cofinite_nonempty:
    infinite universe_ ->
    forall vs,
    cofinite vs ->
    exists v, vs v.
  Proof.
    unfold cofinite.
    intros ? ? ?.
    (* Reason by reductio ad absurdum. *)
    eapply not_all_not_ex. intros hypothesis.
    (* We claim that [vs] must be empty. *)
    assert (f: complement vs = universe_). eapply subset_antisymmetric; mysets.
    clear hypothesis.
    rewrite f in *; clear f.
    (* A contradiction appears. *)
    unfold infinite in *. tauto.
  Qed.

  (* The intersection of two cofinite sets is cofinite. *)

  Lemma cofinite_intersection:
    forall vs ws,
    cofinite vs ->
    cofinite ws ->
    cofinite (intersection vs ws).
  Proof.
    unfold cofinite. intros.
    rewrite complement_intersection.
    eauto using finite_union.
  Qed.

  (* Cofiniteness is preserved by inclusion. *)

  Lemma cofinite_subset:
    forall vs ws,
    cofinite vs ->
    subset vs ws ->
    cofinite ws.
  Proof.
    unfold cofinite. eauto using finite_subset, prove_subset_complement.
  Qed.

End Lists.

(* ---------------------------------------------------------------------------- *)

(* Experimental support for rewriting. *)

Global Obligation Tactic :=
  repeat intro; mysets.

Program Instance Reflexive_subset:
  forall V, Reflexive (@subset V).

Program Instance Transitive_subset:
  forall V, Transitive (@subset V).

Program Instance Proper_union:
  forall V, Proper (@subset V ++> @subset V ++> @subset V) (@union V).

Program Instance Proper_intersection:
  forall V, Proper (@subset V ++> @subset V ++> @subset V) (@union V).

Program Instance Proper_complement:
  forall V, Proper (flip (@subset V) ++> @subset V) (@complement V).

Program Instance subrelation_strict_subset_subset:
  forall V, subrelation (@strict_subset V) (@subset V).

Program Instance Proper_strict_subset_1:
  forall V, Proper (flip (@subset V) ++> @subset V ++> impl) (@strict_subset V).
