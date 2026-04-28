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

From stdpp Require Import numbers list.
From stdpp Require Import sets propset.
From listz Require Import listz.
Notation len := length.
From Stdlib Require Import Uint63.
From Stdlib Require Import Array.PArray.
From Stdlib Require Export ZifyNat ZifyUint63.
From marble Require Import tactics bool int iteration loop wp array.
From marble.logic Require Import relations dfs.
From marble Require Import listz_buffer. (* TODO *)
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

(* -------------------------------------------------------------------------- *)

(* The weight of an array [m] is defined as the number of unmarked
   vertices in this array. It is a natural number. This number is
   used to establish the termination of the algorithm. *)

Local Definition unmarked (b : bool) : nat :=
  if b then 0 else 1.

Definition mweight m : nat :=
  sum_with unmarked m.

(* -------------------------------------------------------------------------- *)

(* The state of the depth-first search algorithm is a pair [(m, u)] where
   [m] is the marks array and [u] is a user state of arbitrary type [U]. *)

Section S.

(* The user state. *)

Variable U : Type.
Implicit Type u : U.

(* A state [s] is a pair [(m, u)]. *)

Definition S : Type := marks * U.
Implicit Type s : S.

(* The notion of weight is extended to states. *)

Definition weight s :=
  let (m, _) := s in mweight m.

(* We write [safe s] for the type of an accessibility witness. *)

Notation safe s :=
  (Acc lt (weight s)).

(* The notations [s' ≤ s] and [s' < s] help reason about the weight
   of a state without visual overhead. *)

Definition slt s' s := lt (weight s') (weight s).
Definition sle s' s := le (weight s') (weight s).
Declare Scope state_scope.
Infix "≤" := sle (at level 70) : state_scope.
Infix "<" := slt (at level 70) : state_scope.
Open Scope state_scope.

(* [beyond s] is the type of a state [s'] such that [s' ≤ s] holds. *)

Definition beyond s :=
  { s' | s' ≤ s }.

(* [below s] is the type of a state [s'] such that [s' < s] holds. *)

Definition below s :=
  { s' | s' < s }.

(* [pack_beyond s] wraps the state [s] so that it has type [beyond s]. *)

Definition pack_beyond s : beyond s :=
  Specif.exist _ s (Nat.le_refl (weight s)).

(* [pack_below s ow] packages the state [s'] and the witness [ow : s' < s]
   so that they have type [beyond s]. *)

Definition pack_below {s} s' (ow : s' < s) : below s :=
  Specif.exist _ s' ow.

(* [bury], an identity function on states, proves that if a state [s0]
   is beyond [s1], and if [s1 < s2] holds, then [s0] is below [s2]. *)

Local Definition bury {s1 s2} : s1 < s2 → beyond s1 → below s2.
Proof.
  intros ow12 (s0 & ow01). exists s0.
  unfold sle, slt in *. eauto using Nat.le_lt_trans.
Defined.

(* [decay], an identity function on states, proves that if a state [s']
   is below [s] then it is also beyond [s]. (Information is lost.) *)

Local Definition decay {s} : below s → beyond s.
Proof.
  intros (s' & ow). exists s'.
  unfold slt, sle in *. eauto using Nat.lt_le_incl.
Defined.

(* [bury] and [decay] are identity functions, so, while reasoning via
   [wpd] judgements, they have no effect. *)

Local Lemma wpd_bury {s1 s2} (a : beyond s1) (pf : s1 < s2) Q :
  wpd a Q →
  wpd (bury pf a) Q.
Proof.
  unfold bury. destruct a. tauto.
Qed.

Local Lemma wpd_decay {s} (a : below s) Q :
  wpd a Q →
  wpd (decay a) Q.
Proof.
  unfold decay. destruct a. tauto.
Qed.

(* [transform] applies a transformation [f] to the component [u] in
   a composite state of the form [((m', u'), ow)]. *)

Local Definition transform {s} (f : U → U) : beyond s → beyond s.
Proof.
  intros ((m' & u') & ow).
  exists (m', f u'). assumption.
Defined.

(* A reasoning rule for [transform]. *)

Local Lemma wpd_transform {s} f (s' : beyond s) Q :
  wpd s' (λ '(m', u'), wp (m', f u') Q) →
  wpd (transform f s') Q.
Proof.
  unfold transform. destruct s' as ((m' & u') & ?). eauto.
Qed.

(* [decrease] constructs a strict ordering witness, expressing the idea
   that if the vertex [_v] is unmarked in the state [s], which is the pair
   [(m, u)], then marking [_v] produces a new state of smaller weight. *)

Lemma decrease s m _v u u' :
  s = (m, u) →
  safe s →
  (_v <? length m)%uint63 = true →
  get m _v = false →
  (set m _v true, u') < s.
Proof.
  intros ? Hsafe Hv Hget. subst.
  unfold slt, weight, mweight.
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

(* Every state is safe. *)

Local Lemma all_safe s : safe s.
Proof.
  eapply (Acc_intro_generator 32). eapply Wf_nat.lt_wf.
Defined.

(* -------------------------------------------------------------------------- *)

(* The main recursive function of the depth-first search algorithm: [visit].  *)

Section Visit.

(* [foreach_successor a _v] iterates on the successors of the vertex [_v]. *)

(* Fortunately, no properties of this function are needed in the proof of
   termination of [visit]. *)

Variable foreach_successor : ∀ {A}, A → _vertex → (A → _vertex → A) → A.

(* The user function [hook _event u] is invoked when an event is observed,
   that is, when a vertex is entered or exited. It updates the user state
   [u]. *)

(* If the user needs to observe only one kind of event, they can provide
   a hook that ignores the other kind. *)

Variable hook : event _vertex → U → U.

(* [visit] expects a state [s], a vertex [_v], and a proof that [s] is
   safe (accessible). This proof is used to justify termination; the
   function is defined by structural recursion on [ACC]. *)

(* [visit s _v ACC] produces a result of type [beyond s], that is, a new
   state [s'] such that [s' ≤ s] holds. This information is required,
   while iterating on the successors of a state, to prove that every call
   to [visit] in this sequence is permitted. *)

(* To iterate on the successors, we use a normal (simply-typed) iteration
   function. This requires us to package [visit] as a function whose
   argument state and result state have the same type, and which does not
   require an accessibility witness as an argument. Fortunately, this is
   possible! *)

Fixpoint visit s _v (ACC : safe s) : beyond s :=
  (* Destruct [s] as a pair [m, u] while keeping track of the equation. *)
  match s as b return s = b → _ with (m, u) => λ Hsmu,
  (* Test whether this vertex is valid. *)
  IFC (_v <? length m)%uint63 THEN λ Hv,
  (* Test whether this vertex is marked. *)
  IFC get m _v THEN λ _,
    (* It is marked: do nothing. *)
    pack_beyond s
  ELSE λ Hunmarked,
    (* Mark this vertex. *)
    let m' := set m _v true in
    (* Invoke [hook] to signal that we are entering [_v]. *)
    do u' ← hook (Enter _v) u ;
    (* Construct an updated state. *)
    let s' := (m', u') in
    (* Construct a witness of the assertion [s' < s]. *)
    let ow : s' < s := decrease s m _v u u' Hsmu ACC Hv Hunmarked in
    (* Package them together. *)
    let s' := pack_below s' ow in
    (* Package [visit] as a function of type [below s → vertex → below s],
       which can be passed to [foreach_successor]. Because we have [ACC]
       at hand, any call to [visit] on a state that is smaller than [s] is
       permitted. Therefore we are able to package [visit] as a function
       that does not require an accessibility witness. *)
    (* This construction has just [visit] and [ACC] as free variables. *)
    let visit (sow' : below s) (_w : _vertex) : below s :=
      let (s', ow) := sow' in
      bury ow (visit s' _w (Acc_inv ACC ow))
    in
    (* Visit the successors of [v]. *)
    do sow ← foreach_successor s' _v visit ;
    (* Forget that we went below [s]. *)
    do sow ← decay sow ;
    (* Invoke [hook] to signal that we are exiting [_v]. *)
    do sow ← transform (hook (Exit _v)) sow ;
    sow
  ELSE λ _,
     (* This vertex is out-of-bounds. Ignore it. This lets us prove
        termination without imposing any conditions on the vertices
        that we receive. *)
    pack_beyond s
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

(* We now formulate more hypotheses about the functions [foreach_successor]
   and [body], which the user provides. Under these hypotheses, we prove
   that [visit] is correct. *)

(* The vertices must form a directed graph. *)

Variable E : relation vertex.

(* The vertices must be numbered from 0 to [n], excluded. *)

Variable n : Z.

(* No edge can leave the interval [0, n). *)

Hypothesis bound :
  ∀ v w, 0 ≤ v < n → E v w → 0 ≤ w < n.

(* -------------------------------------------------------------------------- *)

(* The set [start] is the set of vertices where the user would like
   the traversal to begin. *)

Local Notation vertices := (propset vertex).

Variable start : vertices.

(* -------------------------------------------------------------------------- *)

(* [marked], [imarked], [omarked] denote sets of vertices. *)

Implicit Types marked imarked omarked : vertices.

Implicit Type σ : stack vertex.

(* We wish to specify what sequences of events the user can expect to
   observe. In short, we are a producer of events. We must expose the
   labeled transition system that we obey: that is, we must define the
   type of producer states as well as the relation that specifies one we
   move from one producer state to the next, while emitting an event. *)

(* A producer state is a pair [(marked, σ)]. *)

(* We name this type [ghost] to emphasize that it is NOT the type of
   runtime states, [S]. Producer states do not exist at runtime. *)

Local Notation ghost :=
  (dfs.state vertex).

Implicit Type γ : ghost.

(* A transition from state [γ] to state [γ'], emitting an event [e], is
   permitted if the relation [step] allows it. *)

Local Notation step :=
  (dfs.step E start).

(* The assertion [wf γ] means that the set of vertices [marked] and the
   stack [σ] are a well-formed state of an ongoing DFS traversal of the
   graph [E]. *)

Local Notation wf := (dfs.wf E start ∅).

Local Hint Constructors dfs.wf : wf.

Local Hint Resolve wf_step : wf.

(* The assertion [edge (top σ) v] means that there is an edge of the
   stack's current vertex to [v]. (If the stack has no current vertex,
   it means that [v] is a member of the set [start].) *)

Local Notation edge := (dfs.edge E start).

(* -------------------------------------------------------------------------- *)

(* The function [foreach_successor], applied to [_v], must enumerate the
   successors of the vertex [v]. They can be enumerated in an arbitrary
   order, and it is permitted for a vertex [w] to be presented several
   times. *)

Local Notation successors v :=
  (image E {[v]}).

Variable wp_foreach_successor:
  ∀ {A} (body : A → _vertex → A),
  ∀Int _v v,
  0 ≤ v < n →
  ITER_SET ∅ (successors v)
    (λ w a Q, ∀ _w, isInt _w w → wp (body a _w) Q)
    (λ a Q, wp (foreach_successor a _v body) Q).

(* -------------------------------------------------------------------------- *)

(* The function [hook], applied to an event and to a user state,
   returns a new user state. *)

(* The user's loop invariant is a parameter. As usual (iteration.v),
   it relates a producer state [γ] and a user state [u]. *)

Variable inv : ghost → U → Prop.

(* [isEvent _e e] relates a runtime event [_e] and an event [e].
   They are the same thing, up to the relation between a machine
   integer [_v] and an ideal integer [v]. *)

Inductive isEvent : event _vertex → event vertex → Prop :=
| IsEventEnter:
    ∀ _v v, isInt _v v → 0 ≤ v < n → isEvent (Enter _v) (Enter v)
| IsEventExit:
    ∀ _v v, isInt _v v → 0 ≤ v < n → isEvent (Exit _v) (Exit v).

Local Hint Constructors isEvent : marble.

(* The specification of the user function [hook] states that [hook]
   can expect the invariant [inv γ u] to hold, can expect to observe
   an event [e] such that [move γ e γ'] holds, and must update the
   user state to a new state [u'] such that [inv γ' u'] holds. *)

Variable wp_hook :
  ∀ γ γ' u,
  inv γ u →
  ∀ _e e,
  isEvent _e e →
  step γ e γ' →
  wp (hook _e u) (λ u', inv γ' u').

(* -------------------------------------------------------------------------- *)

(* [isMarks m marked] means that the Boolean array [m] represents the set
   of vertices [marked]. *)

Open Scope Z_scope.

Definition isMarks m marked :=
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

Local Instance isBool_get_mark m marked :
  ∀Int _v v,
  0 ≤ v < n →
  isMarks m marked →
  isBool1 (get m _v) (v ∈ marked).
Proof.
  intros. destructMarks.
  assert (fact: wp (get m _v) (eq (bs !!! v))).
  { wp_get b. eauto. }
  rewrite wp_iff in fact.
  rewrite <- fact. tc.
Qed.

Local Lemma mark_self marked v : v ∈ {[v]} ∪ marked.
Proof. set_solver. Qed.
Local Hint Resolve mark_self : marble.

Local Lemma mark_unaffected marked v v' :
  v ≠ v' →
  v' ∈ {[v]} ∪ marked ↔ v' ∈ marked.
Proof. set_solver. Qed.

(* -------------------------------------------------------------------------- *)

(* The postcondition of [visit]. *)

(* [visit_post γ examined s'] means that, if one starts from the producer
   state [γ] then [s'] is a correct final runtime state where every vertex
   in the set [examined] is marked. *)

Definition visit_post γ examined s' :=
  let (marked, σ) := γ in
  let (m', u') := s' in
  ∃ marked' σ',
  isMarks m' marked' ∧
  marked ⊆ marked' ∧
  inv (marked', σ') u' ∧
  similar σ σ' ∧
  wf (marked', σ') ∧
  examined ⊆ marked'.

Local Ltac intro_visit_post :=
  unfold visit_post; do 2 eexists; pack;
    [ eauto | set_solver | eauto  |
      eauto using similar_store with similar wf |
      eauto with wf | set_solver ].

Local Ltac elim_visit_post marked' σ' :=
  match goal with h: visit_post _ _ _ |- _ =>
    unfold visit_post in h;
    destruct h as (marked' & σ' & h);
    unpack in h
  end.

Local Hint Resolve similar_same_edges : marble.
Local Hint Extern 1 (_ ≡ _) => reflexivity : marble.
Local Opaque bury decay transform.

(* The specification of [visit]. *)

(* Because the result type of [visit] is a subset type,
   instead of [wp], we use the judgement [wpd]. *)

Lemma wpd_visit (k : nat) :
  ∀ m u _v v ACC marked σ,
  mweight m = k →
  isMarks m marked →
  inv (marked, σ) u →
  wf (marked, σ) →
  isInt _v v →
  0 ≤ v < n →
  edge (top σ) v →
  wpd (visit (m, u) _v ACC) (λ s', visit_post (marked, σ) {[v]} s').
Proof.
  by well-founded induction on k along lt.
  intros. subst k. destruct ACC. simpl visit.
  destructMarks. arrays.
  (* Because we require [v < n], the first branch of this conditional
     construct must be taken. The second branch is dead. *)
  eapply wpd_IFC; [ tc | intros | lia ].
  (* The second conditional construct tests whether [v] is marked. *)
  eapply wpd_IFC; [ tc | intros | intros ].
  (* Case: [v] is marked already. *)
  { eapply wpd_ret. intro_visit_post. }
  (* Case: [v] is unmarked. We mark this vertex. *)
  assert (Hm': wp (set m _v true) (λ m, isMarks m ({[v]} ∪ marked))).
  { wp_set. introMarks. intros v' ?. case_lookup_insert.
    + subst v'. tc.
    + rewrite mark_unaffected by assumption. tc. }
  rewrite wp_iff in Hm'. revert Hm'.
  set (m' := set m _v true).
  set (marked' := {[v]} ∪ marked).
  set (σ' := Frame (Some v) Empty :: σ).
  intro.
  (* We invoke the user function [hook]. *)
  assert (step (marked, σ) (Enter v) (marked', σ')).
  { econstructor; tc. }
  eapply wpd_bind.
  { eapply wp_hook; tc. }
  cbv beta; intros u' ?.
  (* The state at this point is described by [marked'], [σ'], [u']. *)
  eapply wpd_wpd_bind_unary.
  (* We reach the loop on the successors of [v]. The goal must be changed
     from [wpd] to [wp], so that [wp_foreach_successor] can be used. *)
  rewrite wpd_wp.
  wp_op wp_foreach_successor with invariant: (
    λ examined (s'' : { s'' | slt s'' (m, u) }),
      visit_post (marked', σ') examined (proj1_sig s'')
  ).
  (* Initialization. *)
  { simpl. intro_visit_post. }
  (* Preservation. *)
  { wp_body examined0 examined1 ((m'' & u'') & ow)
      introducing: (fun _ => set_step w; intros _w ?).
    elim_visit_post marked'' σ''.
    assert (E v w) by set_solver.
    (* The state at this point is described by [marked''], [σ''], [u''].
       The successors of [v] that have been examined already form the
       set [examined0], a subset of [marked'']. The vertex [w], also
       a successor of [v], is about to be examined. *)
    (* Change the goal back into [wpd] format. *)
    eapply wp_wpd
      with (Q1 := λ s'', visit_post (marked', σ') examined1 s'');
      [| solve [ eauto] ].
    eapply wpd_bury.
    (* Use the induction hypothesis to justify calling [visit s'' _w]. *)
    eapply wpd_conseq.
    { eapply IH; try reflexivity; tc. }
    (* Justify that this call establishes the loop invariant. *)
    cbv beta. intros (m''' & u''') ?.
    elim_visit_post marked''' σ'''.
    intro_visit_post. }
  (* All successors of [v] have now been examined. *)
  intros ((m'' & u'') & ?). simpl proj1_sig.
  intros (examined & Hpost & Hexamined) ?.
  elim_visit_post marked'' σ''.
  (* Decay. *)
  eapply wpd_wpd_bind_unary.
  eapply wpd_decay. eapply wpd_ret.
  simpl proj1_sig. intro.
  (* The structure of the stack has been preserved. *)
  unfold σ' in Hpost2.
  assert (∃ vs, σ'' = Frame (Some v) vs :: σ) as (vs & ?).
  { inversion Hpost2. eauto. }
  set (marked''' := marked'').
  set (σ''' := store v vs σ).
  (* We invoke the user function [hook] again. *)
  assert (step (marked'', σ'') (Exit v) (marked''', σ''')).
  { econstructor; eauto with set_solver. }
  eapply wpd_wpd_bind_unary.
  eapply wpd_transform.
  eapply wpd_ret. simpl proj1_sig. cbv iota.
  change (m'', hook (Exit _v) u'')
    with (do u''' ← hook (Exit _v) u'' ; (m'', u''')).
  wp_op wp_hook introducing: u'''.
  (* Return. *)
  wp_ret. intro. eapply wpd_ret.
  intro_visit_post.
Qed.

(* -------------------------------------------------------------------------- *)

(* Once the termination of [visit] has been established, one can define a
   simplified version of it, which does not need an accessibility witness,
   and whose result type is just [S]. *)

Definition visit' s _v : S :=
  proj1_sig (visit s _v (all_safe s)).

(* As an exercise, we prove that [visit'] satisfies the desired fixed
   point equation. Most likely, we will NOT need this property. I am
   showing this proof for pedagogical purposes; it is super difficult
   if one does not approach it in exactly the right way. *)

(* Under [proj1_sig], the coercion [bury] vanishes. *)

Local Lemma proj1_sig_bury {s1 s2} (pf : slt s1 s2) (s' : beyond s1) :
  proj1_sig (bury pf s') = proj1_sig s'.
Proof.
  destruct s'. eauto.
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

(* [visit] satisfies the desired fixed point equation: *)

Lemma visit_eq (k : nat) :
  ∀ s _v ACC,
  weight s = k →
  proj1_sig (visit s _v ACC) =
    let (m, u) := s in
    if (_v <? length m)%uint63 then
      do b ← get m _v ;
      if b then
        s
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
Proof.
  by well-founded induction on k along lt.
  intros. subst k. destruct ACC as (ACC). simpl visit.
  destruct s as (m & u).
  eapply IFC_if_dep; intro; [| eauto ].
  eapply IFC_if_dep; intro; [ eauto |].
  (* Eliminate [do m' ← ...], which appears only on one side. *)
  unfold bind at 5.
  eapply bind_eq_dep; [ eauto | intro u' ].
  eapply bind_eq_dep_dep; [| clear u' ].
  (* The loop. *)
  { eapply foreach_successor_parametric
      with (A := λ (s1 : below (m, u)) (s2 : S), proj1_sig s1 = s2);
      [| eauto ].
    intros (s' & ?) ?. simpl. intros <- _w.
    rewrite proj1_sig_bury.
    unfold visit'.
    (* The goal boils down to proving that the parameter [ACC] is
       computationally irrelevant; that is, it does not influence
       the first projection of the result of [visit]. *)
    erewrite !IH by eauto. (* rewrite both sides *)
    reflexivity. }
  (* The code that follows the loop. *)
  intros (m' & u') ?. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)

(* The top-level function does not need an accessibility witness.
   It allocates the marks array [m]. *)

(* TODO use [foreach_root] *)

(* Variable u0 : U. *)
(* Variable Hinit : *)
(*   inv (∅, (Frame None Empty) :: []) u0. *)

(* TODO in the end, the spec of the toplevel DFS function should be an
   instance of [ITER]. *)

Definition visit_top _n u _v : S :=
  let m := init _n (λ _i, false) in
  let s := (m, u) in
  visit' s _v.

End Visit.

End S.
