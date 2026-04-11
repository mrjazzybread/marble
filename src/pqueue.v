From stdpp Require Import numbers list.
From listz Require Import listz.
Notation len := length.
Local Ltac Zify.zify_pre_hook ::= ulength.
From Stdlib Require Import Uint63.
From Stdlib Require Import Array.PArray.
From marble Require Import tactics bool iteration int wp.
From marble Require array vector.
From marble Require Import orders compare equations.
Implicit Types _i _j _k _n : int.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

Local Ltac wp_intro_hook Hx ::=
  list in Hx; unpack in Hx; wp_ret_hook.

(* This file implements a priority queue inside a vector. We follow
   the code by Jean-Christophe Filliâtre in OCaml's standard library:
   https://github.com/ocaml/ocaml/blob/trunk/stdlib/pqueue.ml

   See also the verified priority queue in Why3's examples library,
   by Aymeric Walch, Mário Pereira and Jean-Christophe Filliâtre:
   https://gitlab.inria.fr/why3/why3/-/blob/master/examples/pqueue.mlw *)

Section PQueue.

(* -------------------------------------------------------------------------- *)

(* Assumptions. *)

(* We assume that there is a preorder [R], also written [≤], on the type [A]. *)

(* We also assume that there is a two-way comparison function [leb]. *)

Context `{Inhabited A} `{PreOrder A R} `{LebSpec A R}.

Infix "≤?" := leb
  (at level 70, no associativity) : element_scope.

Implicit Types x y : A.

(* Standard mathematical notation. *)

Open Scope element_scope.

Infix "≤" := R
  (at level 70, no associativity) : element_scope.
Infix "<" := (strict R)
  (at level 70, no associativity) : element_scope.
Notation "y ≥ x" := (x ≤ y)
  (only parsing, at level 70, no associativity) : element_scope.
Notation "y > x" := (x < y)
  (only parsing, at level 70, no associativity) : element_scope.
Infix "≡" := (equivalent R)
  (at level 70, no associativity) : element_scope.

(* The following hints seem to be needed. I don't understand why
   reflexivity and transitivity do not work out of the box. *)

Local Lemma reflex_le x : x ≤ x.
Proof. intros. reflexivity. Qed.
Local Lemma trans_le x y z : x ≤ y → y ≤ z → x ≤ z.
Proof. intros. transitivity y; eauto. Qed.
Local Hint Resolve reflex_le trans_le : core.
Local Hint Resolve strict_transitive_l strict_transitive_r : core.

Local Definition lt_le' := (@lt_le A R).
Local Hint Resolve lt_le' : core.

Local Lemma lt_equiv_lt x y z : x < y → y ≡ z → x < z.
Proof. unfold equivalent, strict. intros; unpack; split; eauto. Qed.
Local Lemma equiv_lt_lt x y z : x ≡ y → y < z → x < z.
Proof. unfold equivalent, strict. intros; unpack; split; eauto. Qed.
Local Hint Resolve lt_equiv_lt equiv_lt_lt : core.

(* We write [xs ≃ ys] when the lists [xs] and [ys] are equivalent up to
   a permutation of their elements. In other words, [xs ≃ ys] means that
   the multisets [xs] and [ys] are equal. *)

Local Infix "≃" := (@Permutation A)
  (at level 70, no associativity).

(* -------------------------------------------------------------------------- *)

(* The node at index [i] has children at indices [2 * i + 1] and
   [2 * i + 2], provided these are valid indices into the vector. *)

Local Notation   left i := (2 * i + 1).
Local Notation  right i := (2 * i + 2).
Local Notation parent i := ((i - 1) / 2).

(* The tree is heap-ordered. *)

Local Notation dominates_left_child x i xs :=
  (valid  (left i) xs%list → x ≤ xs%list !!!  (left i)).

Local Notation dominates_right_child x i xs :=
  (valid (right i) xs%list → x ≤ xs%list !!! (right i)).

Local Notation dominates_children x i xs :=
  (dominates_left_child  x i xs ∧
   dominates_right_child x i xs).

Definition heap xs :=
  (∀ i, valid i xs → dominates_left_child  (xs !!! i) i xs) ∧
  (∀ i, valid i xs → dominates_right_child (xs !!! i) i xs).

Local Ltac introHeap :=
  split.

Local Ltac destructHeap :=
  match goal with h: heap _ |- _ =>
    destruct h
  end.

Local Ltac destructAndKeepHeap :=
  match goal with h: heap _ |- _ =>
    generalize h; intro;
    destruct h
  end.

(* -------------------------------------------------------------------------- *)

(* Basic properties of heaps. *)

Local Lemma parent_left i : parent (left i) = i.
Proof. lia. Qed.

Local Lemma parent_right i : parent (right i) = i.
Proof. lia. Qed.

Local Lemma child_disjunction i :
  i ≠ 0 → i = left (parent i) ∨ i = right (parent i).
Proof. lia. Qed.

Local Hint Rewrite parent_left parent_right : parent.

Local Lemma exploit_heap_upwards i xs :
  heap xs → valid i xs → i ≠ 0 →
  xs !!! parent i ≤ xs !!! i.
Proof.
  intros. destructHeap.
  assert (fact: i = left (parent i) ∨ i = right (parent i)) by lia.
  destruct fact as [fact|fact];
  rewrite fact at 2;
  eauto 2 with lia.
Qed.

Local Hint Resolve exploit_heap_upwards : heap.

(* If [x] dominates the two children of slot 0 then it can be written
   into slot 0. *)

Lemma heap_insert_at_root x i xs :
  heap xs →
  i = 0 →
  valid i xs →
  dominates_children x i xs →
  heap (<[i := x]>xs).
Proof.
  intros. destructHeap.
  introHeap; intros j ?; list; intro;
  case_lookup_insert; unpack; try subst;
  eauto 2 with lia.
Qed.

(* If [x] dominates the two children of slot [i] and if it is dominated
   by the parent of slot [i] then [x] can be written into slot [i]. *)

Lemma heap_insert_deep x i xs y :
  heap xs →
  i ≠ 0 →
  valid i xs →
  dominates_children x i xs →
  y = xs !!! parent i →
  y ≤ x →
  heap (<[i := x]>xs).
Proof.
  intros. destructHeap. subst y.
  introHeap; list; intros j ??;
  repeat case_lookup_insert; unpack; try subst;
  autorewrite with parent in *;
  eauto 2 with lia.
Qed.

(* Moving an element [y] from slot [parent i] down to slot [i] is
   always permitted. *)

Lemma heap_move_down x i xs y :
  heap xs →
  i ≠ 0 →
  valid i xs →
  y = xs !!! parent i →
  heap (<[i := y]>xs).
Proof.
  intros. destructAndKeepHeap. subst y.
  introHeap; list; intros j ??;
  repeat case_lookup_insert; unpack; try subst;
  autorewrite with parent in *;
  eauto 4 with heap lia.
Qed.

(* -------------------------------------------------------------------------- *)

(* A priority queue is represented as a vector. *)

Definition queue (A : Type) :=
  vector.vector A.

(* The proposition [isQueue q ys] means that [q] is a priority queue whose
   elements form the list [ys]. *)
(* TODO should [xs] be a finite set? a sorted list? *)

Definition isQueue (q : queue A) (ys : list A) :=
  ∃ xs,
  vector.isVector q xs ∧
  xs ≃ ys ∧
  heap xs.

(* These tactics and lemmas help work with the above propositions. *)

Local Ltac introQueue :=
  unfold isQueue; eexists; pack; [ eauto | | ].

Tactic Notation "destructQueue" simple_intropattern(xs) :=
  match goal with h: isQueue ?q _ |- _ =>
    unfold isQueue in h;
    destruct h as (xs & h);
    unpack in h
  end.

Lemma isQueue_bounded_length (a : queue A) ys :
  isQueue a ys →
  0 ≤ len ys ≤ array.max_array_length.
Proof.
  intros. destructQueue xs. lengths.
  assert (0 ≤ len xs ≤ array.max_array_length)
    by eauto using vector.isVector_bounded_length.
  lia.
Qed.

(* -------------------------------------------------------------------------- *)

(* The tactic [queues] looks for hypotheses of the form [isQueue q xs]
   and introduces the fact [0 ≤ len xs ≤ max_array_length]. *)

Ltac queues :=
  repeat match goal with
  h: isQueue ?q ?xs |- _ =>
    let h' := fresh h in
    generalize (isQueue_bounded_length q xs h); intro h';
    revert h h'
  end;
  intros;
  (* We also introduce [unsigned max_array_length]. *)
  generalize array.unsigned_max_array_length; intro.

(* -------------------------------------------------------------------------- *)

(* Conventions. *)

Implicit Types q : queue A.
Implicit Types v : vector.vector A.
Implicit Types xs : list A.
Implicit Types a b : array A.

(* -------------------------------------------------------------------------- *)

(* Creating an empty queue: [create]. *)

Definition create (_ : unit) : queue A :=
  vector.create().

Lemma wp_create :
  wp (create ()) (λ q, isQueue q []).
Proof.
  unfold create.
  wp_op vector.wp_create introducing: q.
  introQueue.
  + eauto.
  + introHeap; length; intros; exfalso; lia.
Qed.

(* -------------------------------------------------------------------------- *)

Section Code.
Open Scope uint63.

(* TODO use [vector.borrow] and work directly on the array *)

Lemma move_up_ilt _i : (_i =? 0) = false → ilt ((_i - 1) / 2) _i.
Proof. eauto with lia. Qed.

Fixpoint move_up v _i x (ACC : Acc ilt _i) : vector.vector A :=
  IFC _i =? 0 THEN λ _,
    vector.set v _i x
  ELSE λ Hi,
    let _j := (_i - 1) / 2 in (* [_j] is the parent of [_i] *)
    do y ← vector.get v _j ;
    if leb y x then
      (* [x] can settle in slot [_i]. *)
      vector.set v _i x
    else
      (* Move [y] down into slot [_i] and continue moving [x] up. *)
      do v ← vector.set v _i y ;
      move_up v _j x (Acc_inv ACC (move_up_ilt _i Hi)).

Definition insert q x :=
  do _n ← vector.length q ;
  if _n =? 0 then
    vector.push q x
  else
    let _j := (_n - 1) / 2 in (* [_j] is the parent of [_n] *)
    do y ← vector.get q _j ;
    if leb y x then
      (* [x] can settle in slot [_n]. *)
      vector.push q x
    else
      (* Move [y] down into slot [_n] and continue moving [x] up. *)
      do v ← vector.push q y ;
      move_up v _j x (Wf_ilt _j).

End Code.

Definition move_up_post v xs i x :=
  ∃ xs',
  vector.isVector v xs' ∧
  <[i := x]>xs ≃ xs' ∧
  heap xs'.

Local Ltac intro_move_up_post :=
  eexists; split; [ eauto | pack; eauto ].

Local Ltac elim_move_up_post xs' :=
  match goal with h: move_up_post _ _ _ _ |- _ =>
   destruct h as (xs' & h);
   unpack in h
  end.

Lemma wp_move_up _i :
  ∀ v x ACC xs,
  vector.isVector v xs →
  heap xs →
  ∀ i, isInt _i i →
  valid i xs →
  dominates_children x i xs →
  wp (move_up v _i x ACC) (λ v, move_up_post v xs i x).
Proof.
  by well-founded induction on _i along ilt.
  intros. unpack. vector.vectors.
  destruct ACC; simpl.
  wp_if.
  (* Case [i = 0]. *)
  { wp_op vector.wp_set shadowing: v.
    intro_move_up_post; eauto using heap_insert_at_root. }
  (* Case [i ≠ 0]. *)
  set (_j := ((_i - 1) / 2)%uint63).
  set (j := parent i).
  assert (isInt _j j) by tc.
  wp_op vector.wp_get introducing: y.
  wp_if.
  (* Subcase: [y ≤ x]. *)
  { wp_op vector.wp_set shadowing: v.
    intro_move_up_post; eauto using heap_insert_deep. }
  (* Subcase: [x < y]. *)
  { wp_op vector.wp_set shadowing: v.
    wp_op IH shadowing: v.
    + (* The first precondition of the recursive call. *)
      eauto using heap_move_down.
    + (* The second precondition of the recursive call. *)
      destructHeap. subst y.
      split; intros; case_lookup_insert; eapply lt_le';
      eapply strict_transitive_l; eauto 2 with lia.
    + elim_move_up_post xs'. intro_move_up_post.
      (* Permutation. *)
      match goal with h: _ ≃ xs' |- _ => rewrite <- h end.
      rewrite swap_inserts by lia.
      rewrite (list_insert_total_id' _ j) by (list; eauto with lia).
      eauto. }
Qed.

(* -------------------------------------------------------------------------- *)

End PQueue.
