From stdpp Require Import numbers list.
From listz Require Import listz.
Notation len := length.
Local Ltac Zify.zify_pre_hook ::= ulength.
From Stdlib Require Import Uint63.
From Stdlib Require Import Array.PArray.
From marble Require Import tactics bool iteration int wp.
From marble Require Import array vector.
From marble Require Import orders compare sorting equations.
Implicit Types _i _j _k _n : int.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

(* This file implements a priority queue inside a vector. We follow
   the code by Jean-Christophe Filliâtre in OCaml's standard library:
   https://github.com/ocaml/ocaml/blob/trunk/stdlib/pqueue.ml

   See also the verified priority queue in Why3's examples library,
   by Aymeric Walch, Mário Pereira and Jean-Christophe Filliâtre:
   https://gitlab.inria.fr/why3/why3/-/blob/master/examples/pqueue.mlw *)

Section PQueue.

(* -------------------------------------------------------------------------- *)

(* Assumptions. (These assumptions should be identical to those in sort.v,
   but they have diverged a bit, as I have made some changes.) *)

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

Local Lemma reflex_le x y : x = y → x ≤ y.
Proof. intros. subst. reflexivity. Qed.
Local Lemma trans_le x y z : x ≤ y → y ≤ z → x ≤ z.
Proof. intros. transitivity y; eauto. Qed.
Local Hint Resolve reflex_le trans_le : order.
Local Hint Resolve strict_transitive_l strict_transitive_r : order.

Local Definition lt_le' := (@lt_le A R).
Local Hint Resolve lt_le' : order.

Local Lemma lt_equiv_lt x y z : x < y → y ≡ z → x < z.
Proof. unfold equivalent, strict. intros; unpack; split; eauto with order. Qed.

Local Lemma equiv_lt_lt x y z : x ≡ y → y < z → x < z.
Proof. unfold equivalent, strict. intros; unpack; split; eauto with order. Qed.

(* We write [xs ≃ ys] when the lists [xs] and [ys] are equivalent up to
   a permutation of their elements. In other words, [xs ≃ ys] means that
   the multisets [xs] and [ys] are equal. *)

Local Infix "≃" := (@Permutation A)
  (at level 70, no associativity).

Local Ltac use_permutation_hypothesis :=
  match goal with h: _ ≃ _ |- _ => rewrite <- h; clear h end.

(* We write [xs ≼ ys] when every element of the list [xs] is less than
   or equal to every element of the list [ys]. *)

Notation "xs '≼' ys" := (pairwise R xs ys) (at level 80).

(* -------------------------------------------------------------------------- *)

(* The node at index [i] has children at indices [2 * i + 1] and
   [2 * i + 2], provided these are valid indices into the vector. *)

Local Notation     left j := (2 * j + 1).
Local Notation    right j := (2 * j + 2).
Local Notation   parent i := ((i - 1) / 2).

Local Notation   _left _j := (2 * _j + 1)%uint63.
Local Notation  _right _j := (2 * _j + 2)%uint63.
Local Notation _parent _i := ((_i - 1) / 2)%uint63.

(* The tree is heap-ordered. *)

Local Notation dominates_left_child x j xs :=
  (valid  (left j) xs%list → x ≤ xs%list !!!  (left j)).

Local Notation dominates_right_child x j xs :=
  (valid (right j) xs%list → x ≤ xs%list !!! (right j)).

Local Notation dominates_children x j xs :=
  (dominates_left_child  x j xs ∧
   dominates_right_child x j xs).

Definition heap xs :=
  (∀ j, valid j xs → dominates_left_child  (xs !!! j) j xs) ∧
  (∀ j, valid j xs → dominates_right_child (xs !!! j) j xs).

Local Ltac introHeap :=
  split.

Local Ltac destructHeap :=
  match goal with
  | h: heap _ |- _ =>
      destruct h
  end.

Local Ltac destructAndKeepHeap :=
  match goal with
  | h: heap _ |- _ =>
      generalize h; intro; destruct h
  end.

(* -------------------------------------------------------------------------- *)

(* Basic properties of heaps. *)

(* The parent of a child of [i] is [i]. *)

Local Lemma parent_left i : parent (left i) = i.
Proof. lia. Qed.

Local Lemma parent_right i : parent (right i) = i.
Proof. lia. Qed.

Local Hint Rewrite parent_left parent_right : parent.

(* These technical corollaries are used in the proof of [move_down]. *)

Lemma move_down_remark_left i y xs x :
  valid i xs →
  y < x →
  <[i:=y]>xs !!! parent (left i) < x.
Proof.
  intros. rewrite parent_left. list. assumption.
Qed.

Lemma move_down_remark_right i y xs x :
  valid i xs →
  y < x →
  <[i:=y]>xs !!! parent (right i) < x.
Proof.
  intros. autorewrite with parent. list. assumption.
Qed.

Local Hint Resolve move_down_remark_left move_down_remark_right : order.

(* Removing the last element of a heap preserves the heap property. *)

Lemma heap_pop xs x :
  heap (xs ++ {[x]}) →
  heap xs.
Proof.
  intros (Hl & Hr). introHeap.
  { intros j ? ?. specialize (Hl j). list in Hl. eauto with lia. }
  { intros j ? ?. specialize (Hr j). list in Hr. eauto with lia. }
Qed.

(* These technical remarks are used in the proofs of [move_up]. *)

Lemma move_up_remark i j y xs x :
  heap xs →
  valid i xs →
  j = parent i →
  y = xs !!! j →
  x < y →
  i ≠ 0 →
  dominates_children x (parent i) (<[i:=y]> xs).
Proof.
  length. intros. destructHeap.
  assert (x ≤ y) by eauto with order.
  split; intros; case_lookup_insert; eauto 2 with order;
  transitivity y; try assumption;
  subst y j;
  eauto 2 with lia.
Qed.

Lemma move_up'_remark n j y xs x :
  heap xs →
  n = len xs →
  j = parent n →
  y = xs !!! j →
  x < y →
  dominates_children x j (xs ++ {[y]}).
Proof.
  intros. destructHeap. list in *.
  assert (x ≤ y) by eauto with order.
  split; intros; case_lookup_app;
  transitivity y; try assumption;
  subst y;
  eauto 2 with lia.
Qed.

(* In the ideal integers, there are several ways of expressing the fact that
   a node has no left child: one can write either [n ≤ left i] or [n / 2 ≤ i].
   These conditions are equivalent. In the machine integers, however, these
   tests are not equivalent; one must add extra hypotheses, namely [i < n] and
   [n ≤ max_array_length], for these conditions to be equivalent. Thus, in
   [move_down], we prefer to use the test [n / 2 ≤ i]; this lets us prove the
   termination of [move_down] without keeping track of hypotheses about [n]
   and [i]. *)

Goal ∀ i n, (n ≤ left i ↔ parent (n - 1) < i)%Z.
Proof. lia. Qed.

Goal ∀ i n, (n ≤ left i ↔ n / 2 ≤ i)%Z.
Proof. lia. Qed.

Goal ∀ i n, (n ≤ right i ↔ parent (n - 2) < i)%Z.
Proof. lia. Qed.

Goal ∀ i n, (n ≤ right i ↔ (n - 1) / 2 ≤ i)%Z.
Proof. lia. Qed.

Goal ∀ _i _n,
  (_n ≤? _i)%uint63 = false →
  (_n ≤? max_length)%uint63 = true →
  (_n ≤? _left _i)%uint63 = true ↔
  (_n / 2 ≤? _i)%uint63 = true.
Proof. unfold max_length. lia. Qed.

Local Lemma rigt_left {_i _n} :
  (_n / 2 ≤?_i)%uint63 = false →
  rigt _n (_left _i)%uint63 _i.
Proof. tc. Qed.

Local Lemma rigt_right {_i _n} :
  ((_n - 1) / 2 ≤? _i)%uint63 = false →
  rigt _n (_right _i)%uint63 _i.
Proof. tc. Qed.

(* TODO
Local Hint Resolve rigt_left rigt_right : marble.
  with these lemmas, we hit this bug:
  https://github.com/rocq-prover/rocq/issues/21919 *)

(* If the heap property holds then every element is dominated by its
   parent in the tree. *)

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

Local Hint Resolve exploit_heap_upwards : order.

(* The first element of a heap is a minimal element. *)

(* The heap invariant is local: each element must dominate its children.
   This lemma is the only place where we extract a global consequence
   out of this local invariant. *)

Lemma root_dominates_all xs :
  heap xs →
  valid 0 xs →
  ∀ j,
  valid j xs →
  xs !!! 0 ≤ xs !!! j.
Proof.
  by well-founded induction on j using (Z.lt_wf 0). intros.
  case (decide (j = 0)); intro.
  (* Case [j = 0]. *)
  { subst j. eauto 2 with order. }
  (* Case [j ≠ 0]. *)
  { transitivity (xs !!! parent j); eauto 2 with marble order. }
Qed.

Lemma heap_minimum xs m :
  heap xs →
  valid 0 xs →
  m = xs !!! 0 →
  {[m]} ≼ xs.
Proof.
  intros. rewrite pairwise_singleton_left_iff.
  intros y Hy.
  apply list_elem_of_lookup_total_1 in Hy.
  destruct Hy as (i & ? & ?).
  subst. eauto using root_dominates_all.
Qed.

(* A grandparent dominates its grandchild. *)

Lemma grandparent_dominates_grandchild xs i j y :
  heap xs →
  parent j = i →
  y = xs !!! j →
  valid i xs →
  valid j xs →
  (0 < i)%Z →
  xs !!! parent i ≤ y.
Proof.
  intros. subst y.
  assert (xs !!! parent i ≤ xs !!! i) by eauto 2 with marble order.
  assert (xs !!! i ≤ xs !!! j) by (subst i; eauto 2 with marble order).
  eauto 2 with marble order.
Qed.

(* A transitivity property. *)

Lemma dominates_trans x y i xs :
  dominates_children y i xs →
  x ≤ y →
  dominates_children x i xs.
Proof.
  intros (? & ?) ?. split; eauto 3 with order.
Qed.

Local Hint Resolve dominates_trans : order.

(* If [x] dominates the two children of slot 0 then it can be written
   into slot 0. *)

Lemma heap_insert_at_root x i xs :
  i = 0 →
  valid i xs →
  heap xs →
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

(* A combination of the previous two lemmas. *)

Lemma heap_insert x i xs :
  heap xs →
  valid i xs →
  dominates_children x i xs →
  ((0 < i)%Z → xs !!! parent i ≤ x) →
  heap (<[i := x]>xs).
Proof.
  intros. case (decide (i = 0)); intros; [ subst i |].
  { eauto using heap_insert_at_root. }
  { eauto using heap_insert_deep with lia. }
Qed.

(* Moving an element [y] from slot [parent i] down to slot [i] is
   always permitted. This is used in the proof of [move_up]: as [x]
   moves up, [y] moves down. *)

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
  eauto 4 with marble order.
Qed.

(* The empty sequence forms a heap. *)

Lemma empty_heap xs :
  xs = [] →
  heap xs.
Proof.
  intros. subst. introHeap; list; lia.
Qed.

(* A singleton sequence forms a heap. *)

Lemma singleton_heap xs :
  len xs = 1 →
  heap xs.
Proof.
  intros. introHeap; eauto 2 with lia.
Qed.

(* If [x] is dominated by the parent of slot [n], where [n] is the final
   uninitialized slot, then [x] can be written into this slot. *)

Lemma quasi_heap_insert_deep x n xs y :
  heap xs →
  n = len xs →
  y = xs !!! parent n →
  y ≤ x →
  heap (xs ++ {[x]}).
Proof.
  intros. destructHeap.
  introHeap; intros j; length; intros; list;
  case_lookup_app;
  eauto 2 with lia;
  assert (parent n = j) by lia;
  congruence.
Qed.

(* Moving an element [y] from slot [parent n] down to slot [n],
   where [n] is the final uninitialized slot, is permitted. *)

Lemma quasi_heap_move_down x n xs y :
  heap xs →
  n = len xs →
  y = xs !!! parent n →
  heap (xs ++ {[y]}).
Proof.
  intros. destructAndKeepHeap. subst y.
  introHeap; list; intros j ??;
  repeat case_lookup_app; eauto 2 with marble.
  { replace n with (left j) by lia.
    autorewrite with parent.
    reflexivity. }
  { replace n with (right j) by lia.
    autorewrite with parent.
    reflexivity. }
Qed.

(* -------------------------------------------------------------------------- *)

(* A priority queue is represented as a vector. *)

Definition queue (A : Type) :=
  vector A.

(* The proposition [isQueue q ys] means that [q] is a priority queue whose
   elements form the list [ys]. *)
(* TODO should [xs] be a finite set? a sorted list? *)

Definition isQueue (q : queue A) (ys : list A) :=
  ∃ xs,
  isVector q xs ∧
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
  0 ≤ len ys ≤ max_array_length.
Proof.
  intros. destructQueue xs. lengths.
  assert (0 ≤ len xs ≤ max_array_length)
    by eauto using isVector_bounded_length.
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
  generalize unsigned_max_array_length; intro.

(* -------------------------------------------------------------------------- *)

(* Conventions. *)

Implicit Types q : queue A.
Implicit Types v : vector A.
Implicit Types xs ys : list A.
Implicit Types a : array A.

(* -------------------------------------------------------------------------- *)

(* Creating an empty priority queue: [create]. *)

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

(* Inserting an element into a priority queue: [move_up] and [insert]. *)

(* TODO use [vector.borrow] and work directly on the array *)

Section Code.
Open Scope uint63.

Local Lemma move_up_ilt _i : (_i =? 0) = false → ilt (_parent _i) _i.
Proof. tc. Qed.

(* [move_up v _i x] writes the element [x] into slot [_i], then moves it
   up as far as necessary so as to restore the heap invariant. *)

Fixpoint move_up v _i x (ACC : Acc ilt _i) : vector A :=
  IFC _i =? 0 THEN λ _,
    (* [x] has reached the root. *)
    vector.set v _i x
  ELSE λ Hi,
    (* [_j] is the parent of [_i]. *)
    let _j := _parent _i in
    (* Read the element [y] in slot [_j]. *)
    do y ← vector.get v _j ;
    if (y ≤? x)%element then
      (* [x] can settle in slot [_i]. *)
      vector.set v _i x
    else
      (* Move [y] down into slot [_i] and continue moving [x] up. *)
      do v ← vector.set v _i y ;
      move_up v _j x (Acc_inv ACC (move_up_ilt _i Hi)).

(* To insert a new element [x], it suffices to reserve a new slot at the end
   of the vector, thus creating a logically empty slot, and to call [move_up].
   Filliâtre does essentially this, but does not have access to [reserve], so
   he uses [push] instead, causing a redundant write. Walch et al. duplicate
   the logic of [move_up] inside [insert]. We avoid this code duplication;
   instead we verify [move_up] twice with slightly different specifications. *)

Definition insert q x :=
  do _n ← vector.length q ;
  do q ← vector.reserve q ;
  move_up q _n x (Wf_ilt _n).

End Code.

(* The postcondition of [move_up] and [move_down]. *)

(* The effect of [move_up] and [move_down] is to write [x] into slot [i]
   and then permute the elements so that they form a heap again. *)

Definition move_post v xs i x :=
  ∃ xs',
  isVector v xs' ∧
  <[i := x]>xs ≃ xs' ∧
  heap xs'.

Local Ltac intro_move_post :=
  eexists; split; [ eauto | pack; eauto ].

Local Ltac elim_move_post xs' :=
  match goal with h: move_post _ _ _ _ |- _ =>
    destruct h as (xs' & h);
    unpack in h
  end.

(* Inside [move_up v _i x], if [y] is the element at index [j], then
   writing [y] into slot [i] and calling [move_up v _j x] establishes
   the desired postcondition. *)

Lemma move_post_insert v i y xs j x :
  move_post v (<[i:=y]> xs) j x →
  valid i xs →
  valid j xs →
  i ≠ j →
  y = xs !!! j →
  move_post v xs i x.
Proof.
  intros. elim_move_post xs'. intro_move_post.
  (* A permutation goal. *)
  use_permutation_hypothesis.
  rewrite swap_inserts by eauto.
  rewrite (list_insert_total_id' _ j) by (list; eauto with lia).
  eauto.
Qed.

(* This is the first specification of [move_up]. If [xs] forms a heap and
   if [x] dominates the children of slot [i] then [move_up v _i x] can be
   called. *)

(* Intuitively, the precondition of [move_up] is: [xs] must form a heap
   except possibly at index [i], which is logically empty and could
   contain a dummy value. Here, following Walch, Pereira and Filliâtre,
   we cheat a little bit: for simplicity, we require [xs] to form a heap
   everywhere. When [move_up] calls itself, this stronger requirement is
   met because [y] has been copied down, so the logically empty slot
   contains a copy of [y]. When [insert] calls [move_up], this
   requirement is NOT met, because the logically empty slot is in fact
   uninitialized and contains an arbitrary value. To deal with this
   situation, we give a second specification of [move_up] below. *)

Lemma wp_move_up _i :
  ∀ v x ACC xs,
  isVector v xs →
  heap xs →
  ∀ i, isInt _i i →
  valid i xs →
  dominates_children x i xs →
  wp (move_up v _i x ACC) (λ v, move_post v xs i x).
Proof.
  by well-founded induction on _i along ilt.
  intros. unpack. vectors.
  destruct ACC; simpl.
  wp_if.
  (* Case [i = 0]. *)
  { wp_op vector.wp_set shadowing: v.
    intro_move_post; eauto using heap_insert_at_root. }
  (* Case [i ≠ 0]. *)
  set (_j := (_parent _i)).
  set (j := parent i).
  assert (isInt _j j) by tc3.
  wp_op vector.wp_get introducing: y.
  wp_if.
  (* Subcase: [y ≤ x]. *)
  { wp_op vector.wp_set shadowing: v.
    intro_move_post; eauto using heap_insert_deep. }
  (* Subcase: [x < y]. *)
  { wp_op vector.wp_set shadowing: v.
    assert (dominates_children x (parent i) (<[i:=y]> xs))
      by eauto using move_up_remark.
    assert (heap (<[i:=y]> xs))
      by eauto using heap_move_down.
    wp_op IH shadowing: v.
    eauto 2 using move_post_insert with marble. }
Qed.

(* This is the second specification of [move_up]. If [xs] forms a heap
   and if the vector contains the sequence [xs ++ {[dummy]}] then
   [move_up v _n x] can be called. *)

(* The proof is essentially the same as above, with small changes. *)

Lemma wp_move_up' _n n :
  ∀ v x ACC xs dummy ,
  isVector v (xs ++ {[dummy]}) →
  heap xs →
  isInt _n n →
  n = len xs →
  wp (move_up v _n x ACC) (λ v, move_post v (xs ++ {[dummy]}) n x).
Proof.
  intros. vectors. lengths. length in *.
  destruct ACC; simpl.
  wp_if.
  (* Case [n = 0]. *)
  { subst n. list_inv. list.
    wp_op vector.wp_set shadowing: v.
    intro_move_post; eauto using singleton_heap. }
  (* Case [n ≠ 0]. *)
  set (_j := (_parent _n)).
  set (j := parent n).
  assert (isInt _j j) by tc.
  wp_op vector.wp_get introducing: y.
  wp_if.
  (* Subcase: [y ≤ x]. *)
  { wp_op vector.wp_set shadowing: v. list in *.
    intro_move_post; list; eauto using quasi_heap_insert_deep. }
  (* Subcase: [x < y]. *)
  { wp_op vector.wp_set shadowing: v. list in *.
    assert (heap (xs ++ {[y]}))
      by eauto using quasi_heap_move_down.
    assert (dominates_children x j (xs ++ {[y]}))
      by eauto using move_up'_remark.
    wp_op wp_move_up shadowing: v.
    + elim_move_post xs'. intro_move_post.
      (* Permutation. *)
      use_permutation_hypothesis. list.
      rewrite (Permutation_app_comm (_) {[y]}).
      rewrite overwrite_and_compensate by eauto with marble.
      reflexivity. }
Qed.

(* The specification of [insert]. *)

Lemma wp_insert q y ys :
  isQueue q ys →
  (len ys + 1 ≤ max_array_length)%Z →
  wp (insert q y) (λ q, isQueue q (ys ++ {[y]})).
Proof.
  intros. destructQueue xs. lengths. unfold insert.
  wp_op vector.wp_length introducing: _n.
  wp_op vector.wp_reserve shadowing: q.
  wp_op wp_move_up' shadowing: q. wp_last Hpost.
  elim_move_post xs'. list in Hpost0.
  introQueue; eauto 2.
  (* Permutation. *)
  { use_permutation_hypothesis. simplify_list_permutation_goal. eauto. }
Qed.

(* -------------------------------------------------------------------------- *)

(* Extracting an element out of a priority queue: [move_down] and [extract]. *)

Section Code.
Open Scope uint63.

(* [move_down _n v _i x ACC] writes the element [x] into slot [_i],
   then moves it down as far as necessary to restore the heap invariant. *)

(* [move_down] calls itself in three possible situations: 1- there is a
   left child and no right child; 2- there are two children and the left
   child is smaller; 3- there are two children and the right child is
   smaller. In order to avoid duplicating code (and proofs), one could
   introduce an auxiliary function; however, this function would be
   mutually recursive with [move_down], which would make our definitions
   and proofs more complex. Or, one could introduce a [do] construct whose
   body is a conditional; but then, either this conditional would have to
   return a pair, causing an allocation, or a redundant read in the vector
   would be necessary. We avoid all of these problems by duplicating
   (three times) the 5 lines of code that determine whether [x] can settle
   here or should continue to move down. The copies are marked with [BEGIN
   COPY ... END COPY] in the code and in the proof. *)

Fixpoint move_down _n v _i x (ACC : Acc (rigt _n) _i) : vector A :=
  IFC _n / 2 ≤? _i THEN λ _,
    (* There are no children. [x] cannot move further down. *)
    vector.set v _i x
  ELSE λ Hl,
    (* The left child exists. *)
    (* To preserve the heap invariant, the smaller of the two children
       must move up. Let us compute its index [_j]. *)
    IFC (_n - 1) / 2 ≤? _i THEN λ _,
      (* Only the left child exists. Go left. *)
      let _j := _left _i in
      do y ← vector.get v _j ;
      (* BEGIN COPY 1 *)
      if (x ≤? y)%element then
        (* [x] can settle here. *)
        vector.set v _i x
      else
        (* Move [y] up and continue moving [x] down. *)
        do v ← vector.set v _i y ;
        move_down _n v _j x (Acc_inv ACC (rigt_left Hl))
      (* END COPY 1 *)
    ELSE λ Hr,
      (* Both children exist. Compare them. *)
      let _i1 := _left _i in
      let _i2 := _right _i in
      do y1 ← vector.get v _i1 ;
      do y2 ← vector.get v _i2 ;
      if (y1 ≤? y2)%element then
        (* The left child is smaller. Go left. *)
        let _j := _i1 in
        let y := y1 in
        (* BEGIN COPY 2 *)
        if (x ≤? y)%element then
          (* [x] can settle here. *)
          vector.set v _i x
        else
          (* Move [y] up and continue moving [x] down. *)
          do v ← vector.set v _i y ;
          move_down _n v _j x (Acc_inv ACC (rigt_left Hl))
        (* END COPY 2 *)
      else
        let _j := _i2 in
        let y := y2 in
        (* BEGIN COPY 3 *)
        if (x ≤? y)%element then
          (* [x] can settle here. *)
          vector.set v _i x
        else
          (* Move [y] up and continue moving [x] down. *)
          do v ← vector.set v _i y ;
          move_down _n v _j x (Acc_inv ACC (rigt_right Hr))
        (* END COPY 3 *)
.

(* Here are [extract_nonempty] and [extract]. *)

Definition extract_nonempty q : A * queue A :=
  (* Pop the last element [x] of the vector. *)
  do (x, q) ← vector.pop q ;
  do _n ← vector.length q ;
  if _n =? 0 then
    (* [x] was the only element. We are done. *)
    (x, q)
  else
    (* Read the first element [m] of the vector. *)
    (* This is the root of the tree. *)
    do m ← vector.get q 0 ;
    (* Now place [x] at the root of the tree and let it go down. *)
    do q ← move_down _n q 0 x (Wf_rigt _n 0) ;
    (* Return [m] and [q]. *)
    (m, q).

Definition extract q : option (A * queue A) :=
  do _n ← vector.length q ;
  if (_n =? 0) then None else
  do xq ← extract_nonempty q ;
  Some xq.

End Code.

(* The specification of [move_down]. *)

(* TODO *)
Local Lemma le_eq_trans x y z : x ≤ y → y = z → x ≤ z.
Proof. intros. subst. assumption. Qed.
Local Hint Resolve le_eq_trans : order.

(* TODO *)
Lemma qwd (z : Z) : (2 * z) `div` 2 = z.
Proof. lia. Qed.
Hint Rewrite qwd : uz z.



Lemma wp_move_down :
  ∀IntU _n n,
  ∀IntU _i i,
  ∀ v xs x ACC,
  isVector v xs →
  n = len xs →
  valid i xs →
  heap xs →
  ((0 < i)%Z → xs !!! parent i < x) →
  wp (move_down _n v _i x ACC) (λ v, move_post v xs i x).
Proof.
  intros _n n ? ?.
  by well-founded induction on _i along (rigt _n).
  intros. vectors.
  destruct ACC; simpl.
  set (_i1 :=  _left _i).
  set (_i2 := _right _i).
  assert (isInt _i1 (left i)) by tc3.
  assert (isInt _i2 (right i)) by tc3.
  (* Now examine the code. *)
  wp_if.
  (* Case [n / 2 ≤ i]. There are no children. *)
  { wp_op vector.wp_set shadowing: v.
    intro_move_post.
    eapply heap_insert; eauto 3 with marble order. }
  (* Case [i < n / 2]. There is a left child. *)
  (* assert (rigt _n _i1 _i). { unfold rigt, igt. lia. } TODO *)
  wp_if.
  (* Case [(n - 1) / 2 ≤ i]. There is only a left child. *)
  { wp_op vector.wp_get introducing: y.
    (* BEGIN COPY 1 *)
    wp_if.
    (* Case [x ≤ y]. [x] can settle here. *)
    { wp_op vector.wp_set shadowing: v.
      intro_move_post.
      assert (dominates_children x i xs).
      { subst y. split; intro; [ eauto 2 | lia ]. }
      eapply heap_insert; eauto 3 with order. }
    (* Case [y < x]. [y] moves up; [x] continues to move down. *)
    { wp_op vector.wp_set shadowing: v.
      assert (dominates_children y i xs).
      { split; eauto 2 with order lia. }
      assert ((0 < i)%Z → xs !!! parent i ≤ y).
      { intro. eapply grandparent_dominates_grandchild with (j := left i);
        eauto 2 with marble nocore. }
      assert (heap (<[i:=y]> xs)).
      { eapply heap_insert; eauto 2 with lia. }
      wp_op IH shadowing: v. (* UGLY slow, for no reason; related to BUG? *)
      { rewrite lookup_total_insert_eq by assumption. eauto 1. }
      eauto 2 using move_post_insert with marble nocore. }
    (* END COPY 1 *)
  }
  (* Case [i < (n - 1) / 2]. There are two children. *)
  (* assert (rigt _n _i1 _i) by tc3. *) (* TODO *)
  (* assert (rigt _n _i2 _i) by tc3. *)
  wp_op vector.wp_get introducing: y1.
  wp_op vector.wp_get introducing: y2.
  wp_if.
  (* Subcase [y1 ≤ y2]. The left child is smaller. *)
  {
    (* BEGIN COPY 2 *)
    wp_if.
    (* Case [x ≤ y]. [x] can settle here. *)
    { wp_op vector.wp_set shadowing: v.
      intro_move_post.
      assert (dominates_children x i xs).
      { split; eauto 3 with order. }
      eapply heap_insert; eauto 3 with order. }
    (* Case [y < x]. [y] moves up; [x] continues to move down. *)
    { set (y := y1).
      wp_op vector.wp_set shadowing: v.
      assert (dominates_children y i xs) by (split; eauto 2 with order).
      assert ((0 < i)%Z → xs !!! parent i ≤ y).
      { intro. eapply grandparent_dominates_grandchild with (j := left i);
        eauto 2 with marble nocore. }
      assert (heap (<[i:=y]> xs)).
      { eapply heap_insert; eauto 2. }
      wp_op IH shadowing: v. (* UGLY slow again *)
      { rewrite lookup_total_insert_eq by assumption. eauto 1. }
      eauto using move_post_insert with marble nocore. }
    (* END COPY 2 *)
  }
  (* Subcase [y2 < y1]. The right child is smaller. *)
  {
    (* BEGIN COPY 3 *)
    wp_if.
    (* Case [x ≤ y]. [x] can settle here. *)
    { wp_op vector.wp_set shadowing: v.
      intro_move_post.
      assert (dominates_children x i xs).
      { split; eauto 4 with order. }
      eapply heap_insert; eauto 3 with order. }
    (* Case [y < x]. [y] moves up; [x] continues to move down. *)
    { set (y := y2).
      wp_op vector.wp_set shadowing: v.
      assert (dominates_children y i xs) by (split; eauto 3 with order).
      assert ((0 < i)%Z → xs !!! parent i ≤ y).
      { intro. eapply grandparent_dominates_grandchild with (j := right i);
        eauto 2 with marble nocore. }
      assert (heap (<[i:=y]> xs)).
      { eapply heap_insert; eauto 2. }
      wp_op IH shadowing: v. (* UGLY slow again *)
      { rewrite parent_right, lookup_total_insert_eq by assumption.
        eauto 1. }
      eauto using move_post_insert with marble nocore. }
    (* END COPY 3 *)
  }
Qed.

(* The specification of [extract_nonempty]. *)

(* [extract_nonempty] requires the queue to be nonempty
   and extracts a minimal element out of it. *)

Local Notation extract_post x q ys :=
(
  ∃ ys',
  isQueue q ys' ∧
  {[x]} ++ ys' ≃ ys ∧
  {[x]} ≼ ys
).

Local Ltac intro_extract_post :=
  eexists; split; [ introQueue | split ].

Lemma wp_extract_nonempty q ys :
  isQueue q ys →
  ys ≠ [] →
  wp (extract_nonempty q) (λ '(x, q), extract_post x q ys).
Proof.
  intros. destructQueue xs. vectors. lengths.
  unfold extract_nonempty.
  wp_pop x. subst_pop.
  wp_op vector.wp_length introducing: _n.
  wp_if.
  (* Case: [n = 0]. The queue is a singleton. *)
  { list_inv. list in *. wp_ret.
    intro_extract_post; eauto 2 using empty_heap.
    use_permutation_hypothesis. autorewrite with pairwise.
    reflexivity. }
  (* Case: [0 < n]. *)
  wp_op vector.wp_get introducing: m.
  wp_op wp_move_down shadowing: q.
  { eapply heap_pop. eassumption. }
  elim_move_post xs'.
  intro_extract_post; eauto 2; repeat use_permutation_hypothesis.
  (* Permutation. *)
  { eapply overwrite_and_compensate; eauto 1 with lia. }
  (* Minimum. *)
  { eapply heap_minimum; eauto 1 with lia. list. eauto. }
Qed.

(* -------------------------------------------------------------------------- *)

End PQueue.
