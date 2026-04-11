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

(* Assumptions. (Identical to sort.v.) *)

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

Local Notation   left j := (2 * j + 1).
Local Notation  right j := (2 * j + 2).
Local Notation parent i := ((i - 1) / 2).

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

Local Lemma parent_left i : parent (left i) = i.
Proof. lia. Qed.

Local Lemma parent_right i : parent (right i) = i.
Proof. lia. Qed.

Local Hint Rewrite parent_left parent_right : parent.

Local Lemma child_disjunction i :
  i ≠ 0 → i = left (parent i) ∨ i = right (parent i).
Proof. lia. Qed.

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

(* Any sequence of length 1 forms a heap. *)

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
  repeat case_lookup_app.
  { replace n with (left j) by lia.
    autorewrite with parent.
    eauto. }
  { replace n with (right j) by lia.
    autorewrite with parent.
    eauto. }
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

Local Lemma move_up_ilt _i : (_i =? 0) = false → ilt ((_i - 1) / 2) _i.
Proof. eauto with lia. Qed.

Fixpoint move_up v _i x (ACC : Acc ilt _i) : vector.vector A :=
  IFC _i =? 0 THEN λ _,
    vector.set v _i x
  ELSE λ Hi,
    (* [_j] is the parent of [_i]. *)
    let _j := (_i - 1) / 2 in
    (* Read the element [y] in slot [_j]. *)
    do y ← vector.get v _j ;
    if leb y x then
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

(* The postcondition of [move_up]. *)

(* The effect of [move_up] is to write [x] into slot [i] and then permute
   the elements so that they form a heap again. *)

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

(* This is the second specification of [move_up]. If [xs] forms a heap
   and if the vector contains the sequence [xs ++ {[dummy]}] then
   [move_up v _n x] can be called. *)

(* The proof is essentially the same as above, with small changes. *)

Lemma wp_move_up' _n n :
  ∀ v x ACC xs dummy ,
  vector.isVector v (xs ++ {[dummy]}) →
  heap xs →
  isInt _n n →
  n = len xs →
  wp (move_up v _n x ACC) (λ v, move_up_post v (xs ++ {[dummy]}) n x).
Proof.
  intros. vector.vectors. lengths. length in *.
  destruct ACC; simpl.
  wp_if.
  (* Case [n = 0]. *)
  { subst n. list_inv. list.
    wp_op vector.wp_set shadowing: v.
    intro_move_up_post; eauto using singleton_heap. }
  (* Case [n ≠ 0]. *)
  set (_j := ((_n - 1) / 2)%uint63).
  set (j := parent n).
  assert (isInt _j j) by tc.
  wp_op vector.wp_get introducing: y.
  wp_if.
  (* Subcase: [y ≤ x]. *)
  { wp_op vector.wp_set shadowing: v.
    intro_move_up_post; list; eauto using quasi_heap_insert_deep. }
  (* Subcase: [x < y]. *)
  { wp_op vector.wp_set shadowing: v.
    wp_op wp_move_up shadowing: v.
    + (* The first precondition of the recursive call. *)
      eauto using quasi_heap_move_down.
    + (* The second precondition of the recursive call. *)
      destructHeap. subst y.
      split; intros; case_lookup_app; eapply lt_le';
      eapply strict_transitive_l; eauto 2 with lia.
    + elim_move_up_post xs'. intro_move_up_post.
      (* Permutation. *)
      match goal with h: _ ≃ xs' |- _ => rewrite <- h end.
      replace (xs ++ {[y]}) with (<[n := y]>(xs ++ {[dummy]}))
        by (list; eauto).
      rewrite swap_inserts by lia.
      eapply identity_permutation. subst y. lego. }
Qed.

(* The specification of [insert]. *)

Lemma wp_insert q y ys :
  isQueue q ys →
  (len ys + 1 ≤ array.max_array_length)%Z →
  wp (insert q y) (λ q, isQueue q (ys ++ {[y]})).
Proof.
  intros. destructQueue xs. lengths. unfold insert.
  wp_op vector.wp_length introducing: _n.
  wp_op vector.wp_reserve shadowing: q.
  wp_op wp_move_up' shadowing: q. wp_last Hpost.
  elim_move_up_post xs'. list in Hpost0.
  introQueue; eauto 2.
  (* Permutation. *)
  { match goal with h: _ ≃ xs' |- _ => rewrite <- h end.
    simplify_list_permutation_goal. eauto. }
Qed.

(* -------------------------------------------------------------------------- *)

End PQueue.
