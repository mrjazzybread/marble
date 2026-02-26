From stdpp Require Import list.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

Lemma list_lookup_insert_eq' {A} (xs : list A) i j x :
  i = j →
  i < length xs →
  <[i:=x]>xs !! j = Some x.
Proof.
  intros. subst. rewrite list_lookup_insert_eq by eauto. eauto.
Qed.

Lemma list_lookup_total_insert_eq' `{Inhabited A} (xs : list A) i j x :
  i = j →
  i < length xs →
  <[i:=x]>xs !!! j = x.
Proof.
  intros. subst. rewrite list_lookup_total_insert_eq by eauto. eauto.
Qed.

Global Instance singleton_list {A} : Singleton A (list A) :=
  λ x, [x].

Lemma length_singleton {A} (x : A) : length {[x]} = 1.
Proof. reflexivity. Qed.

Lemma lookup_singleton_eq_0 {A} i (x : A) :
  i = 0 →
  ({[x]} : list A) !! i = Some x.
Proof.
  intros. subst. reflexivity.
Qed.

Lemma lookup_total_singleton_eq_0 `{Inhabited A} i (x : A) :
  i = 0 →
  ({[x]} : list A) !!! i = x.
Proof.
  intros. subst. reflexivity.
Qed.

Lemma lookup_app' {A} (xs ys : list A) i :
  (xs ++ ys) !! i =
    if decide (i < length xs) then xs !! i
    else ys !! (i - length xs).
Proof.
  intros. case_decide.
  - rewrite lookup_app_l by lia. eauto.
  - rewrite lookup_app_r by lia. eauto.
Qed.

Lemma lookup_total_cons_eq_0 `{!Inhabited A} (xs : list A) x i :
  i = 0 → (x :: xs) !!! i = x.
Proof. intros ->. reflexivity. Qed.

(* A variant of the lemma [drop_S]. *)

Lemma drop_S' `{Inhabited A} (xs : list A) (x : A) (i : nat) :
  i < List.length xs →
  x = xs !!! i →
  x :: drop (i + 1) xs = drop i xs.
Proof.
  intros. subst.
  replace (i + 1) with (S i) by lia.
  rewrite <- drop_S by eauto using list_lookup_lookup_total_lt with lia.
  eauto.
Qed.

Lemma replicate_is_repeat {A} n (x : list A) :
  replicate n x = List.repeat x n.
Proof.
  revert n. induction n as [| n]; simpl; congruence.
Qed.

Lemma replicate_0 {A} (x : A) :
  replicate 0 x = [].
Proof. eauto. Qed.

Lemma expand_replicate {A} n (x : A) :
  0 < n →
  replicate n x = x :: replicate (n-1) x.
Proof.
  intros. destruct n as [| n]; [ lia |].
  rewrite replicate_S. do 2 f_equal. lia.
Qed.

Lemma insert_replicate_0 {A} n (x y : A) :
  0 < n →
  <[0:=y]>(replicate n x) = [y] ++ replicate (n-1) x.
Proof.
  intros. rewrite insert_replicate_lt by eauto.
  rewrite app_nil_l. eauto.
Qed.

(* The tactics [list] and [list in h] perform simplification
   (via rewriting) in the goal or in a hypothesis. *)

Global Ltac list :=
  autorewrite with list.

Global Tactic Notation "list" "in" hyp(h) :=
  autorewrite with list in h.

(* A number of arithmetic simplification lemmas can be very useful
   while simplifying expressions that involve lists. *)

Lemma sub_succ (n h : nat) :
  n - (h + 1) = n - h - 1.
Proof. lia. Qed.

Global Hint Rewrite
  <- Nat.add_assoc
: list.

Global Hint Rewrite
  Nat.add_0_l
  Nat.add_0_r
  Nat.sub_0_l
  Nat.sub_0_r
  Nat.sub_diag
  Nat.add_simpl_l Nat.add_simpl_r
  sub_succ
: list.

Lemma sub_diag' (x y : nat) :
  x ≤ y → x - y = 0.
Proof. lia. Qed.

Lemma simpl_sub_add i k delta :
  i ≤ k →
  (k - i) + delta = (k + delta) - i.
Proof. lia. Qed.

Global Hint Rewrite
  Nat.max_l Nat.max_r
  sub_diag'
  simpl_sub_add
  using (list; lia)
: list.

Global Hint Rewrite
  @app_nil_l @app_nil_r
  @replicate_0
  @length_nil
  @length_cons
  @length_singleton
  @length_app
  @length_insert
  @length_replicate
  @length_take
  @length_drop
: list.

Global Hint Rewrite
  <- @app_assoc
: list.

Global Hint Extern 1 (_ < length _) => (list; lia) : lia.

Global Hint Rewrite
  @lookup_total_cons_eq_0
  @lookup_total_cons_ne_0
  @list_lookup_insert_eq'
  @list_lookup_total_insert_eq'
  @list_lookup_insert_ne
  @list_lookup_total_insert_ne
  @lookup_replicate_2
  @lookup_total_replicate_2
  using (list; lia)
: list.

Global Hint Rewrite
  @insert_app_l
  @insert_app_r_alt
  @insert_replicate_0
  @take_app
  @drop_app
  using (list; lia)
: list.

Lemma take_0' {A} n (xs : list A) :
  n = 0 →
  take n xs = [].
Proof.
  intros. subst. apply take_0.
Qed.

Lemma drop_0' {A} n (xs : list A) :
  n = 0 →
  drop n xs = xs.
Proof.
  intros. subst. apply drop_0.
Qed.

Global Hint Rewrite
  @take_0'
  @take_nil
  @take_ge
  @drop_0'
  @drop_ge
  @lookup_singleton_eq_0
  @lookup_total_singleton_eq_0
  @lookup_take_lt
  @lookup_drop
  using (list; lia)
: list.

(* The tactic [apply_prefix_length] searches for a hypothesis of the form
   [xs `prefix_of` ys] and introduces a new fact [length xs ≤ length ys].
   This new fact is then simplified using the tactic [list]. *)

Global Ltac apply_prefix_length :=
  match goal with h: _ `prefix_of` _ |- _ =>
    generalize h;
    let h' := fresh h in
    intro h'; apply prefix_length in h';
    list in h'
  end.

Lemma list_eq_same_length' {A} (xs ys : list A) :
  length xs = length ys →
  (∀ i, i < length xs → xs !! i = ys !! i) →
  xs = ys.
Proof.
  intros.
  apply list_eq_same_length with (n := length xs); eauto 1.
  intros i x y Hi Hxs Hys.
  cut (xs !! i = ys !! i). { congruence. } clear Hxs Hys.
  eauto.
Qed.

Lemma list_eq_same_length'_total `{Inhabited A} (xs ys : list A) :
  length xs = length ys →
  (∀ i, i < length xs → xs !!! i = ys !!! i) →
  xs = ys.
Proof.
  intros. apply list_eq_same_length'; [ eauto | intros ].
  rewrite !list_lookup_lookup_total_lt by lia.
  f_equal. eauto.
Qed.

(* The tactic [listx i] proves that two lists are equal by checking that
   they are extensionally equal: same length and same elements.
   The parameter [i] is the name of the index that is looked up. *)

Global Ltac listx i :=
  eapply list_eq_same_length'; list; [ eauto with lia | intros i ? ].

Global Ltac listx_total i :=
  eapply list_eq_same_length'_total; list; [ eauto with lia | intros i ? ].

(* The tactic [lookup_insert_split] performs a case split in a situation where
   the goal contains a lookup in an update [<[i:=x]>xs !! j]. *)

Global Ltac lookup_insert_split :=
  rewrite list_lookup_insert; list; case_decide; list; eauto 2.

(* The tactic [lookup_app_split] performs a case split in a situation where
   the goal contains a lookup in a concatenation [(xs ++ ys) !! i]. *)

Global Ltac lookup_app_split :=
  rewrite lookup_app'; list; case_decide; list; eauto 2.

(* -------------------------------------------------------------------------- *)

(* List segments. *)

(* We define [seg i j] as the list segment whose start and end indices
   are [i] and [j]. As usual, this is a semi-open interval. *)

Definition seg {A} i j (xs : list A) : list A :=
  take (j - i) (drop i xs).

(* The following short-hands help recognize an initial segment
   or a final segment of a list. *)

Global Notation initial_seg i xs :=
  (seg 0 i xs).

Global Notation final_seg j xs :=
  (seg j (length xs) xs).

(* [valid_seg i j xs] means that [i] and [j] delimit a valid segment
   of the list [xs]. *)

Global Notation valid_seg i j xs :=
  (i ≤ j ≤ length xs).

(* [valid i xs] means that [i] is a valid index into the list [xs].
   In other words, this index can be used for reading or updating
   one element; it is the start index of a valid segment of length 1. *)

Global Notation valid i xs :=
  (i < length xs).

Lemma valid_valid_seg {A} i (xs : list A) :
  valid i xs ↔ valid_seg i (i+1) xs.
Proof. lia. Qed.

(* [clip k i j] forces the index [k] into the semi-open interval [i, j). *)

Global Notation clip k i j :=
  ((k `max` i) `min` j).

(* Interaction of [drop] and [clip]. *)

Lemma drop_clip {A} n (xs : list A) :
  drop (clip n 0 (length xs)) xs = drop n xs.
Proof.
  assert (n ≤ length xs ∨ length xs ≤ n) as [|] by lia.
  + f_equal. lia.
  + list. eauto.
Qed.

(* [take] and [drop] are special cases of [seg]. *)

Lemma take_seg {A} n (xs : list A) : take n xs = initial_seg n xs.
Proof. unfold seg. list. eauto. Qed.

Lemma drop_seg {A} n (xs : list A) : drop n xs = final_seg n xs.
Proof. unfold seg. listx j. eauto. Qed.

(* An empty segment and a complete segment can be simplified away. *)

Lemma seg_none {A} i (xs : list A) : seg i i xs = [].
Proof. intros. unfold seg. list. eauto. Qed.

Lemma seg_none' {A} i j (xs : list A) : j ≤ i → seg i j xs = [].
Proof. intros. unfold seg. list. eauto. Qed.

Lemma seg_all {A} i j (xs : list A) : i ≤ 0 → length xs ≤ j → seg i j xs = xs.
Proof. intros. unfold seg. list. eauto. Qed.

(* In the reverse direction, a list can be viewed as a list segment. *)

Lemma seg_intro {A} (xs : list A) : xs = final_seg 0 xs.
Proof. rewrite seg_all by lia. eauto. Qed.

(* Any segment is equal to a valid segment. *)

Lemma seg_valid {A} i j (xs : list A) :
  seg i j xs =
    let i := clip i 0 (length xs) in
    let j := clip j i (length xs) in
    seg i j xs.
Proof.
  unfold seg. listx k. rewrite drop_clip. list. eauto.
Qed.

Goal forall {A} i j (xs : list A),
  let i := clip i 0 (length xs) in
  let j := clip j i (length xs) in
  valid_seg i j xs.
Proof. lia. Qed.

(* Interaction of [length] and [seg]. *)

Lemma length_seg {A} i j (xs : list A) :
  length (seg i j xs) = (j `min` length xs) - i.
Proof. intros. unfold seg. list. lia. Qed.

Lemma length_seg' {A} i j (xs : list A) :
  valid_seg i j xs →
  length (seg i j xs) = j - i.
Proof. intros. rewrite length_seg. lia. Qed.

(* Interaction of [lookup] and [seg]. *)

Lemma lookup_seg {A} i j (xs : list A) k :
  valid_seg i j xs →
  k < j - i →
  seg i j xs !! k = xs !! (i + k).
Proof. intros. unfold seg. list. eauto. Qed.

(* Interaction of [lookup_total] and [seg]. *)

Lemma lookup_total_seg `{Inhabited A} i j (xs : list A) k :
  valid_seg i j xs →
  k < j - i →
  seg i j xs !!! k = xs !!! (i + k).
Proof.
  intros. rewrite !list_lookup_total_alt, lookup_seg by eauto. eauto.
Qed.

Global Hint Rewrite
  @length_seg'
  @lookup_seg
  @lookup_total_seg
  @seg_none
  @seg_none'
  @seg_all
  using (list; lia)
: list.

(* A segment can be split anywhere. *)

Lemma split_seg {A} j (xs : list A) i k :
  valid_seg i j xs →
  valid_seg j k xs →
  seg i k xs = seg i j xs ++ seg j k xs.
Proof.
  intros. listx o. lookup_app_split. f_equal. lia.
Qed.

(* A singleton segment is a singleton. *)

Lemma seg_is_singleton `{Inhabited A} i j (xs : list A) :
  valid i xs →
  i + 1 = j →
  seg i j xs = {[xs !!! i]}.
Proof.
  intros. subst. listx_total k. assert (k = 0) by lia. subst. list. eauto.
Qed.

Lemma singleton_is_seg `{Inhabited A} i (xs : list A) :
  valid i xs →
  {[xs !!! i]} = seg i (i+1) xs.
Proof.
  intros. rewrite seg_is_singleton by eauto. eauto.
Qed.

(* Automatic recognition of singleton segments
   and automatic joining of adjacent segments. *)

(* Unfortunately, automatic joining of adjacent segments often requires
   reasoning up to associativity of [++], so the tactic [list] will miss
   some opportunities. Manual rewriting using [aac_rewrite <- split_seg]
   may be necessary. *)

(* As a poor man's approach, see [simplify_list_equality_goal] further on. *)

(* TODO do we want this?  *)

Global Hint Rewrite
  @singleton_is_seg
  using (list; lia)
: list.

Global Hint Rewrite
  <- @split_seg
  using (list; lia)
: list.

(* Interaction of [seg] and [app]. *)

Lemma seg_app {A} i j (xs ys : list A) :
  seg i j (xs ++ ys) =
    let n := length xs in
    seg i j xs ++ seg (i - n) (j - n) ys.
Proof.
  intros. unfold seg. list. f_equal. listx k. list. eauto. (* yes! *)
  (* This is just as good as an SMT solver...! *)
Qed.

Global Hint Rewrite
  @seg_app
  using (list; lia)
: list.

(* Interaction of [seg] and [insert]. *)

(* Taking a segment out of the result of an update. *)

Lemma seg_insert_outside {A} (xs : list A) i j k x :
  valid_seg i j xs →
  ¬ (i ≤ k < j) →
  seg i j (<[k:=x]>xs) = seg i j xs.
Proof.
  intros. listx o. list. eauto.
Qed.

Lemma seg_insert_inside {A} (xs : list A) i j k x :
  valid_seg i j xs →
  i ≤ k < j →
  seg i j (<[k:=x]>xs) = <[k-i:=x]>(seg i j xs).
Proof.
  intros. listx o. list. lookup_insert_split.
Qed.

Lemma seg_insert {A} (xs : list A) i j k x :
  valid_seg i j xs →
  seg i j (<[k:=x]>xs) =
    if decide (i ≤ k < j) then <[k-i:=x]>(seg i j xs)
    else seg i j xs.
Proof.
  intros. case_decide; eauto using seg_insert_inside, seg_insert_outside.
Qed.

Global Hint Rewrite
  @seg_insert_inside
  @seg_insert_outside
  using (list; lia)
: list.

(* Updating a segment. *)

Lemma insert_seg_first {A} i j x (xs : list A) :
  valid_seg i j xs →
  i < j →
  <[0 := x]> (seg i j xs) =
  {[x]} ++ seg (i+1) j xs.
Proof.
  intros. listx o. lookup_app_split. f_equal. lia.
Qed.

Lemma insert_seg_last {A} i j k x (xs : list A) :
  valid_seg i j xs →
  i < j →
  k = j - i - 1 →
  <[k := x]> (seg i j xs) =
  seg i (j - 1) xs ++ {[x]}.
Proof.
  intros. listx o. lookup_app_split.
Qed.

Global Hint Rewrite
  @insert_seg_first
  @insert_seg_last
  using (list; lia)
: list.

(* Interaction of [seg] and [replicate]. *)

Lemma seg_replicate {A} n i j (x : A) :
  j ≤ n →
  seg i j (replicate n x) = replicate (j - i) x.
Proof.
  intros.
  assert (i ≤ j ∨ j < i) as [|] by lia.
  + listx k. list. eauto.
  + list. eauto.
Qed.

(* Interaction of [seg] with itself. *)

Lemma seg_seg {A} i j k l (xs : list A) :
  valid_seg k l xs →
  i ≤ j ≤ l - k → (* valid_seg i j (seg k l xs) *)
  seg i j (seg k l xs) =
  seg (k + i) (k + j) xs.
Proof.
  intros. listx o. list. eauto.
Qed.

Global Hint Rewrite
  @seg_replicate
  @seg_seg
  using (list; lia)
: list.

(* The tactic [split_seg j xs] splits a list [xs] or a list segment
   [seg i k xs] at index [j]. *)

Global Ltac split_seg j xs :=
  first [
    (* case: [xs] is already a segment *)
    rewrite (split_seg j xs) by (list; lia)
  | (* case: introduce a list segment first *)
    rewrite (seg_intro xs); list;
    rewrite (split_seg j xs) by (list; lia)
  ];
  list.

(* -------------------------------------------------------------------------- *)

(* We define [sub i n xs] as the segment of the list [xs] whose start
   index is [i] and whose length is [n]. *)

Global Notation sub i n xs :=
  (seg i (i + n) xs).

Lemma sub_take_drop {A} i n (xs : list A) :
  sub i n xs = take n (drop i xs).
Proof.
  intros. unfold seg. f_equal. lia.
Qed.

(* -------------------------------------------------------------------------- *)

(* [simplify_list_equality_goal] simplifies a goal of the form [xs = ys].
   To compensate for the lack of rewriting modulo associativity, we first
   identify and eliminate identical terms on the left-hand side and on the
   right-hand side; then we attempt to fuse adjacent list segments. *)

(* This tactic cannot fail, and does not solve the goal. *)

Lemma simplify_app_l {A} (xs ys zs : list A) :
  ys = zs → xs ++ ys = xs ++ zs.
Proof. congruence. Qed.

Lemma simplify_app_r {A} (xs ys zs : list A) :
  ys = zs → ys ++ xs = zs ++ xs.
Proof. congruence. Qed.

Global Ltac simplify_list_equality_goal :=
  list;
  repeat rewrite app_assoc;
  repeat eapply simplify_app_r;
  repeat rewrite <- app_assoc;
  repeat eapply simplify_app_l;
  repeat rewrite <- @split_seg by lia.
