From stdpp Require Import list.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

(* currently unused *)
Lemma list_insert_id'' `{Inhabited A} (xs : list A) (i : nat) (x : A) :
  i < length xs →
  xs !!! i = x →
  <[i:=x]>xs = xs.
Proof.
  rewrite <- lookup_lt_is_Some.
  intros Hvalid Hlookup.
  apply list_lookup_lookup_total in Hvalid.
  rewrite list_insert_id by congruence.
  eauto.
Qed.

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

Lemma cons_is_append {A} x (xs : list A) :
  x :: xs = {[x]} ++ xs.
Proof. eauto. Qed.

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

Lemma replicate_is_repeat {A} n (x : list A) :
  replicate n x = List.repeat x n.
Proof.
  revert n. induction n as [| n]; simpl; congruence.
Qed.

Lemma replicate_0 {A} (x : A) :
  replicate 0 x = [].
Proof. eauto. Qed.

Lemma replicate_app_singleton_l {A} n (x : A) :
  {[x]} ++ replicate n x = replicate (n + 1) x.
Proof.
  change {[x]} with [x]. simpl. rewrite <- replicate_S. f_equal. lia.
Qed.

Lemma replicate_app_singleton_r {A} n (x : A) :
  replicate n x ++ {[x]} = replicate (n + 1) x.
Proof.
  change {[x]} with [x]. rewrite <- replicate_S_end. f_equal. lia.
Qed.

Lemma insert_replicate_0 {A} n (x y : A) :
  0 < n →
  <[0:=y]>(replicate n x) = {[y]} ++ replicate (n-1) x.
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

Global Tactic Notation "list" "in" "*" :=
  autorewrite with list in *.

(* A number of arithmetic simplification lemmas can be very useful
   while simplifying expressions that involve lists. *)

Lemma sub_succ (n h : nat) :
  n - (h + 1) = n - h - 1.
Proof. lia. Qed.

Global Hint Rewrite
  <- Nat.add_assoc
: list nat.

Global Hint Rewrite
  Nat.add_0_l
  Nat.add_0_r
  Nat.sub_0_l
  Nat.sub_0_r
  Nat.sub_diag
  Nat.add_simpl_l Nat.add_simpl_r
  sub_succ
: list nat.

Global Hint Rewrite
  <- Nat.le_add_sub
  using (list; lia)
: list nat.

(* Do NOT add [sub_diag'] to the rewrite hint database, because it can
   change an informative equation [x - y = 0] into the uniformative
   equation [0 = 0]. (The equation destroys itself, so to speak.) *)

Lemma sub_diag' (x y : nat) :
  x ≤ y → x - y = 0.
Proof. lia. Qed.

Lemma simpl_sub_add i k delta :
  i ≤ k →
  (k - i) + delta = (k + delta) - i.
Proof. lia. Qed.

Global Hint Rewrite
  Nat.min_l Nat.min_r
  Nat.max_l Nat.max_r
  (* sub_diag' *)
  simpl_sub_add
  using (list; lia)
: list nat.

Lemma abc_minus_c a b c : a + (b + c) - c = a + b.
Proof. lia. Qed.
Lemma ab_minus_cb a b c : a + b - c - b = a - c.
Proof. lia. Qed.

Hint Rewrite abc_minus_c ab_minus_cb : list nat.

Global Hint Rewrite
  @app_nil_l @app_nil_r
  @replicate_0
  @replicate_app_singleton_l
  @replicate_app_singleton_r
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
  @lookup_total_app_l
  @lookup_total_app_r
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

Lemma length_equality {A} (xs ys : list A) :
  xs = ys →
  length xs = length ys.
Proof.
  congruence.
Qed.

(* The tactic [lengths] searches for hypotheses of the form [xs = ys] or
   [xs `prefix_of` ys] and introduces new facts [length xs = length ys]
   or [length xs ≤ length ys]. These new facts are then simplified using
   the tactic [list]. *)

Global Ltac lengths :=
  repeat
    match goal with
    | h: _ = _ |- _ =>
        let h' := fresh h in
        generalize h; revert h; intro h';
        apply length_equality in h';
        list in h'
    | h: _ `prefix_of` _ |- _ =>
        let h' := fresh h in
        generalize h; revert h; intro h';
        apply prefix_length in h';
        list in h'
    | h: _ |- _ =>
        revert h
    end;
  intros.

(* Extensional equality of lists. *)

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

Lemma seg_overshoot {A} i j (xs : list A) : length xs ≤ i → seg i j xs = [].
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

(* [length_seg'] is simpler but weaker. *)

Lemma length_seg {A} i j (xs : list A) :
  length (seg i j xs) = (j `min` length xs) - i.
Proof. intros. unfold seg. list. lia. Qed.

Lemma length_seg' {A} i j (xs : list A) :
  valid_seg i j xs →
  length (seg i j xs) = j - i.
Proof. intros. rewrite length_seg. lia. Qed.

(* Interaction of [lookup] and [seg]. *)

(* [valid_seg i j xs ∧ k < j - i] are sufficient conditions,
   but they are too strong. *)

Lemma lookup_seg {A} i j (xs : list A) k :
  valid k (seg i j xs) →
  seg i j xs !! k = xs !! (i + k).
Proof.
  rewrite length_seg. intros. unfold seg. list. eauto.
Qed.

(* Interaction of [lookup_total] and [seg]. *)

Lemma lookup_total_seg `{Inhabited A} i j (xs : list A) k :
  valid k (seg i j xs) →
  seg i j xs !!! k = xs !!! (i + k).
Proof.
  intros. rewrite !list_lookup_total_alt, lookup_seg by eauto. eauto.
Qed.

Global Hint Rewrite
  @length_seg
  @lookup_seg
  @lookup_total_seg
  @seg_none
  @seg_none'
  @seg_overshoot
  @seg_all
  using (list; lia)
: list.

(* Interaction of [lookup] and [seg], in reverse. *)

(* If a segment of [xs] is known under the name [ys], and if index [k]
   falls within this segment, then the lookup [xs !! k] can be viewed
   as a lookup into [ys]. *)

(* This lemma is not made a rewrite hint because 1- [autorewrite]
   seems unable to exploit it, and 2- it is perhaps not clear that
   this would be a good idea. *)

Lemma lookup_through_seg {A} i j k (xs ys : list A) :
  seg i j xs = ys →
  i ≤ k →
  k < j `min` length xs →
  xs !! k = ys !! (k - i).
Proof.
  intros. subst. list. eauto.
Qed.

(* Interaction of [lookup_total] and [seg], in reverse. *)

Lemma lookup_total_through_seg `{Inhabited A} i j k (xs ys : list A) :
  seg i j xs = ys →
  i ≤ k →
  k < j `min` length xs →
  xs !!! k = ys !!! (k - i).
Proof.
  intros. subst. list. eauto.
Qed.

(* A segment can be split anywhere. *)

Lemma split_seg {A} j (xs : list A) i k :
  valid_seg i j xs →
  valid_seg j k xs →
  seg i k xs = seg i j xs ++ seg j k xs.
Proof.
  intros. listx o. lookup_app_split. f_equal. lia.
Qed.

(* A singleton segment is a singleton. *)

Lemma seg_is_singleton `{Inhabited A} (xs : list A) i j :
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

(* Splitting off a singleton. *)

Lemma split_seg_singleton_l `{Inhabited A} (xs : list A) i k :
  valid_seg i k xs →
  i < k →
  seg i k xs = {[ xs !!! i ]} ++ seg (i + 1) k xs.
Proof.
  intros.
  rewrite (split_seg (i + 1) xs) by lia.
  rewrite singleton_is_seg by lia.
  eauto.
Qed.

Lemma split_seg_singleton_r `{Inhabited A} (xs : list A) i k :
  valid_seg i k xs →
  i < k →
  seg i k xs = seg i (k-1) xs ++ {[ xs !!! (k-1) ]}.
Proof.
  intros.
  rewrite (split_seg (k-1) xs) by lia.
  rewrite singleton_is_seg by lia.
  list. eauto.
Qed.

Lemma split_seg_singleton_r' `{Inhabited A} (xs : list A) i k :
  valid_seg i k xs →
  valid k xs →
  seg i (k+1) xs = seg i k xs ++ {[ xs !!! k ]}.
Proof.
  intros.
  rewrite (split_seg k xs) by lia.
  rewrite singleton_is_seg by lia.
  eauto.
Qed.

(* Automatic recognition of singleton segments
   and automatic joining of adjacent segments. *)

(* Unfortunately, automatic joining of adjacent segments often requires
   reasoning up to associativity of [++], so the tactic [list] will miss
   some opportunities. Manual rewriting using [aac_rewrite <- split_seg]
   may be necessary. *)

(* As a poor man's approach, see [simplify_list_equality_goal] further on. *)

(* It is unclear whether we want to transform singleton segments into
   singletons, or vice-versa. Our current choice is to transform
   singletons into singleton segments, in the hope of enabling fusions
   between segments. *)

Global Hint Rewrite
  @singleton_is_seg
  using (list; lia)
: list.

Global Hint Rewrite
  <- @split_seg
  using (list; lia)
: list.
  (* TODO recognizing a fusion opportunity may require rewriting
          modulo associativity *)

(* Interaction of [seg] and [app]. *)

Lemma seg_app {A} i j (xs ys : list A) :
  seg i j (xs ++ ys) =
    seg i j xs ++ seg (i - length xs) (j - length xs) ys.
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
  intros. listx o. lookup_app_split.
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

Lemma insert_seg {A} i j k x (xs : list A) :
  valid_seg i j xs →
  valid k (seg i j xs) →
  <[k := x]> (seg i j xs) =
  seg i (i + k) xs ++ {[x]} ++ seg (i + k + 1) j xs.
Proof.
  list. intros. listx o. do 2 lookup_app_split.
Qed.

Global Hint Rewrite
  @insert_seg_first
  @insert_seg_last
  (* TODO @insert_seg *)
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
  + rewrite sub_diag' by lia. list. eauto.
Qed.

(* Interaction of [seg] with itself. *)

(* [seg_seg'] is simpler but weaker. *)

Lemma seg_seg' {A} i j k l (xs : list A) :
  valid_seg k l xs →
  i ≤ j ≤ l - k → (* valid_seg i j (seg k l xs) *)
  seg i j (seg k l xs) =
  seg (k + i) (k + j) xs.
Proof.
  intros. listx o. list. eauto.
Qed.

Lemma seg_seg {A} i j k l (xs : list A) :
  seg i j (seg k l xs) =
  seg (k + (i `min` (l - k))) (k + (j `min` (l - k))) xs.
Proof.
  intros. listx o. list. eauto. (* nice! *)
Qed.

Global Hint Rewrite
  @seg_replicate
  @seg_seg
  using (list; lia)
: list.

(* If a segment of [xs] is known under the name [ys],
   then an attempt to extract a smaller segment of [xs]
   can be viewed as an attempt to extract a segment of [ys]. *)

(* This lemma is not made a rewrite hint because 1- [autorewrite]
   seems unable to exploit it, and 2- it is perhaps not clear that
   this would be a good idea. *)

Lemma seg_through_seg {A} i j k l (xs ys : list A) :
  seg i j xs = ys →
  i ≤ k → l ≤ j →
  seg k l xs = seg (k - i) (l - i) ys.
Proof.
  intros. subst. list. listx o. list. eauto. (* wow *)
Qed.

(* The tactic [split_seg j xs] splits a list [xs] or a list segment
   [seg i k xs] at index [j]. *)
(* TODO this may not work / will not work if there are multiple
        occurrences of [xs] in the goal *)

Global Ltac split_seg j xs :=
  first [
    (* case: [xs] is already a segment *)
    rewrite (split_seg j xs) by (list; lia)
  | (* case: introduce a list segment first *)
    rewrite (seg_intro xs);
    rewrite (split_seg j xs) by (list; lia)
  ].

(* The tactic [split_seg_singleton_l xs] splits off the first element
   of a nonempty segment of the form [seg i k xs]. *)

Global Ltac split_seg_singleton_l xs :=
  erewrite (split_seg_singleton_l xs) by lia;
  autorewrite with nat.
    (* We do not use [list] because it would undo the splitting. *)

(* The tactic [split_seg_singleton_r xs] splits off the last element
   of a nonempty segment of the form [seg i k xs]. *)

Global Ltac split_seg_singleton_r xs :=
  erewrite (split_seg_singleton_r xs) by lia;
  autorewrite with nat.
    (* We do not use [list] because it would undo the splitting. *)

(* Some properties of empty segments. *)

Lemma empty_seg_iff {A} i j (xs : list A) :
  seg i j xs = [] ↔ j `min` length xs ≤ i.
Proof.
  intros. rewrite <- length_zero_iff_nil. list. lia.
Qed.

Lemma invert_empty_seg {A} i j (xs : list A) :
  seg i j xs = [] →
  valid_seg i j xs →
  i = j.
Proof.
  intros Hseg ?. rewrite empty_seg_iff in Hseg by eauto. lia.
Qed.

Lemma invert_nonempty_seg {A} i j (xs : list A) :
  seg i j xs ≠ [] →
  valid_seg i j xs →
  i < j.
Proof.
  intros Hseg ?. rewrite empty_seg_iff in Hseg by eauto. lia.
Qed.

(* If certain two list segments are known to be equal, then two smaller
   segments must be equal as well. *)

Lemma seg_equality_implication {A} i1 j1 i2 j2 i'1 j'1 i'2 j'2 (xs1 xs2 : list A) :
  seg i1 j1 xs1 = seg i2 j2 xs2 →
  valid_seg i1 j1 xs1 →
  valid_seg i2 j2 xs2 →
  i1 ≤ i'1 ≤ j'1 ≤ j1 →
  i2 ≤ i'2 ≤ j'2 ≤ j2 →
  i'2 - i2 = i'1 - i1 →
  j'2 - i2 = j'1 - i1 →
  seg i'1 j'1 xs1 = seg i'2 j'2 xs2.
Proof.
  intros.
  replace (seg i'1 j'1 xs1) with
          (seg (i'1 - i1) (j'1 - i1) (seg i1 j1 xs1))
  by (list; eauto).
  replace (seg i'2 j'2 xs2) with
          (seg (i'2 - i2) (j'2 - i2) (seg i2 j2 xs2))
  by (list; eauto).
  congruence.
Qed.

(* -------------------------------------------------------------------------- *)

(* We define [sublist i n xs] as the segment of the list [xs]
   whose start index is [i] and whose length is [n]. *)

Definition sublist {A} i n (xs : list A) :=
  seg i (i + n) xs.

Lemma sublist_take_drop {A} i n (xs : list A) :
  sublist i n xs = take n (drop i xs).
Proof.
  intros. unfold sublist, seg. list. eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* [simplify_list_equality_goal] simplifies a goal of the form [xs = ys].
   To compensate for the lack of rewriting modulo associativity, we first
   identify and eliminate identical terms on the left-hand side and on the
   right-hand side; then we attempt to fuse adjacent list segments. *)

(* This tactic cannot fail, and does not solve the goal. *)

(* The goal should be rigid. If it contains metavariables at either end
   then they may be instantiated in incorrect ways. *)

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
  list.

(* [simplify_list_permutation_goal] simplies a goal of the form [xs π ys],
   that is, an obligation to prove that the lists [xs] and [ys] are equal
   up to a permutation of their elements. *)

(* We do not use the tactic [list] because it fuses adjacent segments,
   which, in a permutation goal, can be counter-productive. *)

Ltac simplify_list_permutation_goal :=
  autorewrite with nat;
  repeat rewrite app_assoc;
  repeat eapply Permutation_app_tail;
  repeat rewrite <- app_assoc;
  repeat eapply Permutation_app_head.

(* -------------------------------------------------------------------------- *)

Lemma Forall2_lookup_total `{Inhabited A} P (xs ys : list A) :
  Forall2 P xs ys ↔
    length xs = length ys ∧
    ∀ i, i < length xs → P (xs !!! i) (ys !!! i).
Proof.
  split.
  + revert xs ys. induction 1; simpl.
    - eauto with lia.
    - destruct IHForall2.
      split; [ eauto with lia | intros i ? ].
      case (decide (i = 0)); intros; [| replace i with ((i - 1) + 1) by lia ];
      list; eauto with lia.
  + revert xs ys. induction xs as [| x xs]; intros ys Hyp;
    destruct ys as [| y ys ]; list in Hyp; try lia.
    - constructor.
    - destruct Hyp as [ ? Hyp ].
      constructor.
      * specialize (Hyp 0). list in Hyp. eauto with lia.
      * eapply IHxs. split; [ lia |]. intros i ?.
        specialize (Hyp (S i)). list in Hyp. eauto with lia.
Qed.

(* The following instances allow the tactic [isBool] to exploit
   the previous result to establish [isBool _ (Forall2 _ _ _)]. *)

From marble Require Import bool.

Global Instance isBool1_true_Forall2 `{Inhabited A} P (xs ys : list A) :
  length xs = length ys →
  (∀ i, valid i xs → P (xs !!! i) (ys !!! i)) →
  isBool1 true (Forall2 P xs ys).
Proof.
  intros. eapply isBool_intro_true. rewrite Forall2_lookup_total. firstorder.
Qed.

Global Instance isBool1_false_Forall2_witness `{Inhabited A} P (xs ys : list A) :
  ∀ i,
  valid i xs →
  valid i ys →
  ¬ P (xs !!! i) (ys !!! i) →
  isBool1 false (Forall2 P xs ys).
Proof.
  intros. eapply isBool_intro_false. rewrite Forall2_lookup_total. firstorder.
Qed.

Global Instance isBool1_false_Forall2_lengths `{Inhabited A} P (xs ys : list A) :
  length xs ≠ length ys →
  isBool1 false (Forall2 P xs ys).
Proof.
  intros. eapply isBool_intro_false. rewrite Forall2_lookup_total. firstorder.
Qed.
