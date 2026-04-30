From stdpp Require Import numbers list gmap.
From listz Require Import listz.
Notation len := length.
From Stdlib Require Import Uint63.
From Stdlib Require Import Array.PArray.
From marble Require Import tactics bool int iteration loop wp logic array.
Implicit Types _i _j _k _n : int.
From Corelib Require Derive.

(* Type of keys *)
Parameter K : Type.

(* Type of values. *)
Parameter V : Type.

(* Hash function. *)
Parameter _hash : K -> int.
Parameter hash : K -> Z.

Axiom hash_unsigned :
  forall k, unsigned (hash k).

Local Hint Resolve hash_unsigned : marble.

Declare Instance IsInt_hash :
  forall k, isInt (_hash k) (hash k).

(* Decidable equality over keys. *)
Global Declare Instance EqK : EqDecision K.
Open Scope uint63.

(* Hash tables are arrays of buckets.  A bucket is an association list
   of keys to values.  Keys may appear more than once in the same
   bucket but can never belong to two buckets simultaneously. *)
Definition bucket := (list (K * V)).
Definition hashtbl := array bucket.

(* Function that calculates the index of a particular key using
[hash].  In machine integers and ideal integers. *)

Notation index k len :=
  ((_hash k) mod len).

Notation indexZ k len := (hash k mod len)%Z.

(* Filters a bucket leaving only pairings whose key is [k]. *)
Notation filter_key k l :=
  (base.filter (fun (x: K * V) => let (k', _) := x in k' = k) l).

(* Trivial lemmas to automate rewriting goals involving    [filter_key]*)

Lemma filter_key_cons_True :
  forall k v b, filter_key k ((k, v) :: b) = (k, v) :: filter_key k b.
Proof.
  intros.
  by apply filter_cons_True.
Qed.

Lemma filter_key_cons_False :
  forall k k' v b,
    k' ≠ k ->
    filter_key k ((k', v) :: b) = filter_key k b.
Proof.
  intros.
  unfold filter_key. by apply filter_cons_False.
Qed.

Hint Rewrite
  @filter_nil
  filter_key_cons_False
  filter_key_cons_True
  using auto : cfilter.

Ltac filter := autorewrite with cfilter.

(* Association lists *)

Fixpoint remove_assoc (k : K) (b : bucket) :=
  match b with
  |[] => []
  |(x, v) :: t =>
     if decide (x = k) then t else
       (x, v) :: remove_assoc k t
  end.

Lemma remove_assoc_in :
  forall b k k' v,
    (k', v) ∈ remove_assoc k b ->
    (k', v) ∈ b.
Proof.
  intros b k k' v H1.
  induction b as [|[k'' v'] t Ih]; simpl in H1.
  + apply not_elem_of_nil in H1. contradiction.
  + destruct decide in H1; apply elem_of_cons. auto.
   apply elem_of_cons in H1 as [H1 | H1].
   auto. right. by apply Ih.
Qed.

Lemma remove_assoc_bucket_eq :
  forall k b b',
    b' = remove_assoc k b ->
    filter_key k b' = tl (filter_key k b).
Proof.
  intros k b.
  induction b as [|[k' v] t Ih]; simpl; intros; subst b'.
  - auto.
  - case_decide.
    + subst. filter. by simpl.
    + filter. auto.
Qed.

Lemma filter_key_cons :
  forall k k' v b1 b2,
    filter_key k b1 = filter_key k b2 ->
    filter_key k ((k', v)::b1) = filter_key k ((k', v) :: b2).
Proof.
  intros.
  destruct (decide (k = k')).
  + subst. do 2 rewrite filter_key_cons_True. by f_equal.
  + by do 2 rewrite filter_key_cons_False by auto.
Qed.

Lemma remove_assoc_bucket_ne :
  forall k k' b b',
    b' = remove_assoc k b ->
    k' ≠ k ->
    filter_key k' b' = filter_key k' b.
Proof.
  intros k k' b.
  induction b as [|[k'' v] t Ih]; simpl; intros b' H1 H2; subst b'.
  + auto.
  + case_decide.
    - subst. by filter.
    - apply filter_key_cons. by apply Ih.
Qed.

Fixpoint find_assoc (k : K) (b : bucket) : option V :=
  match b with
  |[] => None
  |(k', v) :: t =>
     if (decide (k = k'))
     then Some v
     else find_assoc k t
  end.

Hint Rewrite
  remove_assoc_bucket_ne
  remove_assoc_bucket_eq
  remove_assoc_in : cassoc.

Ltac assoc := autorewrite with cassoc.

Tactic Notation "assoc" "in" "*" :=
  autorewrite with cassoc in *.

(* Relates a list of buckets to a total function from keys to lists of
   values, where [n] is the length of the [tbl].  For every key [k],
   [m] returns the list of values mapped to [k] in [tbl].  If [k] is
   not in [tbl], [m] returns the empty list.  This definition only
   considers the bucket whose index corresponds to the hash of [k]. *)
Definition valid_buckets (n : Z) (tbl : list bucket) (m : K -> (list V)) : Prop :=
  forall i b k,
    indexZ k n = i ->
    b = filter_key k (tbl !!! i) ->
    m k = map snd b.

(* If a key [k] is in a bucket of index [i], then [i] must correspond
to the hash of [k]. *)
Definition no_garbage (n : Z) (tbl : list bucket) : Prop :=
  forall i (k : K) v,
    valid i tbl ->
    (k, v) ∈ (tbl !!! i) ->
    indexZ k n = i.

Require Stdlib.Logic.Epsilon.

Definition cardinality (m : K -> (list V)) :=
  let s := Epsilon.epsilon (inhabits ([] : list V))
    (fun (l : list V) => forall k v, v ∈ m k -> v ∈ l /\ NoDup l) in
  len s.

(* Correlates a hash table with a total function that maps keys to a
   list of values.  Here we combine the previous two definitions as
   well as stating that a hash table has the same properties as a
   non-empty array.  The condition that the table must be non-empty is
   necessary for array accesses to be valid since the array is not
   resizable for now. *)
Definition isHashtbl (h : hashtbl) (m : K -> (list V)) :=
  ∃ l n, isArray h l ∧ n = len l ∧ 0 < n ∧
      no_garbage n l ∧ valid_buckets n l m.

(* Destructs a isHashtbl hypothesis. *)
Local Ltac destructIsHashtbl :=
  match goal with h: isHashtbl ?v _ |- _ =>
    unfold isHashtbl in h;
    let c := fresh "l" in
    let n := fresh "n" in
    destruct h as (c&?);
    destruct h as (n&?);
    unpack;
    arrays
  end.

(* Introduces the goals needed to prove [isHashtbl _]. [lia] is
   executed so that the goal stating that a table is greater than [0]
   is automatically dispatched.  *)
Local Ltac introIsHashtbl :=
  unfold isHashtbl;
  eexists; pack;
  eauto; list; try lia.

(* [index_intro k _n n] Introduces an index and its logical
   representation computed from [k].  This tactic is not strictly
   necessary although it makes following the proofs a little
   easier. *)
Local Ltac index_intro k _n n :=
  let _i := fresh "i'" in
  let i := fresh "i" in
  set (_i:= index k _n);
  set (i := indexZ k n);
  assert (isInt _i i) by tc.

(* Some definitions to facilitate working with functions as infinite
   maps. *)

Definition _empty := fun (_ : K) => [] : list V.
Notation "'∅'" := _empty.
Definition _set m (k : K) (v : V) :=
  (fun k' => if decide (k = k') then v :: m k' else m k').
Definition rm m (k : K) : K -> list V :=
  (fun k' => if (decide (k = k')) then tl (m k') else m k').
Definition rm_set m (k : K) (v : V) : K -> list V :=
  _set (rm m k) k v.

(* Hash table operations and their respective specifications. *)

Definition create (n : int) : hashtbl :=
  do a ← make n [] ; a.

Lemma wp_create :
  ∀Int _n n,
    (0 < n ≤ max_array_length)%Z ->
    wp (create _n) (λ h, isHashtbl h ∅).
Proof.
  intros _n n H1 H2. unfold create. wp_make a.
  wp_ret. introIsHashtbl.
  { unfold no_garbage. intros.
    do 2 list in *. apply not_elem_of_nil in H3.
    contradiction. }
  { intros i b k H3 H4.
    list in H3. list in H4.
    subst. simpl. auto. }
Qed.

Definition add (h : hashtbl) k v :=
  do _n ← length h;
  do i ← index k _n;
  do b ← get h i;
  do h' ← set h i ((k, v) :: b);
  h'.

(* If the list representation of a hash table does not contain keys in
   incorrect indexes and a new key is added in the correct index, the
   table remains valid. *)

Lemma no_garbage_insert :
  forall n k v i tbl b,
  len tbl = n ->
  no_garbage n tbl ->
  i = indexZ k n ->
  b = tbl !!! i ->
  no_garbage n (<[i:=(k, v) :: b]> tbl).
Proof.
  intros n k v i tbl b H1 H2 H3 H4.
  unfold no_garbage in *.
  intros i' k' v' H5 H6.
  list in H5.
  destruct (decide (i = i')).
  { subst i. list in H6.
    rewrite elem_of_app in H6.
    destruct H6 as [H6 | H6].
    - rewrite list_elem_of_singleton in H6.
      injection H6. intros. by subst.
    - subst. by apply H2 with v'. }
  { list in H6. by apply H2 with v'. }
Qed.

Lemma valid_insert_bucket_eq :
  forall k v l m n b b',
    n = len l ->
    valid_buckets n l m ->
    b = l !!! indexZ k n ->
    b' = filter_key k ((k, v) :: b) ->
    v :: m k = map snd b'.
Proof.
  intros k v l m n b b' H1 H2 H3 H4.
  subst b'. filter. simpl. f_equal.
  apply H2 with (indexZ k (len l)); by subst.
Qed.

Lemma valid_insert_bucket_ne :
  forall k k' i v l n m b b',
    n = len l ->
    valid_buckets n l m ->
    indexZ k n = i ->
    indexZ k' n = i ->
    b = l !!! indexZ k n ->
    b' = filter_key k' ((k, v) :: b) ->
    k ≠ k' ->
    m k' = map snd b'.
Proof.
  intros k k' i ????? b' H1 H2 ?????.
  subst b'. rewrite filter_key_cons_False by auto.
  apply H2 with i; by subst.
Qed.

(* Creates a case analysis for if [i] corresponds to the index of the
   bucket for key [k] in a hash table whose array is of size [n]. *)

Ltac case_bucket k n i :=
  destruct (decide (indexZ k n = i)).

Lemma valid_buckets_insert :
  forall i n tbl k v b m,
    n = len tbl ->
    0 < n ->
    i = indexZ k n ->
    b = tbl !!! i ->
    valid_buckets n tbl m ->
    valid_buckets n (<[i:=(k, v) :: b]> tbl)
      (_set m k v).
Proof.
  intros i n tbl k v b m ???? H5.
  intros i' b' k' ? ?.
  (* The updated map as described in the postcondition
     accurately models the updated hash table. *)
  unfold _set. destruct decide.
  + (* When we apply the updated map with the key we pass as
         argument. *)
    apply valid_insert_bucket_eq with tbl n (tbl !!! i);
      subst; by list.
  + (* When we apply the updated map with a different key [k']. *)
    case_bucket k n i'; [apply H5 with i| apply H5 with i'];
      subst; list; simpl; by filter.
Qed.

Lemma wp_add :
  forall h m k v,
    isHashtbl h m ->
    wp (add h k v)
      (λ h, isHashtbl h (_set m k v)).
Proof.
  intros h m k v H.
  unfold add.
  destructIsHashtbl.
  wp_length _n.
  index_intro k _n n.
  wp_bind_eq.
  index_intro k _n n.
  wp_get b.
  wp_set.
  wp_ret.
  introIsHashtbl.
  - subst. apply no_garbage_insert; auto.
  - apply valid_buckets_insert; by subst.
Qed.

Definition remove (h : hashtbl) (k : K) :=
  do l ← length h;
  do i ← index k l;
  do b ← get h i;
  do b' ← remove_assoc k b;
  set h i b'.

Hint Rewrite <- tl_map : clist.

Lemma no_garbage_remove :
  forall n tbl k i b b',
    i = indexZ k n ->
    n = len tbl ->
    b' = remove_assoc k b ->
    no_garbage n tbl ->
    b = tbl !!! i ->
    no_garbage n (<[i:=b']> tbl).
Proof.
  intros n tbl k i b b' ??? NG ? i' k' v??.
  list in *.
  apply NG with v. auto.
  destruct (decide (i = i')); subst; list in *. 2: auto.
  by apply remove_assoc_in with k.
Qed.

Lemma valid_buckets_remove :
  forall n i k b b' tbl m,
    0 < n ->
    n = len tbl ->
    i = indexZ k n ->
    b = tbl !!! i ->
    b' = remove_assoc k b ->
    valid_buckets n tbl m ->
    valid_buckets n (<[i:=b']> tbl) (rm m k)
  .
Proof.
  intros n i k b b' tbl m H1 H2 H3 H4 H5 H6 i' b'' k' H7 H8.
  unfold rm.
  case_decide.
  { subst b'' b' k i'. list.
    rewrite remove_assoc_bucket_eq with (b:=b) by auto.
    list. f_equal. subst b.
    apply H6 with (i := i); by subst. }
  { case_bucket k' n i.
    + subst b'' i'. list.
      rewrite remove_assoc_bucket_ne with (k:=k) (b:=b) by auto.
      apply H6 with i; by subst.
    + subst b''. list.
      apply H6 with i'; by subst. }
Qed.

Lemma wp_remove :
  forall h m k,
    isHashtbl h m ->
    wp (remove h k)
       (λ h', isHashtbl h' (rm m k)).
Proof.
  intros h m k H.
  destructIsHashtbl.
  unfold remove.
  wp_length _n.
  index_intro k _n n.
  wp_bind_eq.
  wp_get b.
  set (b' := remove_assoc k b).
  wp_bind_eq.
  wp_set.
  introIsHashtbl.
  - subst n. by apply no_garbage_remove with k b.
  - apply valid_buckets_remove with b; by subst.
Qed.

Definition replace (h : hashtbl) (k : K) (v : V) :=
  do n ← length h;
  do i ← index k n;
  do b ← get h i;
  do b' ← remove_assoc k b;
  do b' ← (k, v) :: b';
  set h i b'.

Lemma decompose_replace :
  forall (i : Z) x b (tbl : list bucket),
    <[i:=x :: b]> tbl =
      <[i:=x :: b]>(<[i:=b]>tbl).
Proof.
  intros. subst. by list.
Qed.

Lemma wp_replace :
  forall h m k v,
    isHashtbl h m ->
    wp (replace h k v) (λ h, isHashtbl h (rm_set m k v)).
Proof.
  intros h m k v H.
  unfold replace.
  destructIsHashtbl.
  wp_length _n.
  index_intro k _n n.
  wp_bind_eq.
  wp_get b.
  wp_bind_eq.
  wp_bind_eq.
  wp_set.
  set (b' := remove_assoc k b).
  introIsHashtbl; subst n; simpl; rewrite decompose_replace.
  - apply no_garbage_insert. 1, 3, 4: by list.
    apply no_garbage_remove with k b; subst; by list.
  - apply valid_buckets_insert. 1, 4: by list. 1, 2: lia.
    apply valid_buckets_remove with b; auto.
Qed.

Definition get (h : hashtbl) (k : K) :=
  do n ← length h;
  do i ← index k n;
  do b ← get h i;
  find_assoc k b.

Lemma filter_key_assoc :
  forall k l,
    head (map snd (filter_key k l)) = find_assoc k l.
Proof.
  intros k l.
  induction l as [|[k' v] t Ih]. auto.
  simpl. case_decide; subst; by filter.
Qed.

Lemma get_wp :
  forall h m k,
    isHashtbl h m ->
    wp (get h k) (λ v, head (m k) = v).
Proof.
  intros h m k H.
  unfold get.
  destructIsHashtbl.
  wp_length _n.
  set (_i := index k _n).
  set (i := indexZ k n).
  assert (isInt _i i) by tc.
  wp_bind_eq.
  wp_get b.
  wp_ret.
  rewrite H3 with (i:=i) (b:=filter_key k b); subst; auto.
  apply filter_key_assoc.
Qed.
