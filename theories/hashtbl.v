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
Parameter hash : K -> int.

(* Decidable equality over keys. *)
Global Declare Instance EqK : EqDecision K.
(* The type of keys must be countably infinite.  This is necessary in
   order to have finite maps whose domain is in [K] *)
Global Declare Instance CountK : Countable K.
Open Scope uint63.

(* Hash tables are arrays of buckets.  A bucket is an association list
   of keys to values.  Keys may appear more than once in the same
   bucket but can never belong to two buckets simultaneously. *)
Definition bucket := (list (K * V)).
Definition hashtbl := array bucket.

(* Function that calculates the index of a particular key using
[hash].  In machine integers and ideal integers. *)

Definition index k len : int :=
  (hash k) mod len.

Definition indexZ k (len : Z) : Z :=
   (to_Z (hash k)) mod len.

(* This typeclass instance relates the two indexes and is necessary to
   automatically dispatch side conditions when accessing the hash
   table. *)

Instance index_isInt :
  forall k len, isInt (index k len) (indexZ k (to_Z len)).
Proof.
  intros. introIsInt. unfold index. unfold indexZ. lia.
Qed.

(* For any non-empty array whose model is [l], [indexZ] will always
   generate an index in bounds. *)

Lemma index_valid_len :
  forall A k (l : list A),
    len l > 0 ->
    valid (indexZ k (len l)) l.
Proof.
  intros.
  unfold indexZ. lia.
Qed.

Lemma index_valid :
  forall A k _n (l : list A) `{isInt _n (len l)},
    len l > 0 ->
    valid (indexZ k φ (_n)) l.
Proof.
  intros k h _n l H4 H5.
  unfold indexZ.
  destructIsInt.
  lia.
Qed.

(* Filters a bucket leaving only pairings whose key is [k]. *)
Definition filter_key (k : K) (l : bucket) : bucket :=
  base.filter (fun (x : K * V) => let (k', _) := x in k' = k) l.

Lemma filter_key_cons_True :
  forall k v b, filter_key k ((k, v) :: b) = (k, v) :: filter_key k b.
Proof.
  intros.
  unfold filter_key. by apply filter_cons_True.
Qed.

Lemma filter_key_cons_False :
  forall k k' v b,
    k' ≠ k ->
    filter_key k ((k', v) :: b) = filter_key k b.
Proof.
  intros.
  unfold filter_key. by apply filter_cons_False.
Qed.

Lemma filter_key_nil :
  forall k, filter_key k [] = [].
Proof.
  intros. unfold filter_key.
  Search filter.
  by rewrite filter_nil with (P:=(λ x : K * V, let (k', _) := x in k' = k)).
Qed.

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

(* Correlates a hash table with a total function that maps keys to a
   list of values.  Here we combine the previous two definitions as
   well as stating that a hash table has the same properties as a
   non-empty array.  The condition that the table must be non-empty is
   necessary for array accesses to be valid since the array is not
   resizable for now. *)
Definition isHashtbl (h : hashtbl) (m : K -> (list V)) :=
  ∃ l n, isArray h l ∧ n = len l ∧ 0 < n ∧
      no_garbage n l ∧ valid_buckets n l m.

Hint Rewrite @lookup_total_replicate_lt using listz_arith : clist.

(* TODO : Another hint database for maps? *)
Hint Rewrite (lookup_empty (M := gmap K) (A:=V)) : clist.

(* Destructs a isHashtbl hypothesis. *)
Local Ltac destructIsHashtbl :=
  match goal with h: isHashtbl ?v _ |- _ =>
    unfold isHashtbl in h;
    let c := fresh "l" in
    let n := fresh "n" in
    destruct h as (c&?);
    destruct h as (n&?);
    unpack
  end.

Local Ltac introIsHashtbl :=
  unfold isHashtbl;
  eexists; pack;
  unfold valid_buckets; eauto.

(* Some definitions to facilitate working with functions as infinite
   maps. *)

Definition _empty := fun (_ : K) => [] : list V.
Notation "'∅'" := _empty.
Definition _set m (k : K) (v : V) :=
  (fun k' => if decide (k = k') then v :: m k' else m k').
Definition rm m (k : K) : K -> list V :=
  (fun k' => if (decide (k = k')) then tl (m k') else m k').

(* Specification for create function *)

Definition create (n : int) : hashtbl :=
  do a ← make n [] ; a.

Lemma wp_create :
  ∀Int _n n,
    (0 < n ≤ max_array_length)%Z ->
    wp (create _n) (λ h, isHashtbl h ∅).
Proof.
  intros _n n H1 H2. unfold create. wp_make a.
  wp_ret. introIsHashtbl.
  { list. lia. } (* Array is non-empty *)
  (* The following conditions are trivial since they
      are statements regarding the validity of the
      empty table's contents. *)
  { unfold no_garbage. intros.
    do 2 list in *. apply not_elem_of_nil in H3.
    contradiction. }
  { intros i b k H3 H4. unfold indexZ in H3.
    list in H3. list in H4.
    subst. simpl. auto. }
Qed.

Definition add (h : hashtbl) k v :=
  do _n ← length h;
  do i ← index k _n;
  do b ← get h i;
  do h' ← set h i ((k, v) :: b);
  h'.

(* This tactic solves goals of the form [valid (indexZ i (len l) l)]
   using the [index_valid] lemma. *)

Ltac validi := apply index_valid; [auto | try lia].

(* Whenever we use the tactics [wp_get] or [wp_set], we have to prove
   that the array accesses are valid.  When array indexes are always
   computed using the [index] function, it is always valid to access
   the array.  These wrapper tactics dispatch these conditions
   automatically when the index in generated using [index]. *)

Local Ltac wp_hget i :=
  wp_get i;
  [validi|].

Local Ltac wp_hset :=
  wp_set;
  [validi|].

(* TODO : Maybe François would like to add these lemmas to his listz
library? *)

Lemma list_lookup_total_insert_eq :
  forall {A} `{Inhabited A} (l : list A) (i : Z) x,
    valid i l ->
    <[i := x]> l !!! i = x.
Proof.
  intros.
  apply list_lookup_total_correct.
  by rewrite list_lookup_insert_eq.
Qed.

Lemma list_lookup_total_insert_ne :
  forall {A} `{Inhabited A} (l : list A) (i i' : Z) x,
    valid i l ->
    valid i' l ->
    i ≠ i' ->
    <[i' := x]> l !!! i = l !!! i.
Proof.
  intros.
  apply list_lookup_total_correct.
  rewrite list_lookup_insert_ne. 2: auto.
  apply list_lookup_lookup_total.
  by apply lookup_lt_is_Some_2.
Qed.

Hint Rewrite @lookup_total_insert_eq using try listz_arith : clist.

(* If the list representation of a hash table does not contain keys in
   incorrect indexes and a new key in the correct index, the table
   remains valid. *)

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
  { rewrite list_lookup_total_insert_ne in H6.
    2, 4: auto.
    - by apply H2 with v'.
    - unfold indexZ in H3. lia. }
Qed.

Lemma valid_insert_bucket_eq :
  forall k v l m b b',
    valid_buckets (len l) l m ->
    b = l !!! indexZ k (len l) ->
    b' = filter_key k ((k, v) :: b) ->
    v :: m k = map snd b'.
Proof.
  intros k v l m b b' H1 H2 H3.
  rewrite filter_key_cons_True in H3.
  unfold valid_buckets in H1.
  subst b'.
  rewrite map_cons. f_equal.
  apply H1 with (indexZ k (len l)).
  { f_equal. }
  { subst b. auto. }
Qed.

Lemma valid_insert_bucket_ne :
  forall k k' i v l m b b',
    valid_buckets (len l) l m ->
    indexZ k (len l) = i ->
    indexZ k' (len l) = i ->
    b = l !!! indexZ k (len l) ->
    b' = filter_key k' ((k, v) :: b) ->
    k ≠ k' ->
    m k' = map snd b'.
Proof.
  intros k k' i v l m b b' H1 H2 H3 H4 H5 H6.
  rewrite filter_key_cons_False in H5. 2: auto.
  unfold valid_buckets in H1.
  apply H1 with (indexZ k (len l)); subst; auto.
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
  wp_bind_eq.
  wp_hget b.
  wp_bind_eq.
  wp_hset.
  wp_ret.
  introIsHashtbl. 2,3: destructIsArray.
  - (* The length is still greater than 0. *)
    rewrite length_insert. lia.
  -  (* The key was inserted in the correct bucket. *)
    list. apply no_garbage_insert; subst. 1, 2, 4: auto.
    list in *. unfold max_array_length in *.
    destructIsInt. f_equal. int. lia.
  - intros i b' k' ? ?.
    unfold _set.
    destructIsInt.
    unfold max_array_length in *.
    list in *.
    int in *.
    (* The updated map as described in the postcondition
       accurately models the updated hash table. *)
    destruct decide.
    + (* When we apply the updated map with the key we pass as
         argument. *)
      subst k'. subst i.
      list in *.
      2: { apply index_valid_len. lia. }
      unfold filter_key in *.
      simpl in *.
      subst n.
      apply valid_insert_bucket_eq with l b; auto.
    + (* When we apply the updated map with a different key [k']. *)
      destruct (decide (indexZ k (len l) = i)) as [E | E].
      { (* [k'] belongs to the same bucket (i.e. has the same index)
           as [k]. *)
        rewrite E in H9.
        list in *. 2: { subst i. apply index_valid_len. lia. }
        subst n.
        apply valid_insert_bucket_ne with k i v l b; auto. }
      { (* [k] belongs to another bucket. *)
        list in *.
        unfold valid_buckets in H3.
        apply H3 with (indexZ k' n).
        auto. subst. auto. }
Qed.

Fixpoint remove_assoc (k : K) (b : bucket) :=
  match b with
  |[] => []
  |(x, v) :: t =>
     if decide (x = k) then
       t else (x, v) :: remove_assoc k t
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
Admitted.

Lemma remove_assoc_bucket_ne :
  forall k k' b b',
    b' = remove_assoc k b ->
    k ≠ k' ->
    filter_key k' b' = filter_key k' b.
Proof.
Admitted.

Definition remove (h : hashtbl) (k : K) :=
  do l ← length h;
  do i ← index k l;
  do b ← get h i;
  do b' ← remove_assoc k b;
  set h i b'.

(* Destructs a isHashtbl hypothesis. *)
Local Ltac destructIsHashtbl' :=
  match goal with h: isHashtbl _ _ |- _ =>
    unfold isHashtbl in h;
    let c := fresh "l" in
    let n := fresh "n" in
    destruct h as (c&?);
    destruct h as (n&?);
    unpack
  end.

Lemma wp_remove :
  forall h m k,
    isHashtbl h m ->
    wp (remove h k)
       (λ h', isHashtbl h' (rm m k)).
Proof.
  intros h m k H.
  destructIsHashtbl'.
  unfold remove.
  wp_length _n.
  subst n.
  wp_bind_eq.
  wp_hget b.
  wp_bind_eq.
  wp_hset.
  introIsHashtbl.
  + list. lia.
  + list. unfold no_garbage in *.
    intros ? k' ???.
    list in *.
    apply H2 with v. auto.
    destruct (decide (i = indexZ k φ (_n))); subst; list in *. 2: auto.
    apply remove_assoc_in with k. auto.
  + intros ? b' k' ??.
    unfold rm.
    list in *.
    destructIsInt.
    destructIsArray. unfold max_array_length in *.
    unfold valid_buckets in *.
    destruct decide.
    { subst.
      list in *. int in *.
      list. 2: { apply index_valid_len. lia. }
      rewrite remove_assoc_bucket_eq with (b:=(l !!! indexZ k' (len l))).
      2: auto.
      rewrite <- tl_map.
      f_equal. by apply H3 with (indexZ k' (len l)). }
    { list in *. int in *.
      destruct (decide (indexZ k (len l) = i)) as [E | E]; subst.
      + rewrite E. list.
        2: { apply index_valid_len. lia. }
        rewrite remove_assoc_bucket_ne with (k:=k) (b:=(l !!! indexZ k' (len l))). 2, 3: auto.
        apply H3 with (indexZ k' (len l)). 2:auto.
        reflexivity.
      + rewrite list_lookup_total_insert_ne.
        2, 3 : apply index_valid_len; lia.
        2: symmetry; apply E.
        by apply H3 with (indexZ k' (len l)).
    }
Qed.
