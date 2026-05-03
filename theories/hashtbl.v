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
(* The type of keys is countably infinite. *)
Global Declare Instance CoutntK : Countable K.

Open Scope uint63.

(* Hash tables are arrays of buckets.  A bucket is an association list
   of keys to values.  Keys may appear more than once in the same
   bucket but can never belong to two buckets simultaneously. *)
Definition bucket := (list (K * V)).
Definition hashtbl := (int * array bucket)%type.

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

Lemma filter_key_nin :
  forall k b,
    (∀ v : V, (k, v) ∉ b) ->
    map snd (filter_key k b) = [].
Proof.
  intros k b H1.
  induction b as [|[k' v] t Ih].
  - auto.
  - rewrite filter_key_cons_False.
    + apply Ih. intros v'.
      specialize H1 with v'.
      rewrite not_elem_of_cons in H1.
      by destruct H1.
    + specialize H1 with v.
      rewrite not_elem_of_cons in H1.
      destruct H1.
      intros H3. by subst.
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
  |[] => (false, [])
  |(x, v) :: t =>
     if decide (x = k) then (true, t) else
       let (r, t) := remove_assoc k t in
       (r, (x, v) :: t)
  end.

Instance remove_assoc_is_bool :
  forall k b r b',
    (r, b') = (remove_assoc k b) ->
    isBool r (∃ v, (k, v) ∈ b) (forall v, (k, v) ∉ b).
Proof.
  intros k b r.
  destruct r; simpl; induction b as [|[k' v] b'' Ih]; intros b' H1.
  - inversion H1.
  - simpl in H1.
    case_decide.
    + injection H1. intros. subst b' k'.
      exists v. rewrite elem_of_cons. auto.
    + destruct (remove_assoc k b'').
      injection H1. intros. subst b' b.
      specialize Ih with l.
      destruct Ih as [v' Ih]. auto.
      exists v'. rewrite elem_of_cons. auto.
  - intros. apply not_elem_of_nil.
  - simpl in H1.
    case_decide.
    + injection H1. discriminate.
    + intros v'. rewrite not_elem_of_cons. split.
      { intros H2. injection H2. by subst. }
      { apply Ih with (tail b'). destruct (remove_assoc k b''). injection H1. intros. by subst. }
Qed.



Lemma remove_assoc_in :
  forall b k k' v,
    (k', v) ∈ snd (remove_assoc k b) ->
    (k', v) ∈ b.
Proof.
  intros b k k' v H1.
  induction b as [|[k'' v'] t Ih]; simpl in H1.
  + apply not_elem_of_nil in H1. contradiction.
  + destruct decide in H1; apply elem_of_cons. auto.
    destruct remove_assoc.
   apply elem_of_cons in H1 as [H1 | H1].
   auto. right. by apply Ih.
Qed.

Lemma remove_assoc_bucket_eq :
  forall k b b',
    b' = snd (remove_assoc k b) ->
    filter_key k b' = tl (filter_key k b).
Proof.
  intros k b.
  induction b as [|[k' v] t Ih]; simpl; intros b' H1; subst b'. auto.
  case_decide.
  - subst. filter. by simpl.
  - filter. destruct remove_assoc. simpl.
    filter. auto.
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
    b' = snd (remove_assoc k b) ->
    k' ≠ k ->
    filter_key k' b' = filter_key k' b.
Proof.
  intros k k' b.
  induction b as [|[k'' v] t Ih]; simpl; intros b' H1 H2; subst b'.
  + auto.
  + case_decide.
    - subst. by filter.
    - destruct remove_assoc. simpl. apply filter_key_cons. by apply Ih.
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

Notation hmap := (gmap K (list V)).

(* Some definitions to facilitate working with functions as infinite
   maps.

    Remark: we leverage the fact that the Instance of the in habited
    type class for lists is the empty list.*)

Definition _add (m : hmap) (k : K) (v : V) := <[k:= v :: m !!! k]> m.

Definition rm (m : hmap) (k : K) :=
  <[k:=tl (m !!! k)]> m.

Definition rm_add (m : hmap) (k : K) (v : V) :=
  _add (rm m k) k v.

Definition cardinality (h : hmap) :=
  (map_fold (fun _ v acc => acc + len v) 0 h)%Z.

Lemma cardinality_empty :
  cardinality ∅ = 0%Z.
Proof.
  apply map_fold_empty.
Qed.

Hint Rewrite
  @fin_maps.insert_empty
  using auto : cmap.

Ltac map := autorewrite with cmap.

Lemma cardinality_insert_fresh :
  forall m k l n,
    cardinality m = n ->
    m !! k = None ->
    cardinality (<[k:=l]>m) = (len l + n)%Z.
Proof.
  intros.
  subst n.
  unfold cardinality.
  rewrite map_fold_insert; tc.
Qed.

Lemma cardinality_delete :
  forall m k l n,
    cardinality m = n ->
    m !! k = Some l ->
    (cardinality (delete k m) + len l)%Z = n.
Proof.
  intros. subst n. unfold cardinality.
  rewrite map_fold_delete with (m:=m); tc.
Qed.

Lemma cardinality_insert :
  forall m k l n,
    cardinality m = n ->
    cardinality (<[k:=l]>m) = (n + len l - len (m !!! k))%Z.
Proof.
  intros m k l n H1.
  intros.
  unfold _add.
  destruct (decide (m !! k = None)) as [E1 | E1].
  - rewrite fin_maps.lookup_total_alt. rewrite E1.
    simpl. rewrite cardinality_insert_fresh with (n:=n) by auto. length. lia.
  - rewrite <- insert_delete_eq.
    rewrite cardinality_insert_fresh with (n:=(n - len (m !!! k))%Z).
    + length. lia.
    + rewrite <- cardinality_delete with (n:=n) (k:=k) (l:= m !!! k) (m:=m); auto with lia.
      remember (m !! k) as l' eqn:E2.
      destruct l' as [x|].
      { by rewrite lookup_total_correct with (x:=x). }
      { contradiction. }
    + by rewrite lookup_delete_eq.
Qed.

Ltac cinsert n := rewrite cardinality_insert with (n:=n) by auto.

Lemma cardinality_add :
  forall m n k v,
    cardinality m = n ->
    cardinality (_add m k v) = (n + 1)%Z.
Proof.
  intros.
  unfold _add.
  cinsert n.
  length. lia.
Qed.

Lemma cardinality_rm_empty :
  forall m n k,
    cardinality m = n ->
    m !!! k = [] ->
    cardinality (rm m k) = n%Z.
Proof.
  intros m n k H1 H2.
  unfold rm.
  cinsert n.
  rewrite H2. by length.
Qed.

Lemma cardinality_rm :
  forall m n k,
    cardinality m = n ->
    m !!! k <> [] ->
    cardinality (rm m k) = (n - 1)%Z.
Proof.
  intros.
  unfold rm.
  cinsert n.
  remember (m !!! k) as l eqn:E.
  destruct l. contradiction.
  by length.
Qed.

Lemma cardinality_rm_add_empty :
  forall m n k v,
    cardinality m = n ->
    m !!! k = [] ->
    cardinality (rm_add m k v) = (n + 1)%Z.
Proof.
  intros.
  unfold rm_add.
  rewrite cardinality_add with (n:=cardinality(rm m k)) by auto.
  rewrite cardinality_rm_empty with (n:=cardinality m) by auto.
  lia.
Qed.

Lemma cardinality_rm_add :
  forall m n k v,
    cardinality m = n ->
    m !!! k <> [] ->
    cardinality (rm_add m k v) = n.
Proof.
  intros.
  unfold rm_add.
  rewrite cardinality_add with (n:=cardinality(rm m k)) by auto.
  rewrite cardinality_rm with (n:=cardinality m) by auto. lia.
Qed.

(* Relates a list of buckets to a total function from keys to lists of
   values, where [n] is the length of the [tbl].  For every key [k],
   [m] returns the list of values mapped to [k] in [tbl].  If [k] is
   not in [tbl], [m] returns the empty list.  This definition only
   considers the bucket whose index corresponds to the hash of [k]. *)
Definition valid_buckets (n : Z) (tbl : list bucket) (m : hmap) : Prop :=
  forall i b k,
    indexZ k n = i ->
    b = filter_key k (tbl !!! i) ->
    m !!! k = map snd b.

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
Definition isHashtbl (h : hashtbl) (m : hmap) :=
  let (popu, arr) := h in
  ∃ l n, isArray arr l ∧ n = len l ∧
           isInt popu (cardinality m) ∧ 0 < n ∧
           no_garbage n l ∧ valid_buckets n l m.

(* Destructs a isHashtbl hypothesis. *)
Local Ltac destructIsHashtbl h :=
  destruct h;
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
  let _i := fresh "_i" in
  let i := fresh "i'" in
  set (_i:= index k _n);
  set (i := indexZ k n);
  assert (isInt _i i) by tc.

(* Hash table operations and their respective specifications. *)

Definition create (n : int) : hashtbl :=
  do a ← make n [] ; (0, a).

Lemma wp_create :
  ∀Int _n n,
    (0 < n ≤ max_array_length)%Z ->
    wp (create _n) (λ h, isHashtbl h ∅).
Proof.
  intros _n n H1 H2. unfold create. wp_make a.
  wp_ret. introIsHashtbl.
  { rewrite cardinality_empty. tc. }
  { unfold no_garbage. intros.
    do 2 list in *. apply not_elem_of_nil in H3.
    contradiction. }
  { intros i b k H3 H4.
    list in H4.
    subst. by simpl. }
Qed.

Definition add (h : hashtbl) k v :=
  do (popu, h) ← h;
  do _n ← length h;
  do i ← index k _n;
  do b ← get h i;
  do h' ← set h i ((k, v) :: b);
  (popu + 1,h').

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
    v :: (m !!! k) = map snd b'.
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
    m !!! k' = map snd b'.
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
      (_add m k v).
Proof.
  intros i n tbl k v b m ???? H5.
  intros i' b' k' ? ?.
  (* The updated map as described in the postcondition
     accurately models the updated hash table. *)
  unfold _add. destruct (decide (k = k')).
  + (* When we apply the updated map with the key we pass as
         argument. *)
    subst k'.
    rewrite fin_maps.lookup_total_insert_eq.
    apply valid_insert_bucket_eq with tbl n (tbl !!! i);
      subst; by list.
  + (* When we apply the updated map with a different key [k']. *)
    rewrite fin_maps.lookup_total_insert_ne by auto.
    case_bucket k n i';
      [apply H5 with i| apply H5 with i'];
      subst; list; simpl; by filter.
Qed.

Lemma wp_add :
  forall h m k v,
    isHashtbl h m ->
    wp (add h k v)
      (λ h, isHashtbl h (_add m k v)).
Proof.
  intros h m k v H.
  unfold add.
  destructIsHashtbl h.
  wp_bind_eq.
  wp_length _n.
  index_intro k _n n.
  wp_bind_eq.
  wp_get b.
  wp_set.
  wp_ret.
  introIsHashtbl.
  - rewrite cardinality_add with (n:=cardinality m) by auto. tc.
  - subst. apply no_garbage_insert; auto.
  - apply valid_buckets_insert; by subst.
Qed.

Definition remove (h : hashtbl) (k : K) :=
  do (n, h) ← h;
  do l ← length h;
  do i ← index k l;
  do b ← get h i;
  do (r, b') ← remove_assoc k b;
  do h' ← set h i b';
  do n' ← if r then n - 1 else n;
  (n', h').

Hint Rewrite <- tl_map : clist.

Lemma no_garbage_remove :
  forall n tbl k i b b' r,
    i = indexZ k n ->
    n = len tbl ->
    (r, b') = remove_assoc k b ->
    no_garbage n tbl ->
    b = tbl !!! i ->
    no_garbage n (<[i:=b']> tbl).
Proof.
  intros n tbl k i b b' r ??? NG ? i' k' v??.
  list in *.
  apply NG with v. auto.
  destruct (decide (i = i')); subst; list in *. 2: auto.
  apply remove_assoc_in with k.
  destruct remove_assoc.
  injection H1. simpl. intros. subst. auto.
Qed.

Lemma get_snd :
  forall A B (p1 : A * B) (p2 : A * B),
    p1 = p2 -> snd p1 = snd p2.
Proof.
  intros.
  subst. auto.
Qed.

Lemma valid_buckets_remove :
  forall n i k b b' r tbl m,
    0 < n ->
    n = len tbl ->
    i = indexZ k n ->
    b = tbl !!! i ->
    (r, b') = remove_assoc k b ->
    valid_buckets n tbl m ->
    valid_buckets n (<[i:=b']> tbl) (rm m k)
  .
Proof.
  intros n i k b b' r tbl m H1 H2 H3 H4 H5 H6 i' b'' k' H7 H8.
  unfold rm.
  apply get_snd in H5. simpl in H5.
  destruct (decide (k = k')).
  { subst b'' k i'. list.
    rewrite remove_assoc_bucket_eq with (b:=b) by auto.
    rewrite fin_maps.lookup_total_insert_eq.
    list. f_equal. subst b.
    apply H6 with (i := i); by subst. }
  { rewrite fin_maps.lookup_total_insert_ne by auto.
    case_bucket k' n i.
    + subst b'' i'. list.
      rewrite remove_assoc_bucket_ne with (k:=k) (b:=b) by auto.
      apply H6 with i; by subst.
    + subst b''. list.
      apply H6 with i'; by subst. }
Qed.

Lemma non_empty_bucket :
  forall n tbl i m b k,
  valid_buckets n tbl m ->
  i = indexZ k n ->
  b = tbl !!! i ->
  (∃ v : V, (k, v) ∈ b) ->
  m !!! k ≠ [].
Proof.
  intros n tbl i m b k H1 H2 H3 [v H4].
  rewrite H1 with (i:=i) (b:=filter_key k b) by auto with subst.
  intros H5.
  apply map_eq_nil in H5.
  Search filter nil.
  by apply filter_nil_not_elem_of with (l:=b) (x:=(k, v)) in H5.
Qed.

Lemma empty_bucket :
  forall n tbl i m b k,
  valid_buckets n tbl m ->
  i = indexZ k n ->
  b = tbl !!! i ->
  (forall v : V, (k, v) ∉ b) ->
  m !!! k = [].
Proof.
  intros n tbl i m b k H1 H2 H3 H4.
  rewrite H1 with (i:=i) (b:=filter_key k b) by auto with subst.
  by rewrite filter_key_nin.
Qed.

Lemma wp_remove :
  forall h m k,
    isHashtbl h m ->
    wp (remove h k)
       (λ h', isHashtbl h' (rm m k)).
Proof.
  intros h m k H.
  destructIsHashtbl h.
  unfold remove.
  wp_bind_eq.
  wp_length _n.
  index_intro k _n n.
  wp_bind_eq.
  wp_get b.
  remember (remove_assoc k b) as b' eqn:E.
  destruct b' as [r b'].
  wp_bind_eq.
  wp_set.
  wp_if; wp_ret; wp_ret;
    introIsHashtbl.
  2, 5: subst n; by apply no_garbage_remove with k b r.
  2, 4: apply valid_buckets_remove with b r; by subst.
  - rewrite cardinality_rm with (n:=cardinality m); tc.
    by apply non_empty_bucket with (tbl:=l) (b:=b) (i:= i')  (n:=n).
  - rewrite cardinality_rm_empty with (n:=cardinality m); tc.
    by apply empty_bucket with (tbl:=l) (b:=b) (i:=i') (n:=n).
Qed.

Definition replace (h : hashtbl) (k : K) (v : V) :=
  do (n, h) ← h;
  do l ← length h;
  do i ← index k l;
  do b ← get h i;
  do (r, b') ← remove_assoc k b;
  do b' ← (k, v) :: b';
  do n' ← if r then n else n + 1;
  do h' ← set h i b';
  (n', h').

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
    wp (replace h k v) (λ h, isHashtbl h (rm_add m k v)).
Proof.
  intros h m k v H.
  unfold replace.
  destructIsHashtbl h.
  wp_bind_eq.
  wp_length _n.
  index_intro k _n n.
  wp_bind_eq.
  wp_get b.
  wp_bind_eq.
  remember (remove_assoc k b) as b' eqn:E.
  destruct b' as [r b'].
  wp_bind_eq.
  wp_if; wp_ret; wp_bind_eq; wp_set; wp_ret;
  introIsHashtbl; subst n; simpl.
  2, 3, 5, 6: rewrite decompose_replace.
  2, 4: apply no_garbage_insert; (try (by list)).
  2, 3: apply no_garbage_remove with k b r; subst; by list.
  2, 3: apply valid_buckets_insert; (try by list); try lia.
  2, 3: apply valid_buckets_remove with b r; auto.
  + rewrite cardinality_rm_add with (n:=cardinality m); tc.
    by apply non_empty_bucket with (tbl:=l) (b:=b) (i:=i') (n:=len l).
  + rewrite cardinality_rm_add_empty with (n:=cardinality m); tc.
    by apply empty_bucket with (tbl:=l) (b:=b) (i:=i') (n:=len l).
Qed.

Definition get (h : hashtbl) (k : K) :=
  do (_, h) ← h;
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
    wp (get h k) (λ v, head (m !!! k) = v).
Proof.
  intros h m k H.
  unfold get.
  destructIsHashtbl h.
  wp_bind_eq.
  wp_length _n.
  index_intro k _n n.
  wp_bind_eq.
  wp_get b.
  wp_ret.
  rewrite H4 with (i:=i') (b:=filter_key k b); subst; auto.
  apply filter_key_assoc.
Qed.

Definition hlength (h : hashtbl) : int :=
  fst h.

Lemma length_spec :
  forall h m,
    isHashtbl h m ->
    wp (hlength h) (λ n, isInt n (cardinality m)).
Proof.
  intros.
  unfold hlength.
  wp_ret.
  by destructIsHashtbl h.
Qed.

Fixpoint bucket_iter_right {S} (b : bucket) (s : S) f : S:=
  match b with
  |[] => s
  |(k, v)::b' =>
     do s' ← bucket_iter_right b' s f;
     f k v  s' end.

Definition fold_right_spec {S} b (f : K -> V -> S -> S) :=
    ITER_LIST [] (List.rev b)
      (λ (x : K * V) s Q,
        forall k v, x = (k, v) -> wp (f k v s) Q)
      (λ s Q, wp (bucket_iter_right b s f) Q).

Lemma bucket_iter_right_wp {S} b f :
  @fold_right_spec S b f.
Proof.
  unfold fold_right_spec.
  induction b as [|[k v] b Ih];
    simpl bucket_iter_right; intros; ITER; list in *.
  - wp_ret.
  - wp_op Ih shadowing:s.
    { intros. wp_op Hbody.
      - simpl. by apply prefix_app_r.
      - by intros. }
    {
      wp_op Hbody.
      - subst. simpl. by list.
      - intros. simpl. exists  (rev b ++ [(k, v)]).
        split; auto. by subst.
    }
Qed.

Definition iter_rev {S} (h : hashtbl) (s : S) f : S :=
  iteri (snd h) s (fun _ b s => bucket_iter_right b s f).

Lemma wp_iter_rev :
  forall S h m f,
  isHashtbl h m →
  ITER_LIST [] (map_to_list m)
    (λ (x : K * (list V)) s Q,
      forall k (l : list V) b,
      x = (k, l) ->
      b = List.map (fun l => (k, l)) (m !!! k) ->
      fold_right_spec b f)
    (λ (s : S) Q, wp (iter_rev h s f) Q).
Proof.
  intros.
  destructIsHashtbl h.
  unfold iter_rev.
  induction m using map_first_key_ind; ITER.
Admitted.

Definition resize (h : hashtbl) : hashtbl :=
  do (p, h) ← h;
  do n ← length h;
  do n ← n * 2;
  do a ← make n [];
  do h' ← (0, a);
  iter_rev (p, h) h'
    (fun k v h'' => add h'' k v).

Lemma resize_spec :
  forall h m,
    isHashtbl h m ->
    wp (resize h) (λ h, isHashtbl h m).
Proof.
  unfold resize.
  intros.
  destructIsHashtbl h.
  wp_bind_eq.
  wp_length n'.
  wp_bind_eq.
  wp_make a'.
  { admit. }
  wp_bind_eq.
  wp_op wp_iter_rev.
  { admit. }
  { admit. }
  { admit. }
  { admit. }
Admitted.
