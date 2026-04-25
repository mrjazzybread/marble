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
  forall A k _n (l : list A),
    len l > 0 ->
    isInt _n (len l) ->
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

Ltac wp_hget k h l i :=
  let h1 := fresh "H1" in
  let h2 := fresh "H2" in
  wp_get i.

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

Hint Rewrite @lookup_total_insert_eq using listz_arith : clist.

(* If the list representation of a hash table does not have any garbage, then adding a key in its correct index will keep it without garbage. *)

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

(* Awful. *)

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
  wp_hget k h l b.
  { apply index_valid; auto with lia. }
  wp_bind_eq.
  wp_set.
  { apply index_valid; auto with lia. }
  wp_ret.
  introIsHashtbl.
  - rewrite length_insert. lia.
  - rewrite length_insert.
    apply no_garbage_insert; subst. 1, 2, 4: auto.
    destructIsInt. f_equal. int. lia. destructIsArray.
    unfold max_array_length in *. list in *. lia.
  - intros i b' k' H5 H6.
    unfold _set. list in H5.
    destructIsInt.
    destructIsArray.
    unfold max_array_length in H4.
    list in H4.
    int in *.
    destruct decide.
    + subst k'. list in H5.
      list in H4. int in *. unfold max_array_length in H4.
      int in *. subst i.
      rewrite lookup_total_insert_eq in H6.
      2: { apply index_valid_len. lia. }
      unfold filter_key in H6.
      rewrite filter_cons_True with (x:=(k, v)) in H6.
      2: auto. unfold valid_buckets in H3.
      subst b'.
      rewrite map_cons. f_equal.
      apply H3 with (indexZ k (len l)).
      { f_equal. auto. }
      { subst b. auto. }
    + list in H5.
      destruct (decide (i = indexZ k (len l))) as [E | E].
      { rewrite E in H6.
        destructIsInt.
        int in *.
        rewrite lookup_total_insert_eq in H6.
        2: { apply index_valid_len. lia. }
        subst b'.
        unfold filter_key.
        rewrite filter_cons_False with (x:=(k, v)). 2: auto.
        unfold valid_buckets in H3.
        apply H3 with i.
        { subst. reflexivity. }
        { subst. rewrite E. auto. }
      }
      { rewrite lookup_total_insert_ne in H6. 2: auto.
        unfold valid_buckets in H3.
        apply H3 with (indexZ k' n).
        auto. subst. auto.
      }
Qed.
