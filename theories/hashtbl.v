From stdpp Require Import numbers list gmap.
From listz Require Import listz.
Notation len := length.
From Stdlib Require Import Uint63.
From Stdlib Require Import Array.PArray.
From marble Require Import tactics bool int iteration loop wp logic array.
Implicit Types _i _j _k _n : int.

Section H.
(* Type of keys *)
Variable K : Type.

(* Type of values. *)
Variable V : Type.

(* Hash function. *)
Parameter _hash : K -> int.
Parameter hash : K -> Z.

Parameter _eq : K -> K -> bool.

Declare Instance isBool_eq :
  ∀ k1 k2, isBool1 (_eq k1 k2) (k1 = k2).

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
Inductive bucket :=
  | Nil : bucket
  | Cons : K -> V -> bucket -> bucket.

Definition assoc := list (K * V).

Fixpoint b2l b := match b with
 |Nil => []
 |Cons k v t => (k, v) :: b2l t
 end.

Instance bucket_inh : Inhabited bucket :=
  populate Nil.

Definition hashtbl := (int * array bucket)%type.

(* Function that calculates the index of a particular key using
[hash].  In machine integers and ideal integers. *)

Notation index k len :=
  ((_hash k) mod len).

Notation indexZ k len := (hash k mod len)%Z.

(* -------------------------------------------------------------------------- *)

(* Trivial lemmas to automate rewriting goals involving    [filter_key]*)

Notation filter_key k l :=
  (filter (fun (x : K * V) => eq x.1 k) l).

Lemma filter_key_cons_True :
  forall k v b, filter_key k ((k, v) :: b) = (k, v) :: filter_key k b.
Proof.
  intros. by rewrite filter_cons_True.
Qed.

Lemma filter_key_cons_False :
  forall k k' v b,
    k' ≠ k ->
    filter_key k ((k', v):: b) = filter_key k b.
Proof.
  intros.
  simpl. by rewrite filter_cons_False.
Qed.

Lemma filter_key_nin :
  forall k b,
    (∀ v : V, (k, v) ∉ b) ->
    filter_key k b = [].
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
  using done : cfilter.

Ltac filter := autorewrite with cfilter.

Lemma filter_key_cons :
  forall k k' v b1 b2,
    filter_key k b1 = filter_key k b2 ->
    filter_key k ((k', v)::b1) = filter_key k ((k', v) :: b2).
Proof.
  intros.
  destruct (decide (k = k')).
  + subst. filter. by f_equal.
  + by filter.
Qed.

(* -------------------------------------------------------------------------- *)

(* Association lists *)

Fixpoint remove_assoc (k : K) (b : bucket) :=
  match b with
  |Nil => (false, Nil)
  |Cons x v t =>
     do b ← _eq x k;
     if b then (true, t)
     else
       do (r, t) ← remove_assoc k t;
       (r, Cons x v t)
  end.

Fixpoint remove_assoc_list (k : K) (l : list (K * V)) :=
  match l with
  |[] => []
  |(k', v) :: t =>
     if (decide (k = k'))
     then t
     else
       (k', v) :: remove_assoc_list k t
  end.

Lemma remove_assoc_wp k b:
  ∀ l, l = b2l b ->
  wp (remove_assoc k b)
    (λ r, let (r, b') := r in
          ∃ l', l' = b2l b' ∧
          isBool r (∃ v, (k, v) ∈ l) (∀ v, (k, v) ∉ l) ∧
          l' = remove_assoc_list k l).
Proof.
  induction b as [|k' v b Ih]; simpl; intros; subst l.
  - wp_ret. simpl in *. pack; eauto.
    intros ?. unpack. by apply not_elem_of_nil in H.
  - simpl. wp_bind_eq. wp_if.
    + subst k'. wp_ret. simpl.
      pack; eauto; try constructor.
      by rewrite decide_True.
    + wp_op Ih. simpl. intros [r b'].
      intros [l' ?]. unpack.
      exists ((k', v) :: l'). subst l'.
      repeat split; try by filter.
      { destruct r; simpl in *.
        - unpack. eexists. by constructor.
        - intros. rewrite not_elem_of_cons.
          split; auto. intros I. by injection I. }
      { rewrite decide_False by auto.
        by f_equal. }
Qed.

Lemma remove_assoc_in :
  forall b k k' v,
    (k', v) ∈ remove_assoc_list k b ->
    (k', v) ∈ b.
Proof.
  intros b k k' v H1.
  induction b as [|[k'' v'] t Ih]; simpl in H1.
  + by apply not_elem_of_nil in H1.
  + destruct decide in H1; apply elem_of_cons; auto.
    apply elem_of_cons in H1 as [H1 | H1]; auto.
Qed.

Lemma remove_assoc_bucket_eq :
  forall k b b',
    b' = remove_assoc_list k b ->
    filter_key k b' = tl (filter_key k b).
Proof.
  intros k b.
  induction b as [|[k' v] t Ih]; simpl; intros b' H1; subst b'. auto.
  case_decide.
  - subst. by filter.
  - filter. auto.
Qed.

Lemma remove_assoc_bucket_ne :
  forall k k' b b',
    b' = remove_assoc_list k b ->
    k' ≠ k ->
    filter_key k' b' = filter_key k' b.
Proof.
  intros k k' b.
  induction b as [|[k'' v] t Ih]; simpl; intros b' H1 H2; subst b'; auto.
  case_decide.
  - subst. by filter.
  - apply filter_key_cons. by apply Ih.
Qed.

Fixpoint find_assoc (k : K) (b : bucket) : option V :=
  match b with
  |Nil => None
  |Cons k' v t =>
     if _eq k k'
     then Some v
     else find_assoc k t
  end.

Lemma find_assoc_wp k b :
  wp (find_assoc k b)
    (λ o, o = head (map snd (filter_key k (b2l b)))).
Proof.
  induction b as [|k' v t Ih].
  - wp_ret.
  - simpl. wp_if.
    + wp_ret. subst. simpl. by filter.
    + wp_op Ih. simpl. intros. subst.
      simpl. by filter.
Qed.

(* -------------------------------------------------------------------------- *)

Notation hmap := (gmap K (list V)).

(* Some definitions to facilitate working with functions as infinite
   maps.

    Remark: we leverage the fact that the Instance of the inhabited
    type class for lists is the empty list.*)

Lemma lookup_total_empty_list (m : hmap) k :
    m !! k = None ->
    m !!! k = [].
Proof.
  intros H. rewrite lookup_total_alt.
  by rewrite H.
Qed.

Lemma lookup_total_non_empty_list :
  forall (m : hmap) k x t,
    m !!! k = x :: t ->
    m !! k = Some(x :: t).
Proof.
  intros m k x t H.
  rewrite lookup_total_alt in H.
  destruct (m !! k); simpl in *; f_equal; done.
Qed.

Lemma lookup_total_Some :
  ∀ (m : hmap) k,
    m !! k ≠ None →
    m !! k = Some (m !!! k).
Proof.
  intros.
  remember (m !! k) as l.
  destruct l as [l|]. 2: done.
  by rewrite lookup_total_correct with (x:=l).
Qed.

Hint Rewrite
  lookup_total_Some
  lookup_total_empty_list
  using done : cmap.

Hint Rewrite
  (fin_maps.lookup_total_insert_ne (M:=gmap K) (A:=list V))
  (fin_maps.lookup_total_insert_eq (M:=gmap K) (A:=list V))
  using done : cmap.

Ltac hmap := autorewrite with cmap.

Tactic Notation "hmap" "in" hyp(h) :=
  autorewrite with cmap in h.

Tactic Notation "hmap" "in" "*" :=
  autorewrite with cmap in *.

Definition _add (m : hmap) (k : K) (v : V) := <[k:= v :: m !!! k]> m.

Lemma add_lookup_eq :
  forall m k v, _add m k v !!! k = v :: m !!! k.
Proof.
  intros.
  unfold _add.
  by hmap.
Qed.

Lemma add_lookup_neq :
  forall m k k' v,
    k ≠ k' →
    _add m k v !!! k' = m !!! k'.
Proof.
  intros.
  unfold _add.
  by hmap.
Qed.

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

Lemma add_ge :
  ∀ n m, n >= 0 -> m >= 0 -> n + m >= 0.
Proof.
  lia.
Qed.

Lemma cardinality_nonneg :
  ∀ m, cardinality m >= 0.
Proof.
  intros.
  induction m as [|k l] using map_first_key_ind.
  - by rewrite cardinality_empty.
  - erewrite cardinality_insert_fresh; eauto.
    generalize (@length_nonneg V l). lia.
Qed.

Lemma cardinality_delete_present :
  forall m k l n,
    cardinality m = n ->
    m !! k = Some l ->
    (cardinality (delete k m) + len l)%Z = n.
Proof.
  intros. subst n. unfold cardinality.
  rewrite map_fold_delete with (m:=m); tc.
Qed.

Lemma cardinality_delete_present_alt :
  forall m k l n,
    cardinality m = n ->
    m !! k = Some l ->
    cardinality (delete k m) = (n - len l)%Z.
Proof.
  intros. subst. unfold cardinality.
  rewrite map_fold_delete with (m:=m) (R:=eq); tc. lia.
Qed.

Lemma cardinality_insert :
  forall m k l n,
    cardinality m = n ->
    cardinality (<[k:=l]>m) = (n + len l - len (m !!! k))%Z.
Proof.
  intros m k l n H1.
  destruct (decide (m !! k = None)).
  - hmap. erewrite cardinality_insert_fresh by auto.
    length. lia.
  - rewrite <- insert_delete_eq.
    rewrite cardinality_insert_fresh with (n:=(n - len (m !!! k))%Z). lia.
    + erewrite <- cardinality_delete_present_alt; auto with lia.
      by hmap.
    + by rewrite lookup_delete_eq.
Qed.

Lemma cardinality_delete :
  forall m n k,
    cardinality m = n ->
    cardinality (delete k m) = (n - len (m !!! k))%Z.
Proof.
  intros m n k H1.
  remember (m !! k) as l eqn:E.
  destruct l as [l|].
  + erewrite cardinality_delete_present_alt; eauto.
    rewrite <- E. f_equal. symmetry.
    by apply lookup_total_correct.
  + hmap. length. by rewrite delete_id.
Qed.

Ltac cinsert n := erewrite cardinality_insert by auto.

Lemma cardinality_empty_lists :
  forall m,
    (∀ k, m !!! k = []) →
    cardinality m = 0%Z.
Proof.
  intros m Hempty.
  induction m as [|k v m Hnone Hfirst Ih] using map_first_key_ind. by hmap.
  erewrite cardinality_insert.
  - hmap. list. specialize Hempty with k.
    rewrite fin_maps.lookup_total_insert_eq in Hempty.
    subst. by list.
  - apply Ih. intros k'.
    specialize Hempty with k'.
    rewrite fin_maps.lookup_total_insert in Hempty.
    case_decide; auto.
    subst. by hmap.
Qed.

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
  destruct l. done.
  subst. by length.
Qed.

Lemma cardinality_rm_add_empty :
  forall m n k v,
    cardinality m = n ->
    m !!! k = [] ->
    cardinality (rm_add m k v) = (n + 1)%Z.
Proof.
  intros.
  unfold rm_add.
  erewrite cardinality_add by auto.
  erewrite cardinality_rm_empty by auto.
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
  erewrite cardinality_add by auto.
  erewrite cardinality_rm by auto. lia.
Qed.

Hint Rewrite
  cardinality_empty
  cardinality_add
  cardinality_rm
  cardinality_rm_empty
  cardinality_rm_add
  cardinality_rm_add_empty
  using done : card.

Lemma cardinality_extensionality :
  ∀ (m1 : hmap) m2,
    (∀ k, m1 !!! k = m2 !!! k) →
    cardinality m1 = cardinality m2.
Proof.
  induction m1 as [|k v m1 Hnone Hfirst Ih] using map_first_key_ind;
    intros m2 HLookup.
  - hmap. rewrite cardinality_empty.
    rewrite cardinality_empty_lists; auto.
    intros k. specialize HLookup with k.
    by rewrite lookup_total_empty in HLookup.
  - erewrite cardinality_insert by auto.
    hmap. rewrite Ih with (delete k m2).
    { erewrite cardinality_delete; auto.
      specialize HLookup with k. hmap in HLookup.
      subst v. by list. }
    { intros k'.
      destruct (decide (k = k')).
      - subst. rewrite fin_maps.lookup_total_delete_eq.
        by hmap.
      - rewrite fin_maps.lookup_total_delete_ne by auto.
       specialize HLookup with k'.
       by hmap in HLookup. }
Qed.

(* -------------------------------------------------------------------------- *)

(* Relates a list of buckets to a finite map of keys to lists of
   values, where [n] is the length of the [tbl].  For every key [k],
   [m !!! k] returns the list of values mapped to [k] in [tbl].
   If [k] is not in [tbl], [m !!! k] returns the empty list. *)

Definition valid_buckets (n : Z) (tbl : list bucket) (m : hmap) : Prop :=
  forall i b k,
    indexZ k n = i ->
    b = filter_key k (b2l (tbl !!! i)) ->
    m !!! k = map snd b.

(* If a key [k] is in a bucket of index [i], then [i] must correspond
   to the hash of [k]. *)
Definition no_garbage (n : Z) (tbl : list bucket) : Prop :=
  forall i (k : K) (v : V),
    valid i tbl ->
    (k, v) ∈ b2l (tbl !!! i) ->
    indexZ k n = i.

(* Correlates a hash table with a total function that maps keys to a
   list of values.  Here we combine the previous two definitions as
   well as stating that a hash table has the same properties as a
   non-empty array.  The condition that the table must be non-empty is
   necessary for array accesses. *)
Definition isHashtblArray
  (arr : array bucket) (n : Z) (m : hmap) : Prop :=
  ∃ l, isArray arr l ∧ n = len l ∧ (0 < n)%Z ∧
         no_garbage n l ∧ valid_buckets n l m.

(* Relates population field of the hash table with the cardinality
   of the map. *)
Definition isHashtblWithPop
  (arr : array bucket) (n : Z) (pop : int) (m : hmap) :=
    isHashtblArray arr n m ∧
      isInt pop (cardinality m).

(* If the array can still be resized, the double of the
   cardinality cannot exceed the size of the array. *)
Definition max_cardinality (array_size : Z) (card : Z) :=
  array_size * 2 ≤ max_array_length -> card * 2 ≤ array_size.

(* Places an upper bound on the cardinality of the table in relation
   to the size of the array. *)
Definition isHashtbl (h : hashtbl) (m : hmap) :=
  let (popu, arr) := h in
    ∃ n, isHashtblWithPop arr n popu m ∧
           max_cardinality n (cardinality m).

(* Tactics to destruct the previous definitions. *)

Local Ltac destructIsHashtblArray :=
  match goal with h: isHashtblArray _ _ _ |- _ =>
    unfold isHashtblArray in h;
    let l := fresh "l" in
    destruct h as (l&?);
    unpack;
    arrays
  end.

Local Ltac destructIsHashtblResize :=
  match goal with h: isHashtblWithPop _ _ _ _ |- _ =>
    unfold isHashtblWithPop in h;
    unpack;
    destructIsHashtblArray
  end.

Local Ltac destructIsHashtbl :=
  match goal with h: isHashtbl ?v _ |- _ =>
    destruct v;
    unfold isHashtbl in h;
    unfold max_cardinality in h;
    let n := fresh "n" in
    let c := fresh "c" in
    destruct h as (n&?);
    destruct h as (c&?);
    unpack;
    destructIsHashtblResize
  end.

(* Introduces the goals needed to prove [isHashtbl _ _].  Can also by
   used to prove the ancillary predicates.  *)
Local Ltac introIsHashtbl :=
  unfold isHashtbl;
  unfold isHashtblWithPop;
  unfold isHashtblArray;
  unfold max_cardinality;
  eexists; pack; eauto; list; try lia.

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

(* -------------------------------------------------------------------------- *)

Definition create (n : int) : hashtbl :=
  do a ← make n Nil ; (0, a).

Lemma wp_create :
  ∀Int _n n,
    (0 < n ≤ max_array_length)%Z ->
    wp (create _n) (λ h, isHashtbl h ∅).
Proof.
  intros _n n H1 H2. unfold create. wp_make a.
  wp_ret. introIsHashtbl.
  { unfold no_garbage. intros ???? H3.
    do 2 list in *.
    by apply not_elem_of_nil in H3. }
  { intros ?**. list in *. by subst. }
  { by rewrite cardinality_empty. }
Qed.

(* -------------------------------------------------------------------------- *)

Fixpoint bucket_iter_right {S} (b : bucket) (s : S) f : S:=
  match b with
  |Nil => s
  |Cons k v b' =>
     do s' ← bucket_iter_right b' s f;
     f k v s' end.

Hint Rewrite
  @reverse_cons
  @elem_of_reverse : clist.

Lemma wp_bucket_iter_right {S} b f :
  ITER_LIST [] (reverse (b2l b))
    (λ (x : K * V) s Q,
      forall k v, x = (k, v) -> wp (f k v s) Q)
    (λ (s : S) Q, wp (bucket_iter_right b s f) Q).
Proof.
  induction b as [|k v b Ih];
    simpl bucket_iter_right;
    intros; ITER; list in *. wp_ret.
  wp_op Ih shadowing:s.
  - intros. wp_op Hbody; auto.
    simpl. list. by apply prefix_app_r.
  - wp_op Hbody; permitted in *; complete in *; simpl.
    + subst. by list.
    + intros. eexists.
      split; auto. subst. by list.
Qed.

Definition iter_rev {S} (h : hashtbl) (s : S) f : S :=
  iteri (snd h) s (fun _ b s => bucket_iter_right b s f).

Definition complete (k : K) (xs : hmap) (history : list (K * V)) :=
  map snd (filter_key k history) = reverse (xs !!! k).

Definition permitted (xs : hmap) history :=
    ∀ k, map snd (filter_key k history) `prefix_of` (reverse (xs !!! k)).

Definition ITER_HMAP {S}
  (xs : hmap)
  (body : K → V → S → WP S)
  (loop : S → WP S)
    : Prop
    :=
    @ITER (list (K * V)) (eq)
      []
      ( λ h, ∀ k, complete k xs h) S
      ( λ history0 history1 s Q,
        ∀ k v,
          history0 ++ [(k, v)] = history1 →
          permitted xs history1 ->
          body k v s Q )
      loop.

Lemma nil_permitted :
  forall xs, permitted xs [].
Proof.
  intros ** ?.
  apply prefix_nil.
Qed.

Lemma reverse_map :
  forall {A B} (l : list A) (f : A -> B),
    reverse (map f l) = map f (reverse l).
Proof.
  intros.
  induction l as [|h t Ih]. auto.
  simpl. do 2 rewrite reverse_cons.
  rewrite map_app. by rewrite Ih.
Qed.

Lemma filter_list_key_nin :
  forall k b,
    (∀ v, (k, v) ∉ b) ->
    filter_key k b = [].
Proof.
  intros k b H1.
  induction b as [|[k' v] t Ih]; auto.
  rewrite filter_cons_False.
  + apply Ih. intros v'.
    specialize H1 with v'.
    rewrite list.not_elem_of_cons in *.
    by unpack.
  + simpl. intros ?. subst.
    specialize H1 with v.
    rewrite list.not_elem_of_cons in *.
    by unpack.
Qed.

Lemma permitted_start_next :
  ∀ n j h m,
  (∀ k v, indexZ k n >= j → (k, v) ∉ h) →
  (∀ k : K, indexZ k n < j → complete k m h) →
  permitted m h.
Proof.
  intros n j h m H1 H2 k.
  destruct (decide (indexZ k n < j)).
  + by rewrite H2 by lia.
  + assert (Hempty: filter_key k h = []).
    { apply filter_list_key_nin. intros. auto with lia. }
    rewrite Hempty. apply prefix_nil.
Qed.

Lemma prefix_map :
  forall A B l1 l2 (f : A -> B),
    l1 `prefix_of` l2 →
    map f l1 `prefix_of` map f l2.
Proof.
  intros ????? [??].
  eexists.
  rewrite <- map_app.
  by f_equal.
Qed.

Lemma prefix_filter :
  forall l1 l2 k,
    l1 `prefix_of` l2 →
    filter_key k l1 `prefix_of` filter_key k l2.
Proof.
  induction l1 as [|h t Ih];
    intros l2 k [l3 H1]. apply prefix_nil.
  rewrite H1.
  rewrite filter_cons. simpl.
  case_decide.
  + rewrite filter_cons_True by auto.
    apply prefix_cons. apply Ih.
    by apply prefix_app_r.
  + rewrite filter_cons_False by auto.
    apply Ih. by apply prefix_app_r.
Qed.

Lemma permitted_add_next :
  ∀ n k v b l i m h h' h'',
    valid i l →
    b = l !!! i →
    (forall k', indexZ k' n >= i → filter_key k' h = []) →
    valid_buckets n l m →
    no_garbage n l →
    h' ++ {[(k, v)]} = h'' →
    h'' `prefix_of` reverse (b2l b) →
    permitted m (h ++ h') →
    permitted m (h ++ h' ++ [(k, v)]).
Proof.
  intros n k v b l i m h h' h''
    HvalidI Hb Hfilterk'
    Hvalid Hgarbage Hh' Hprefix Hpermitted k'.
    assert (A1: (k, v) ∈ b2l (l !!! i)).
  { apply elem_of_reverse.
    apply elem_of_prefix with (l1:= h''); subst; auto.
    apply elem_of_app. right.
    by apply list_elem_of_singleton. }
  assert (A2 : indexZ k n = i).
  { apply Hgarbage with v; auto. }
  destruct (decide (indexZ k' n = i)) as [E | E].
  { rewrite filter_app. rewrite map_app.
    rewrite filter_app.
    rewrite Hfilterk' by lia.
    list. rewrite <- filter_app.
    rewrite Hvalid; auto.
    rewrite reverse_map.
    rewrite <- filter_reverse.
    apply prefix_map.
    apply prefix_filter.
    subst. by rewrite E. }
  { rewrite app_assoc. rewrite filter_app.
    rewrite filter_key_cons_False.
    - list. apply Hpermitted.
    - intros ?. by subst. }
Qed.

Definition inv_array {S} n m :=
  λ h (i : Z) (s : S),
         (forall k,
             indexZ k n < i → complete k m h).

Definition inv_array_unreached {S} n (m : hmap) :=
  λ (h : list (K * V)) (i : Z) (s : S),
    (forall k v,
        indexZ k n >= i → (k, v) ∉ h).

Definition inv_bucket {S} m h inv :=
  λ b (s : S), ∀ h',
      h' = h ++ b →
      inv h' s ∧ permitted m h'.

Lemma inv_array_preserve :
  ∀ {S} tbl n m h j j' b (s' : S) (s'' : S),
    j' = (j + 1)%Z ->
    valid j tbl ->
    no_garbage n tbl ->
    valid_buckets n tbl m ->
    inv_array n m h j s' ->
    inv_array_unreached n m h j s' ->
    b = b2l (tbl !!! j) ->
    inv_array n m (h ++ reverse b) j' s''.
Proof.
  unfold inv_array, inv_array_unreached.
  intros S tbl n m h j j' b s' s''
    ?? NG Hvalid Hcomplete Hunreached **.
  unfold complete.
  rewrite filter_app.
  set (i':=indexZ k n).
  destruct (decide (i' = j)); subst.
  { rewrite filter_key_nin. 2: auto with lia.
    simpl. rewrite filter_reverse.
    rewrite <- reverse_map. f_equal.
    rewrite Hvalid; auto. }
  { rewrite filter_key_nin with (b:=reverse _).
    - list. apply Hcomplete. lia.
    - intros v. rewrite elem_of_reverse.
      intro Hnin. apply NG in Hnin; lia.
  }
Qed.

(* -------------------------------------------------------------------------- *)

Lemma wp_iter_rev_aux :
  ∀ S arr f n m pop,
    isHashtblArray arr n m →
    ITER_HMAP m
    (λ k v (s : S) Q, wp (f k v s) Q)
    (λ s Q, wp (iter_rev (pop, arr) s f) Q).
Proof.
  unfold iter_rev. intros.
  destructIsHashtblArray. ITER. simpl.
  wp_op wp_iteri with invariant:
      (λ (i: Z) (s : S),
        ∃ h, inv h s ∧
               inv_array n m h i s ∧
               inv_array_unreached n m h i s).
  { unfold inv_array, inv_array_unreached.
    exists []. pack; auto with lia.
    apply not_elem_of_nil. }
  { intros j j' s' [h (Hinv & Hcomplete & Hunreached)]
      ???? b Hbucket.
      wp_op wp_bucket_iter_right
        with invariant:(inv_bucket m h inv);
        unfold inv_bucket.
    - intros. subst h'. list. split. auto.
      apply permitted_start_next with (n:=n) (j:=j);
        auto.
    - intros h' h'' s'' Hpermitted_inner **.
      specialize Hpermitted_inner with (h ++ h').
      destruct Hpermitted_inner. auto.
      wp_op Hbody; subst x.
      + list. eapply permitted_add_next; eauto.
        intros. apply filter_key_nin.
        auto with lia.
      + intros s''' Hinv' h'''.
        list in *; split. by subst.
        subst h'''. rewrite <- H10.
        eapply permitted_add_next; eauto.
        intros. apply filter_key_nin. auto with lia.
    - intros s'' [h' [Hinv3?]].
      exists (h ++ (reverse (b2l b))).
      specialize Hinv3 with (h ++ h') as
        [Hinv3 Hpermitted']; auto.
      subst h'. pack. auto.
      + eapply inv_array_preserve; subst; eauto.
      + unfold inv_array_unreached. intros.
        rewrite not_elem_of_app. split;
        eauto with lia. list. intro Hnin.
        subst. apply H2 in Hnin; lia. }
  simpl. intros. unpack. subst. eexists.
  split; eauto with lia.
Qed.

Definition wp_iter_rev :
 ∀ S f h m,
   isHashtbl h m →
   ITER_HMAP m
     (λ k v (s : S) Q, wp (f k v s) Q)
     (λ s Q, wp (iter_rev h s f) Q).
Proof.
  intros.
  destructIsHashtbl.
  eapply wp_iter_rev_aux.
  unfold isHashtblArray.
  by pack.
Qed.

(* -------------------------------------------------------------------------- *)

Definition add' (k : K) (v : V) (arr : array bucket) :=
  do _n ← PArray.length arr;
  do i ← index k _n;
  do b ← get arr i;
  do h' ← set arr i (Cons k v b);
  h'.

Hint Rewrite
  @listz.list_elem_of_singleton
  @elem_of_app : clist.

Lemma no_garbage_insert :
  forall n k v i tbl b,
  len tbl = n ->
  no_garbage n tbl ->
  i = indexZ k n ->
  b = tbl !!! i ->
  no_garbage n (<[i:=Cons k v b]> tbl).
Proof.
  unfold no_garbage.
  intros n k v i tbl b H1 H2 H3 H4.
  intros i' k' v' H5 H6.
  list in H5.
  destruct (decide (i = i')).
  { subst i. list in H6.
    simpl in *.
    rewrite elem_of_cons in H6.
    destruct H6 as [H6 | H6].
    - injection H6. intros. by subst.
    - subst. eauto. }
  { list in H6. eauto. }
Qed.

Lemma valid_insert_bucket_eq :
  forall k v l m n b b',
    n = len l ->
    valid_buckets n l m ->
    b = b2l (l !!! indexZ k n) ->
    b' = filter_key k ((k, v) :: b) ->
    v :: (m !!! k) = map snd b'.
Proof.
  intros. subst. filter. simpl. f_equal.
  eauto with subst.
Qed.

Lemma valid_insert_bucket_ne :
  forall k k' i v l n m b b',
    n = len l ->
    valid_buckets n l m ->
    indexZ k n = i ->
    indexZ k' n = i ->
    b = b2l (l !!! indexZ k n) ->
    b' = filter_key k' ((k, v) :: b) ->
    k ≠ k' ->
    m !!! k' = map snd b'.
Proof.
  intros. subst. filter.
  eauto with subst.
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
    valid_buckets n (<[i:=Cons k v b]> tbl)
      (_add m k v).
Proof.
  intros i n tbl k v b m ???? H5.
  intros i' b' k' ? ?.
  (* The updated map as described in the postcondition
     accurately models the updated hash table. *)
  unfold _add. destruct (decide (k = k')).
  + (* When we apply the updated map with the key we pass as
         argument. *)
    subst k'. hmap.
    eapply valid_insert_bucket_eq;
      subst; by list.
  + hmap. case_bucket k n i'; subst;
      list; simpl; filter; eauto.
Qed.

Lemma wp_add' :
  ∀ arr n m k v,
    isHashtblArray arr n m ->
    wp (add' k v arr)
      (λ h, isHashtblArray h n (_add m k v)).
Proof.
  intros.
  unfold add'.
  destructIsHashtblArray.
  wp_length _n.
  wp_bind_eq.
  index_intro k _n n.
  wp_get b.
  wp_set.
  wp_ret.
  introIsHashtbl.
  - subst. apply no_garbage_insert; auto.
  - apply valid_buckets_insert; by subst.
Qed.

Definition resize (h : hashtbl) : hashtbl :=
  do n ← length h.2;
  do n ← n * 2;
  if n <=? max_length then
  do a ← make n Nil;
  do a ← iter_rev h a add';
  (h.1, a)
  else h.

Lemma hashtbl_extensionality :
  forall h m1 m2,
    isHashtbl h m1 →
    (forall k, m1 !!! k = m2 !!! k) →
    isHashtbl h m2.
Proof.
  intros h m1 m2 H Helts.
  destructIsHashtbl.
  introIsHashtbl.
  + intros i' b k Hindex Hbucket.
    rewrite <- Helts.
    eauto.
  + by erewrite cardinality_extensionality.
  + erewrite <- cardinality_extensionality; eauto.
Qed.

Lemma reverse_injective :
  forall A (l1 : list A) l2,
    reverse l1 = reverse l2 ->
    l1 = l2.
Proof.
  intros A l1 l2 H1.
  rewrite <- reverse_involutive.
  rewrite <- reverse_involutive with (l:=l1).
  by f_equal.
Qed.

Definition resize_inv n :=
  λ (l : list (K * V)) arr, ∃ m',
      isHashtblArray arr n m' ∧
        ∀ k, map snd (filter_key k l) = reverse (m' !!! k).

Definition resize_inv_init :
  ∀ A a (l : list A) n,
    n = len l ->
    0 < n ->
    isArray a (replicate (len l * 2) Nil) ->
    resize_inv (n * 2) [] a.
Proof.
  intros. unfold resize_inv.
  simpl. subst n. exists ∅. introIsHashtbl.
  { intros ???? Helem.
    do 2 list in *.
    by apply not_elem_of_nil in Helem. }
  { intros ?**. list in *. by subst. }
Qed.

Lemma resize_inv_step :
  forall k v k' l b x,
    (∀ k, map snd (filter_key k b) = reverse (x !!! k)) ->
    l = (filter_key k' (b ++ [(k, v)])) ->
    map snd l = reverse (_add x k v !!! k').
Proof.
  intros k v k' l **.
  subst l.
  rewrite filter_app.
  destruct (decide (k = k')).
  { subst. rewrite add_lookup_eq.
    rewrite reverse_cons.
    rewrite map_app. filter. simpl. by f_equal. }
  { rewrite add_lookup_neq by auto. filter. by list. }
Qed.

Lemma reverse_inv_complete :
  forall h pop n m m' hist,
    isHashtblArray h n m ->
    (∀ k, map snd (filter_key k hist) = reverse (m' !!! k)) ->
    (∀ k, complete k m hist) ->
    (isInt pop (cardinality m')) ->
    cardinality m' * 2 ≤ n ->
    isHashtbl (pop, h) m'.
Proof.
  unfold complete.
  intros h pop n m m' hist Htbl Hinv Hcomplete Hcard Hsize.
  destructIsHashtblArray.
  assert (A : ∀ k : K, m !!! k = m' !!! k).
  { intro k. apply reverse_injective.
    by rewrite <- Hcomplete. }
  eapply hashtbl_extensionality with (m2:=m'); auto.
  introIsHashtbl;
  erewrite cardinality_extensionality;
  subst; eauto.
Qed.

(* Try to eliminate these. *)

Instance isBool_leb_proj :
  ∀Int _i i ,
  ∀Int _j j ,
  isBool1 (_i ≤? _j) (proj i ≤ proj j).
Proof.
  intros. eapply isBool1_intro. rewrite leb_spec.
  destructIsInt. lia.
Qed.

Instance isBool_ltb_proj :
  ∀Int _i i ,
  ∀Int _j j ,
  isBool (_i <? _j)
    (proj i < proj j) (proj i >= proj j)%Z.
Proof.
  intros. eapply isBool_intro.
  + rewrite ltb_spec. destructIsInt. lia.
  + lia.
Qed.

Lemma wp_resize :
  forall arr n c pop m,
    c = (cardinality m - 1)%Z ->
    isHashtblWithPop arr n pop m ->
    (n * 2 ≤ max_array_length -> c * 2 ≤ n) ->
    wp (resize (pop, arr)) (λ h, isHashtbl h m).
Proof.
  unfold resize.
  intros.
  simpl.
  destructIsHashtblResize.
  arrays.
  wp_length _n.
  wp_bind_eq.
  assert (isInt (_n * 2) (len l * 2)) by tc.
  wp_if.
  2: { subst. introIsHashtbl. }
  generalize unsigned_twice_max_array_length.
  intros.
  wp_make a'.
  assert (isHashtblArray arr n m) by introIsHashtbl.
  wp_op wp_iter_rev_aux with invariant:(resize_inv (n * 2)).
  - eapply resize_inv_init; subst; eauto with lia.
  - intros l1 l2 **. unfold resize_inv in *.
    unpack. wp_op wp_add'.
    simpl. intros. eexists. split; eauto. intros.
    eapply resize_inv_step; subst; eauto.
  - unfold resize_inv in *. intros. unpack.
    eapply reverse_inv_complete; subst; eauto.
    lia.
Qed.

Definition inc_pop h :=
  do (pop, h) ← h;
  do len ← PArray.length h;
  do pop' ← pop + 1;
  do h' ← (pop', h);
  if len <? pop' * 2
  then resize h'
  else h'.

Lemma wp_inc_pop :
  ∀ arr n m pop c,
    c = cardinality m ->
    isHashtblArray arr n m ->
    isInt (pop + 1) c ->
    max_cardinality n (c - 1) ->
    wp (inc_pop (pop, arr))
      (λ h, isHashtbl h m).
Proof.
  unfold max_cardinality. intros.
  unfold inc_pop.
  destructIsHashtblArray.
  wp_bind_eq.
  wp_length _n.
  do 2 wp_bind_eq.
  wp_if.
  - subst c. wp_op wp_resize. by introIsHashtbl. auto.
  - wp_ret. introIsHashtbl. tc.
Qed.

Definition add (h : hashtbl) k v :=
  do (pop, h) ← h;
  do h' ← add' k v h;
  inc_pop (pop, h').

(* change the name of the model functions *)

Lemma wp_add :
  forall h m k v,
    isHashtbl h m ->
    wp (add h k v)
      (λ h, isHashtbl h (_add m k v)).
Proof.
  intros h m k v H.
  unfold add.
  destructIsHashtbl.
  wp_bind_eq.
  wp_op wp_add'.
  { introIsHashtbl. }
  intros x Harr. simpl in Harr.
  destructIsHashtblArray.
  wp_op wp_inc_pop.
  - introIsHashtbl.
  - erewrite cardinality_add by auto. tc.
  - erewrite cardinality_add by auto. by list.
  - auto.
Qed.

(* -------------------------------------------------------------------------- *)

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

Lemma no_garbage_remove n tbl k :
  forall i b b',
    no_garbage n tbl ->
    b = tbl !!! i ->
    i = indexZ k n ->
    n = len tbl ->
    (b2l b') = remove_assoc_list k (b2l b) ->
    no_garbage n (<[i:=b']> tbl).
Proof.
  intros i b b' NG H1 ** i' k' v??.
  list in *.
  apply NG with v; auto.
  destruct (decide (i = i'));
    subst; list in *. 2: auto.
  apply remove_assoc_in with k.
  by rewrite <- H2.
Qed.

Lemma valid_buckets_remove :
  forall n i k b b' tbl m,
    0 < n ->
    n = len tbl ->
    i = indexZ k n ->
    b = tbl !!! i ->
    (b2l b') = remove_assoc_list k (b2l b) ->
    valid_buckets n tbl m ->
    valid_buckets n (<[i:=b']> tbl) (rm m k)
  .
Proof.
  intros n i k b b' tbl m H1 H2 H3 H4 H5 H6 i' b'' k' H7 H8.
  unfold rm.
  destruct (decide (k = k')).
  { subst. list.
    erewrite remove_assoc_bucket_eq by eauto.
    hmap. list. f_equal. eauto; by subst. }
  { hmap. case_bucket k' n i.
    + subst. list.
      erewrite remove_assoc_bucket_ne; eauto.
    + subst. list. eauto. }
Qed.

Lemma non_empty_bucket :
  forall n tbl i m b k,
  valid_buckets n tbl m ->
  i = indexZ k n ->
  b = tbl !!! i ->
  (∃ v : V, (k, v) ∈ b2l b) ->
  m !!! k ≠ [].
Proof.
  intros n tbl i m b k H1 H2 H3 [v H4].
  rewrite H1 with (i:=i) (b:=filter_key k (b2l b)) by auto with subst.
  intros H5.
  apply map_eq_nil in H5.
  by apply filter_nil_not_elem_of with (l:=b2l b) (x:=(k, v)) in H5.
Qed.

Lemma map_nil_elim :
  forall A B l (f : A -> B), l = [] -> map f l = [].
Proof.
  intros. by subst.
Qed.

Lemma empty_bucket :
  forall n tbl i m b k,
  valid_buckets n tbl m ->
  i = indexZ k n ->
  b = tbl !!! i ->
  (forall v : V, (k, v) ∉ b2l b) ->
  m !!! k = [].
Proof.
  intros n tbl i m b k HValid ???.
  erewrite HValid by auto with subst.
  apply map_nil_elim. subst.
  by rewrite filter_key_nin.
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
  wp_bind_eq.
  wp_length _n.
  index_intro k _n n.
  wp_bind_eq.
  wp_get b.
  wp_op remove_assoc_wp.
  simpl. intros [r b'].
  intros. unpack.
  wp_set.
  eapply wp_bind
    with(P:=λ _n, isInt _n (cardinality (rm m k))).
  { wp_if; wp_ret.
    - erewrite cardinality_rm; tc.
      by eapply non_empty_bucket.
    - erewrite cardinality_rm_empty; tc.
      by eapply empty_bucket. }
 intros. wp_ret. introIsHashtbl.
  - subst. by eapply no_garbage_remove.
  - eapply valid_buckets_remove; by subst.
  - list in *. subst. destruct (decide (m !!! k = [])).
    { erewrite cardinality_rm_empty; eauto with lia. }
    { erewrite cardinality_rm; eauto. lia. }
Qed.

(* -------------------------------------------------------------------------- *)

Definition replace (h : hashtbl) (k : K) (v : V) :=
  do (n, h) ← h;
  do l ← length h;
  do i ← index k l;
  do b ← get h i;
  do (r, b') ← remove_assoc k b;
  do b' ← Cons k v b';
  do h' ← set h i b';
  if r then (n, h') else inc_pop (n, h').

Lemma decompose_replace :
  forall (i : Z) k v b (tbl : list bucket),
    <[i:=Cons k v b]> tbl =
      <[i:=Cons k v b]>(<[i:=b]>tbl).
Proof.
  intros. by list.
Qed.

Lemma wp_replace :
  forall h m k v,
    isHashtbl h m ->
    wp (replace h k v) (λ h, isHashtbl h (rm_add m k v)).
Proof.
  intros h m k v H.
  unfold replace.
  destructIsHashtbl.
  wp_bind_eq.
  wp_length _n.
  index_intro k _n n.
  wp_bind_eq.
  wp_get b.
  wp_op remove_assoc_wp.
  intros [r b'] ?. unpack.
  wp_bind_eq.
  wp_set.
  assert (isHashtblArray a n (rm_add m k v)).
  { introIsHashtbl; simpl; rewrite decompose_replace.
    - apply no_garbage_insert; (try (by list)).
      eapply no_garbage_remove; subst; by list.
    - apply valid_buckets_insert; (try by list); try lia.
      apply valid_buckets_remove with b; subst; auto.
  }
  destructIsHashtblArray.
  wp_if.
  - wp_ret. introIsHashtbl;
      erewrite cardinality_rm_add; tc;
      by eapply non_empty_bucket.
  - wp_op wp_inc_pop. introIsHashtbl. 3:auto.
    all:
      unfold max_cardinality;
      erewrite cardinality_rm_add_empty;
      tc; try lia; by eapply empty_bucket.
Qed.

(* -------------------------------------------------------------------------- *)

Definition get (h : hashtbl) (k : K) :=
  do (_, h) ← h;
  do n ← length h;
  do i ← index k n;
  do b ← get h i;
  find_assoc k b.

Lemma wp_get :
  forall h m k,
    isHashtbl h m ->
    wp (get h k) (λ v, head (m !!! k) = v).
Proof.
  intros h m k H.
  unfold get.
  destructIsHashtbl.
  wp_bind_eq.
  wp_length _n.
  index_intro k _n n.
  wp_bind_eq.
  wp_get b.
  wp_op find_assoc_wp.
  wp_ret. intros.
  erewrite H4 with (i:=i') (b:=filter_key k (b2l b)); subst; auto.
Qed.

Definition population (h : hashtbl) : int :=
  fst h.

Lemma wp_population :
  forall h m,
    isHashtbl h m ->
    wp (population h) (λ n, isInt n (cardinality m)).
Proof.
  intros.
  unfold population.
  wp_ret.
  by destructIsHashtbl.
Qed.

Definition lmap := gmap K V.

Definition lean (m : hmap) (lm : lmap) :=
  ∀ k, (m !!! k = [] ∨ ∃ v, m !!! k = [v]) ∧
  lm !! k = head (m !!! k).

Definition isLeanHashtbl (h : hashtbl) (lm : lmap) :=
  ∃ m, isHashtbl h m ∧ lean m lm.

Ltac destructIsLeanHashtbl :=
  match goal with h: isLeanHashtbl ?v _ |- _ =>
    destruct v;
    unfold isLeanHashtbl in h;
    let m := fresh "m" in
    destruct h as (m&?);
    unpack
  end.

Ltac destructLean k :=
  match goal with H: lean _ _ |- _ =>
    unfold lean in H;
    specialize H with k;
    unpack
  end.

Ltac introLean :=
  unfold isLeanHashtbl;
  simpl; intros;
  eexists; split; eauto;
  intros k'; split.

Ltac simplHmap :=
  unfold rm_add, _add, rm; hmap.

Lemma lean_rm_add_lookup_eq :
  ∀ m lm k v,
  lean m lm ->
  rm_add m k v !!! k = [v].
Proof.
  intros m lm k v Hlean.
  simplHmap.
  unfold lean in Hlean.
  specialize Hlean with k as [[H|[??H]]?];
    by rewrite H.
Qed.

Lemma lean_rm_lookup_eq :
  ∀ m lm k,
    lean m lm ->
    rm m k !!! k = [].
Proof.
  intros m lm k Hlean.
  simplHmap.
  unfold lean in Hlean.
  specialize Hlean with k as [[H|[??H]]?];
    by rewrite H.
Qed.

Lemma wp_replace_lean :
  forall h k v lm,
    isLeanHashtbl h lm ->
    wp (replace h k v)
      (λ h, isLeanHashtbl h (<[k:=v]> lm)).
Proof.
  intros.
  destructIsLeanHashtbl.
  wp_op wp_replace.
  introLean;
  destruct (decide (k' = k)).
  { right. subst. eexists.
    erewrite lean_rm_add_lookup_eq; eauto. }
  { simplHmap.
    by destructLean k'. }
  { subst. rewrite lookup_insert_eq with (m:=lm).
    unfold rm_add, _add, rm. by hmap. }
  { simplHmap.
    rewrite lookup_insert_ne with (m:=lm) by auto.
    by destructLean k'. }
Qed.

Lemma wp_remove_lean :
  forall k h lm,
    isLeanHashtbl h lm ->
    wp (remove h k) (λ h, isLeanHashtbl h (delete k lm)).
Proof.
  intros.
  destructIsLeanHashtbl.
  wp_op wp_remove.
  simpl. intros h' H2.
  introLean; destruct (decide (k' = k)).
  + left. subst. eapply lean_rm_lookup_eq; eauto.
  + destructLean k'. by simplHmap.
  + subst. erewrite lean_rm_lookup_eq by eauto.
    simpl. apply lookup_delete_eq with (m:=lm).
  + destructLean k'. simplHmap.
    by rewrite lookup_delete_ne with (m:=lm).
Qed.

Lemma wp_get_lean :
  forall k h lm,
    isLeanHashtbl h lm ->
    wp (get h k) (λ v, lm !! k = v).
Proof.
  intros.
  destructIsLeanHashtbl.
  wp_op wp_get.
  simpl. intros ? H1.
  destructLean k.
  by rewrite <- H1.
Qed.

Lemma lean_delete :
  forall m lm k v,
  lm !! k = None ->
  lean m (<[k:=v]> lm) ->
  lean (delete k m) lm.
Proof.
  intros m lm k v Hnone Hlean.
  intros k'; split; destruct (decide (k = k')).
  + left. subst. by rewrite lookup_total_delete_eq.
  + destruct Hlean with k'.
    rewrite lookup_total_delete_ne; auto.
  + subst. by rewrite lookup_total_delete_eq.
  + rewrite lookup_total_delete_ne by auto.
    destruct Hlean with k' as [? Hlean'].
    by rewrite lookup_insert_ne with (m:=lm) in Hlean'.
Qed.

Lemma lean_hmap_empty :
  ∀ m, lean m ∅ -> cardinality m = 0%Z.
Proof.
  intros m Hlean.
  induction m as [|k v m Hnone Hfirst Ih]
                   using map_first_key_ind.
  - by rewrite cardinality_empty.
  - erewrite cardinality_insert_fresh; eauto.
    destruct Hlean with k as [Hlist HLookup].
    destruct Hlist as [Hlist | [v' Hlist]].
    { hmap in Hlist. subst. list. rewrite Ih; auto.
      intros k'; split; destruct (decide (k = k')).
      + subst. left. by hmap.
      + destruct Hlean with k' as [H1 _].
        by rewrite fin_maps.lookup_total_insert_ne in H1.
      + subst. by hmap.
      + destruct Hlean with k' as [_ H1].
        rewrite H1. by hmap. }
    { rewrite Hlist in HLookup.
      simpl in HLookup.
      by apply lookup_empty_Some in HLookup. }
Qed.

Lemma cardinality_lean_size :
  forall lm m,
    lean m lm ->
    cardinality m = Z.of_nat (base.size lm).
Proof.
  induction lm as
    [|k v lm Hnone Hfirst Ih] using map_first_key_ind.
  - intros. by rewrite lean_hmap_empty.
  - intros m Hlean.
    rewrite map_size_insert_None with (m:=lm) by auto.
    rewrite <- cardinality_delete_present with
      (n:=cardinality m) (k:=k) (m:=m) (l:=[v]).
    { length. rewrite Ih; auto.
      eapply lean_delete; eauto. }
    { auto. }
    { destruct Hlean with k as [HNone HSome].
      rewrite fin_maps.lookup_insert_eq
        with (m:=lm) in HSome.
      destruct HNone as [HNone | [v' HNone]].
      - destruct (m !!! k); done.
      - rewrite HNone in HSome.
        simpl in *. injection HSome.
        intros. subst v'.
        by apply lookup_total_non_empty_list.
    }
Qed.

Lemma wp_population_lean :
  forall h lm,
    isLeanHashtbl h lm ->
    wp (population h) (λ n, isInt n (Z.of_nat (base.size lm))).
Proof.
  intros.
  destructIsLeanHashtbl.
  wp_op wp_population.
  simpl. intros.
  erewrite <- cardinality_lean_size; eauto.
Qed.

Definition complete_lean_key (k : K) (xs : lmap) (history : (list (K * V))) :=
  ∀ v, (k, v) ∈ history <-> xs !! k = Some v.

Definition complete_lean (xs : lmap) (history : (list (K * V))) :=
  (∀ k, complete_lean_key k xs history) ∧ NoDup history.

Definition permitted_lean (xs : lmap) (history : (list (K * V))) :=
    (∀ k v,
      (k, v) ∈ history -> xs !! k = Some v) ∧ NoDup history.

Definition ITER_LMAP {S}
  (xs : lmap)
  (body : K → V → S → WP S)
  (loop : S → WP S)
    : Prop
    :=
    ITER
      []
      ( λ h, complete_lean xs h)
      ( λ history0 history1 s Q,
        ∀ k v,
          history0 ++ [(k, v)] = history1 ->
          permitted_lean xs history1 ->
          body k v s Q )
      loop.

Definition inv_bucket_lean {S} inv lm :=
  λ h (s : S),
    inv h s ∧ permitted_lean lm h.

Lemma prefix_cons_inv {A} (x : A) y l1 l2 :
  x :: l1 `prefix_of` y :: l2 ->
  x = y ∧ l1 `prefix_of` l2.
Proof.
  intros H. split.
  - by eapply prefix_cons_inv_1.
  - by eapply prefix_cons_inv_2.
Qed.

Lemma filter_key_prefix l k v v':
  ∀ l',
    l' = map snd (filter_key k l) ->
    l'`prefix_of` [v'] ->
    (k, v) ∈ l ->
    l' = [v'].
Proof.
  intros l' H1 H2 H3.
  destruct l' as [|v'' l'].
  + symmetry in H1. apply map_eq_nil in H1.
    by eapply filter_nil_not_elem_of
      with (l:=l) (x:=(k, v)) in H1; eauto.
  + apply prefix_cons_inv in H2 as [? H2].
    apply prefix_nil_inv in H2. by subst v'' l'.
Qed.

Lemma filter_key_singleton k l v v' :
  map snd (filter_key k l) = [v'] ->
  (k, v) ∈ l ->
  v' = v.
Proof.
  intros H1 H2.
  assert (A : (k, v) ∈ filter_key k l).
  { by rewrite list_elem_of_filter. }
  destruct (filter_key k l) as [|[k' v''] l'].
  { by apply elem_of_nil in A. }
  { rewrite map_cons in H1. simpl in H1.
    injection H1. intros E. subst.
    apply map_eq_nil in E. subst.
    apply list_elem_of_singleton in A.
    injection A. intros. by subst. }
Qed.

Lemma permitted_to_lean m lm l:
  permitted m l ->
  lean m lm ->
  permitted_lean lm l.
Proof.
  unfold permitted.
  intros HP Hlean. split.
  - intros k v Helem. destructLean k.
    specialize HP with k.
    destruct Hlean as [Hlean | [v' Hlean]].
    + rewrite Hlean in *.
      apply prefix_nil_inv in HP.
      apply map_eq_nil in HP.
      assert (A : (k, v) ∉ l).
      { eapply filter_nil_not_elem_of; eauto.
        simpl. auto. }
      done.
    + rewrite Hlean in *.
      simpl in *. rewrite reverse_singleton in HP.
      eapply filter_key_prefix in HP; eauto.
      rewrite Hlean0. f_equal.
      by eapply filter_key_singleton.
  - induction l as [|[k v] l Ih]; constructor.
    + specialize HP with k. rewrite filter_cons_True in HP by auto.
      rewrite map_cons in HP. simpl in HP. destructLean k.
      destruct Hlean as [Hlean | [v' Hlean]]; rewrite Hlean in *.
      { rewrite reverse_nil in HP.
        by apply prefix_nil_inv in HP. }
      { rewrite reverse_singleton in HP.
        apply prefix_cons_inv in HP as [? HP].
        subst v'. apply prefix_nil_inv in HP.
        apply map_eq_nil in HP.
        by eapply filter_nil_not_elem_of. }
    + apply Ih. intros k'. specialize HP with k'.
      destruct (decide (k' = k)).
      { subst. rewrite filter_cons_True in HP by auto.
        destructLean k.
        destruct Hlean as [Hlean | [v' Hlean]]; rewrite Hlean in *.
        - rewrite reverse_nil in *.
          by apply prefix_nil_inv in HP.
        - rewrite reverse_singleton in *.
          simpl in *.
          apply prefix_cons_inv_2 in HP.
          apply prefix_nil_inv in HP.
          rewrite HP. apply prefix_nil. }
      { by rewrite filter_cons_False in HP. }
Qed.

Lemma map_elim_filter_key :
  ∀ l k v,
  map snd (filter_key k l) = [v] ->
  filter_key k l = [(k, v)].
Proof.
  induction l as [|[k v] l Ih]; try done.
  intros k' v' H1.
  rewrite filter_cons in H1. case_decide.
  + subst k'. rewrite map_cons in H1.
    simpl in *. injection H1. intros.
    subst. apply map_eq_nil in H.
    filter. by rewrite H.
  + filter. by apply Ih.
Qed.

Lemma complete_to_lean l m lm :
  lean m lm ->
  (∀ k : K, complete k m l) ->
  complete_lean lm l.
Proof.
  unfold complete. intros Hlean Hcomplete. split.
  - intros k v. destructLean k.
    specialize Hcomplete with k.
    split; intros H3;
      destruct Hlean as [Hlean | [v' Hlean]]; rewrite Hlean in *;
      try rewrite reverse_nil in Hcomplete;
      try rewrite reverse_singleton in Hcomplete.
      apply map_eq_nil in Hcomplete.
      assert (A : (k, v) ∉ l).
      { eapply filter_nil_not_elem_of; eauto.
        simpl. auto. }
      done.
    + rewrite Hlean0. simpl. f_equal.
      by eapply filter_key_singleton.
    + by rewrite Hlean0 in H3.
    + rewrite Hlean0 in H3.
      injection H3. intros. subst.
      apply map_elim_filter_key in Hcomplete.
      assert (A : (k, v) ∈ filter_key k l).
      { rewrite Hcomplete. by list. }
      apply list_elem_of_filter in A. by unpack.
  - generalize dependent m.
    generalize dependent lm.
    induction l as [|[k v] l Ih]; constructor.
    + specialize Hcomplete with k.
      destructLean k.
      destruct Hlean as [Hlean | [v' Hlean]];
        rewrite filter_cons_True in Hcomplete by auto;
        rewrite map_cons in Hcomplete; simpl in *;
        rewrite Hlean in Hcomplete.
      { by rewrite reverse_nil in Hcomplete. }
      { rewrite reverse_singleton in Hcomplete.
        injection Hcomplete. intros H.
        apply map_eq_nil in H. intros.
        by eapply filter_nil_not_elem_of. }
    + apply Ih with
        (m:=delete k m) (lm := delete k lm).
      { intros k'. destruct (decide (k' = k)).
        - subst. rewrite lookup_total_delete_eq.
          pack; auto.
          by rewrite lookup_delete_eq with (i:=k) (m:=lm).
        - rewrite lookup_total_delete_ne by auto.
          rewrite lookup_delete_ne with (i:=k) (m:=lm) by auto.
          by destructLean k'. }
      intros k'. specialize Hcomplete with k'.
      destruct (decide (k' = k)).
      { subst. destructLean k. destruct Hlean as [Hlean | [v' Hlean]].
        - rewrite Hlean in *.
          rewrite reverse_nil in *.
          rewrite filter_cons_True in * by auto.
          by simpl in *.
        - rewrite filter_cons_True in Hcomplete by auto.
          simpl in *. rewrite Hlean in *.
          rewrite reverse_singleton in *.
          injection Hcomplete. intros. subst.
          rewrite H. by rewrite lookup_total_delete_eq. }
      { rewrite filter_cons_False in * by auto.
        by rewrite lookup_total_delete_ne. }
Qed.

Lemma wp_iter_rev_lean :
  forall {S} h f lm,
  isLeanHashtbl h lm ->
  ITER_LMAP lm
    (λ k v (s : S) Q, wp (f k v s) Q)
    (λ s Q, wp (iter_rev h s f) Q).
Proof.
  intros. ITER.
  destructIsLeanHashtbl.
  wp_op wp_iter_rev with invariant:inv.
  + intros. wp_op Hbody; auto. by eapply permitted_to_lean.
  + simpl. intros. unpack.
    eexists. pack; eauto.
    by eapply complete_to_lean.
Qed.

End H.
