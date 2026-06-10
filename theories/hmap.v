From stdpp Require Import numbers list gmap.
From marble Require bucket.
From listz Require Import listz.
From marble Require Import tactics.
Notation len := length.
(* This file contains auxiliary lemmas to reason over the model of
   hash tables, that is, finite maps of keys to lists of values. *)
Section Hmap.

Context {K V : Type}.

(* We need to know that the type of [K] is countably infinite in order
   to use the theory of finite maps from [stdpp]. *)
Existing Instance bucket.dec_eq.
Declare Instance count_K : Countable K.

(* [gmap] is an implementation of finite maps using binary trees.  *)
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

Definition add (m : hmap) (k : K) (v : V) := <[k:= v :: m !!! k]> m.

Lemma add_lookup_eq :
  forall m k v, add m k v !!! k = v :: m !!! k.
Proof.
  intros.
  unfold add.
  by hmap.
Qed.

Lemma add_lookup_neq :
  forall m k k' v,
    k ≠ k' →
    add m k v !!! k' = m !!! k'.
Proof.
  intros.
  unfold add.
  by hmap.
Qed.

Definition rm (m : hmap) (k : K) :=
  <[k:=tl (m !!! k)]> m.

Definition rm_add (m : hmap) (k : K) (v : V) :=
  add (rm m k) k v.

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
    cardinality (add m k v) = (n + 1)%Z.
Proof.
  intros.
  unfold add.
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

End Hmap.
