From stdpp Require Import numbers list gmap.
From listz Require Import listz.
Notation len := length.
From Stdlib Require Import Uint63.
From Stdlib Require Import Array.PArray.
From marble Require Import tactics bool int iteration loop wp logic array.

(* This file contains the theory of "buckets", unboxed association lists. *)

Hint Resolve not_elem_of_nil : marble.

Ltac eq_decide v1 v2 := destruct (decide (v1 = v2)).

Section Bucket.

(* Type of keys *)
Context {K : Type}.

(* Type of values. *)
Context {V : Type}.

Parameter _eq : K -> K -> bool.

Hint Rewrite
  (@not_elem_of_cons (K * V)) : clist.

(* The [_eq] function decides equality over keys. *)
Declare Instance is_bool_eq :
  ∀ k1 k2, isBool1 (_eq k1 k2) (k1 = k2).

(* Although we could use a simple association list, we use the
   following unboxed inductive data type for more efficient memory
   usage *)
Inductive bucket :=
  | Nil : bucket
  | Cons : K -> V -> bucket -> bucket.

(* Isomorphism between buckets and lists. *)
Fixpoint b2l b := match b with
 |Nil => []
 |Cons k v t => (k, v) :: b2l t
 end.

(* Proof that the [bucket] type is inhabited.  This is necessary for
   total lookups on finite maps. *)
Global Instance bucket_inh : Inhabited bucket :=
  populate Nil.

(* When reasoning over buckets, we use standard Rocq lists as opposed
   to creating a separate theory over buckets. *)
Definition assoc := list (K * V).

(* Decidable equality over [K].  We use the [_eq] function to show
   that equality is decidable. This instance is necessary for lookups
   on finite maps. *)
Instance dec_eq : EqDecision K.
Proof.
  intros x y.
  pose is_bool_eq as H.
  specialize H with x y.
  unfold Decision.
  unfold isBool1 in H.
  destruct _eq; auto.
Qed.

Notation filter_key k l :=
  (filter (fun (x : K * V) => eq x.1 k) l).

(* -------------------------------------------------------------------------- *)

(* Lemmas for filtering association lists *)

Lemma filter_key_nin :
  forall k b,
    (∀ v : V, (k, v) ∉ b) ->
    filter_key k b = [].
Proof.
  intros k b H1.
  induction b as [|[k' v] t Ih]; auto.
  rewrite filter_cons_False.
  + apply Ih. intros v'.
    specialize H1 with v'.
    list in H1. by unpack.
  + specialize H1 with v.
    list in H1. unpack.
    intros ?. by subst.
Qed.

Hint Rewrite
  @filter_nil
  @filter_cons_False
  @filter_cons_True
  using done : cfilter.

Ltac filter := autorewrite with cfilter.

Lemma filter_key_cons :
  forall k k' v b1 b2,
    filter_key k b1 = filter_key k b2 ->
    filter_key k ((k', v)::b1) = filter_key k ((k', v) :: b2).
Proof.
  intros. eq_decide k k'; subst; filter; auto.
  by f_equal.
Qed.

(* Association lists *)

(* [(b', r) = remove_assoc k b] returns a new bucket [b'] where the
first binding of key [k] is removed.  If there was no value associated
with key [k], [r] is [false] and [b'] = [b], otherwise it is
[true]. *)
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

(* [l' = remove_assoc_list k l] returns a list [l'] where the first
   binding of key [k] is removed.
   If no such binding exists then [l' = l]. *)
Fixpoint remove_assoc_list (k : K) (l : list (K * V)) :=
  match l with
  |[] => []
  |(k', v) :: t =>
     if (decide (k = k'))
     then t
     else
       (k', v) :: remove_assoc_list k t
  end.

(* If a binding is in the result of [remove_assoc_list], then it was
in the original association list *)

Lemma remove_assoc_in :
  forall l k k' v,
    (k', v) ∈ remove_assoc_list k l ->
    (k', v) ∈ l.
Proof.
  intros l k k' v H1.
  induction l as [|[k'' v'] t Ih]; simpl in H1.
  - auto with marble.
  - destruct decide; rewrite elem_of_cons; auto.
    apply elem_of_cons in H1 as [H1 | H1]; auto.
Qed.

(* The list of bindings for [k] in [remove_assoc_list l] is equal to
   [tl (filter_key k l)] *)

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

(* The list of bindings for [k'] in [remove_assoc_list k b] is equal
   to the list of bindings for [k'] in [l], provided that [k' ≠ k].*)

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

Lemma remove_assoc_wp k b:
  ∀ l, l = b2l b ->
  wp (remove_assoc k b)
    (λ r, let (r, b') := r in
          ∃ l', l' = b2l b' ∧
          isBool r (∃ v, (k, v) ∈ l) (∀ v, (k, v) ∉ l) ∧
          l' = remove_assoc_list k l).
Proof.
  induction b as [|k' v b Ih]; simpl; intros; subst l.
  - (* When the list is empty. *)
    wp_ret. simpl. eauto with marble.
  - (* When the list is non-empty. *)
    simpl. wp_bind_eq. wp_if.
    + (* If the current binding is equal to [k]. *)
      subst k'. wp_ret. simpl.
      pack; eauto.
      { try constructor. }
      { by rewrite decide_True. }
    + (* If the current binding is not equal to [k]*)
      wp_op Ih. intros [r b'] [l' ?].
      unpack. eexists. subst l'.
      pack; try by filter.
      { destruct r; simpl in *.
        - unpack. eexists. by constructor.
        - intros. list.
          split; auto. intros I. by injection I. }
      { rewrite decide_False by auto.
        simpl. by f_equal. }
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
  ∀ b', b' = (filter_key k (b2l b)) ->
  wp (find_assoc k b)
    (λ o, o = head (map snd b')).
Proof.
  intros. induction b as [|k' v t Ih].
  - wp_ret.
  - simpl. wp_if.
    + wp_ret. subst. simpl. by filter.
    + wp_op Ih; auto. subst. simpl. by filter.
Qed.

End Bucket.

Hint Rewrite
  @filter_nil
  @filter_cons_False
  @filter_cons_True
  using done : cfilter.

Ltac filter := autorewrite with cfilter.
