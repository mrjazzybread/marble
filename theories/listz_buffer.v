(* This file contains stuff that should move into listz. *)

From stdpp Require Import numbers.
From listz Require Import list_init.

Section Forall2.

Context {A B : Type}.
Variable P : A → B → Prop.

Lemma Forall2_init_segment (f : nat → A) (g : nat → B) :
  ∀ n k,
  (∀ i, i < n → P (f (k + i)) (g (k + i))) →
  Forall2 P (init_segment k n f) (init_segment k n g).
Proof.
  induction n as [|n]; simpl init_segment; intros k HP.
  { econstructor. }
  { econstructor.
    + replace k with (k + 0) by lia.
      eapply HP. lia.
    + eapply IHn. intros i ?.
      replace (S k + i) with (k + (i + 1)) by lia.
      eapply HP. lia. }
Qed.

(* TODO rename *)
Lemma Forall2_init_nat n (f : nat → A) (g : nat → B) :
  (∀ i, i < n → P (f i) (g i)) →
  Forall2 P (init n f) (init n g).
Proof.
  intros. unfold init. eauto using Forall2_init_segment.
Qed.

End Forall2.

From stdpp Require Import list_numbers.
From listz Require Import listz.

Lemma sum_list_with_singleton {A} (f : A → nat) (x : A) :
  sum_list_with f {[x]} = f x.
Proof.
  unfold singleton, stdpp_buffer.singleton_list. simpl. lia.
Qed.

Hint Rewrite
  @sum_list_with_singleton
  @sum_list_with_app
: ulist clist.

Lemma sum_list_with_insert `{Inhabited A} (f : A → nat) i xs x :
  valid i xs →
  (
    sum_list_with f (<[i:=x]>xs) + f (xs !!! i) =
    sum_list_with f xs + f x
  )%nat.
Proof.
  intros.
  rewrite (seg_intro xs) at 1.
  rewrite insert_seg by (length; lia).
  assert (Hxs: xs = initial_seg i xs ++ {[xs !!! i]} ++ final_seg (i+1) xs).
  { rewrite singleton_is_seg by assumption. join_segments. lego. }
  rewrite Hxs at 5.
  list.
  lia.
Qed.

Lemma Forall2_init {A B} (P : A → B → Prop) n (f : Z → A) (g : Z → B) :
  (∀ i, 0 ≤ i < n → P (f i) (g i)) →
  Forall2 P (init n f) (init n g).
Proof.
  intros HP. unfold init.
  case_decide; [ eauto |].
  eapply Forall2_init_nat.
  intros i ?. eapply HP. lia.
Qed.

Lemma Forall2_replicate {A B} (P : A → B → Prop) n (x : A) (y : B) :
  P x y →
  Forall2 P (replicate n x) (replicate n y).
Proof.
  eauto using Forall2_init.
Qed.

Lemma Forall2_insert {A B} (P : A → B → Prop) (xs : list A) (ys : list B)
  x y i :
  Forall2 P xs ys →
  P x y →
  Forall2 P (<[i:=x]> xs) (<[i:=y]> ys).
Proof.
  intros. unfold insert, listz_insert.
  case_decide; eauto using Forall2_insert.
Qed.
