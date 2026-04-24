(* This file contains stuff that should move into listz. *)

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
