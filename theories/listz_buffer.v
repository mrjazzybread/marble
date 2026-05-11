From stdpp Require Import base sets propset.
From listz Require Import list_init.

Module init.

Lemma list_to_set_init_segment {A} n (f : nat → A) : ∀ i,
  list_to_set (init_segment i n f) ≡
  {[ a | ∃ j, a = f j ∧ i ≤ j < i + n ]}.
Proof.
  induction n as [| n]; simpl; intros.
  { intro a. rewrite elem_of_empty, elem_of_PropSet. split.
    + tauto.
    + intros (j & _ & ?). lia. }
  { rewrite IHn.
    intro a. rewrite elem_of_union, elem_of_singleton, !elem_of_PropSet.
    split.
    + intros [| (j & ? & ?) ]; eauto with lia.
    + intros (j & ? & ?).
      destruct (decide (j = i)).
      - subst j. left. eauto.
      - right. eauto with lia. }
Qed.

Lemma list_to_set_init {A} n (f : nat → A) :
  list_to_set (init n f) ≡
  {[ a | ∃ i, a = f i ∧ i < n ]}.
Proof.
  unfold init. rewrite list_to_set_init_segment.
  intro a. rewrite !elem_of_PropSet.
  split; intros (j & ? & ?); eauto with lia.
Qed.

End init.

From listz Require Import listz.

Lemma list_to_set_init {A} n (f : Z → A) :
  list_to_set (init n f) ≡
  {[ a | ∃ i, a = f i ∧ 0 ≤ i < n ]}.
Proof.
  unfold init. case_decide.
  { simpl. intro a. rewrite !elem_of_PropSet, elem_of_empty.
    split; [ tauto | intros (i & _ & ?) ]. lia. }
  { rewrite init.list_to_set_init. (* TODO rename *)
    intro a. rewrite !elem_of_PropSet.
    split; intros (i & ? & ?).
    + eauto with lia.
    + exists (Z.to_nat i). rewrite Z2Nat.id by lia. eauto with lia. }
Qed.
