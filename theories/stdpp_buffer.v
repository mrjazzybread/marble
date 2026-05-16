From stdpp Require Import list.

Lemma NoDup_snoc {A} (history : list A) (x : A) :
  NoDup (history ++ [x]) ↔
  NoDup history ∧ x ∉ history.
Proof.
  rewrite NoDup_app. split.
  + intros (? & Hhistory & _).
    specialize (Hhistory x).
    rewrite list_elem_of_singleton in Hhistory.
    tauto.
  + intros (? & ?).
    assert (NoDup [x]) by apply NoDup_singleton.
    repeat split; eauto.
    intros y Hy.
    rewrite list_elem_of_singleton. congruence.
Qed.
