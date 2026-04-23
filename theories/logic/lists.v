(* This file offers a few lemmas about lists. *)

(* These lemmas could move into stdpp or into listz. (TODO) *)

From Stdlib Require Import Utf8.
From stdpp Require Import list.
From listz Require Import listz.

(* -------------------------------------------------------------------------- *)

(* Lemmas about [singleton]. *)

Lemma rev_singleton {A} (x : A) :
  rev {[x]} = {[x]}.
Proof. reflexivity. Qed.

Lemma singleton_inj {A} (x y : A) :
  {[x]} = ({[y]} : list A) →
  x = y.
Proof. unfold singleton, stdpp_buffer.singleton_list. congruence. Qed.

Instance Inj_singleton {A} : Inj eq eq (singleton : A → list A).
Proof. intros x y. eauto using singleton_inj. Qed.

Lemma singleton_ne_nil {A} (x : A) : {[x]} ≠ [].
Proof. unfold singleton, stdpp_buffer.singleton_list. congruence. Qed.

(* -------------------------------------------------------------------------- *)

(* A variant of the lemma [app_eq_inv], where the two disjuncts are
   mutually exclusive. *)

Lemma app_eq_inv' {A} (l1 l2 k1 k2 : list A) :
  l1 ++ l2 = k1 ++ k2 →
  (∃ k : list A, l1 = k1 ++ k ∧ k2 = k ++ l2) ∨
  (∃ k : list A, k1 = l1 ++ k ∧ l2 = k ++ k2 ∧ k ≠ []).
Proof.
  intro Heq.
  apply app_eq_inv in Heq.
  destruct Heq as [ | (k & ? & ?) ].
  { eauto. }
  { assert (k = [] ∨ k ≠ []) as [|] by (destruct k; eauto).
    + subst k. rewrite ?app_nil_l, ?app_nil_r in *. subst.
      left. exists []. rewrite app_nil_l, app_nil_r. eauto.
    + eauto. }
Qed.

Lemma app_eq_inv'_ge {A} (l1 l2 k1 k2 : list A) :
  l1 ++ l2 = k1 ++ k2 →
  length k1 ≤ length l1 →
  (∃ k : list A, l1 = k1 ++ k ∧ k2 = k ++ l2).
Proof.
  intros Heq ?.
  apply app_eq_inv' in Heq.
  destruct Heq as [ | (k & ? & ? & ?) ].
  { eauto. }
  { exfalso. lengths. length in *. lia. }
Qed.

Lemma app_eq_inv'_le {A} (l1 l2 k1 k2 : list A) :
  l1 ++ l2 = k1 ++ k2 →
  length l1 ≤ length k1 →
  (∃ k : list A, k1 = l1 ++ k ∧ l2 = k ++ k2).
Proof.
  eauto using app_eq_inv'_ge.
Qed.

(* -------------------------------------------------------------------------- *)

(* If [rev xs] is empty then [xs] is empty. *)

Lemma rev_nil_inv {A} (xs : list A) :
  rev xs = [] → xs = [].
Proof.
  destruct xs; simpl.
  + eauto.
  + intros (?&?)%app_nil. congruence.
Qed.

Lemma rev_not_nil {A} (xs : list A) :
  xs ≠ nil → rev xs ≠ nil.
Proof.
  generalize (rev_nil_inv xs). tauto.
Qed.
