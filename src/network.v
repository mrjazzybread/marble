From stdpp Require Import numbers list.
Notation len := List.length.
From Stdlib Require Import Uint63.
From Stdlib Require Import Array.PArray.
From marble Require Import equations.
From marble Require Import tactics list_extra list_tactics.
From marble Require Import iteration bool int wp wp_tactics array.
From marble Require Import orders sorting compare sort.
Open Scope nat_scope.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

Implicit Types x y : nat.

Infix "≤?" := Nat.leb (at level 70, no associativity).

Infix "≃" := Permutation
  (at level 70, no associativity).

Fixpoint cont n A :=
  match n with 0 => A | S n => nat → cont n A end.

Fixpoint tuple n A :=
  match n with 0 => unit | S n => (A * tuple n A)%type end.

Instance isBool_nat_leb x y :
  isBool (x ≤? y) (x ≤ y) (y < x).
Proof.
  unfold isBool. destruct (x ≤? y) eqn:Heq; lia.
Qed.

(* Fixpoint aside {A n} x : cont (S n) A → cont n A := *)
(*   match n return cont (S n) A → cont n A with *)
(*   | 0   => λ k, k x *)
(*   | S n => λ k y, aside x (k y) *)
(*   end. *)

Notation emit k x continue :=
  (continue (k x))
  (only parsing).

Lemma lt_le x y : x < y → x ≤ y.
Proof. lia. Qed.
Hint Resolve lt_le : sort.
Hint Resolve Permutation_app_comm : sort.

Definition merge10 {A} x0 (k : cont 1 A) : A :=
  k x0.

Definition merge11 {A} x0 y0 (k : cont 2 A) : A :=
  if x0 ≤? y0 then
    k x0 y0
  else
    k y0 x0.

Lemma wp_merge11 {A} x0 y0 k (Q : A → Prop) :
  (∀ z0 z1,
     z0 ≤ z1 →
     [x0] ++ [y0] ≃ [z0; z1] →
     wp (k z0 z1) Q
  ) →
  wp (merge11 x0 y0 k) Q.
Proof.
  intros Hret. unfold merge11.
  wp_if; eapply Hret; eauto with sort.
Qed.

Definition merge12 {A} x0 y0 y1 (k : cont 3 A) : A :=
  if x0 ≤? y0 then
    k x0 y0 y1
  else
    emit k y0 (merge11 x0 y1).

Lemma exploit_pairwise x y ys :
  pairwise le [x] ys →
  y ∈ ys →
  x ≤ y.
Proof. Admitted.

Lemma swap_pairwise x xs ys :
  pairwise le [x] xs →
  xs ≃ ys →
  pairwise le [x] ys.
Proof. Admitted.

Lemma exploit_swap_pairwise x y xs ys :
  xs ≃ ys →
  pairwise le [x] xs →
  y ∈ ys →
  x ≤ y.
Proof. eauto using exploit_pairwise, swap_pairwise. Qed.

Lemma pairwise_nil x :
  pairwise le [x] [].
Proof.
  unfold pairwise. intros. rewrite elem_of_nil in *. tauto.
Qed.

Lemma pairwise_cons x y ys :
  x ≤ y →
  pairwise le [x] ys →
  pairwise le [x] (y :: ys).
Proof.
  replace [x] with ({[x]} : list nat) by eauto.
  rewrite <- !sorting.Forall_R_iff.
  intros. constructor; eauto.
Qed.

Hint Resolve exploit_swap_pairwise : sort.

Hint Resolve pairwise_nil pairwise_cons : sort.

Hint Resolve list_elem_of_here list_elem_of_further : sort.

Hint Extern 1 (_ ≃ _) =>
  match goal with h: _ ≃ _ |- _ => rewrite <- h end; econstructor
: sort.

Hint Resolve Nat.le_trans : sort.

Lemma wp_merge12 {A} x0 y0 y1 k (Q : A → Prop) :
  y0 ≤ y1 →
  (∀ z0 z1 z2,
     z0 ≤ z1 → z1 ≤ z2 →
     [x0] ++ [y0; y1] ≃ [z0; z1; z2] →
     wp (k z0 z1 z2) Q
  ) →
  wp (merge12 x0 y0 y1 k) Q.
Proof.
  intros ? Hret. unfold merge12.
  wp_if.
  + eapply Hret; eauto.
  + eapply wp_merge11. intros z0 z1 ? Hpermut. simpl in Hpermut.
    eapply Hret; eauto with sort.
Qed.

Definition merge13 {A} x0 y0 y1 y2 (k : cont 4 A) : A :=
  if x0 ≤? y0 then
    k x0 y0 y1 y2
  else
    emit k y0 (merge12 x0 y1 y2).

Lemma wp_merge13 {A} x0 y0 y1 y2 k (Q : A → Prop) :
  y0 ≤ y1 → y1 ≤ y2 →
  (∀ z0 z1 z2 z3,
     z0 ≤ z1 → z1 ≤ z2 → z2 ≤ z3 →
     [x0] ++ [y0; y1; y2] ≃ [z0; z1; z2; z3] →
     wp (k z0 z1 z2 z3) Q
  ) →
  wp (merge13 x0 y0 y1 y2 k) Q.
Proof.
  intros ? ? Hret. unfold merge13.
  wp_if.
  + eapply Hret; eauto.
  + eapply wp_merge12; eauto. intros z0 z1 z2 ?? Hpermut. simpl in Hpermut.
    eapply Hret; eauto 2 with sort.
    - eapply exploit_swap_pairwise; eauto 6 with sort.
Qed.

Definition merge21 {A} x0 x1 y0 k : A :=
  if x0 ≤? y0 then
    emit k x0 (merge11 x1 y0)
  else
    k y0 x0 x1.

Lemma wp_merge21 {A} x0 x1 y0 k (Q : A → Prop) :
  x0 ≤ x1 →
  (∀ z0 z1 z2,
     z0 ≤ z1 → z1 ≤ z2 →
     [x0; x1] ++ [y0] ≃ [z0; z1; z2] →
     wp (k z0 z1 z2) Q
  ) →
  wp (merge21 x0 x1 y0 k) Q.
Proof.
  intros ? Hret. unfold merge21.
  wp_if.
  + eapply wp_merge11. intros z0 z1 ? Hpermut. simpl in Hpermut.
    eapply Hret; eauto with sort.
  + eapply Hret; eauto with sort.
Qed.

Definition merge31 {A} x0 x1 x2 y0 k : A :=
  if x0 ≤? y0 then
    emit k x0 (merge21 x1 x2 y0)
  else
    k y0 x0 x1 x2.

Definition merge22 {A} x0 x1 y0 y1 k : A :=
  if x0 ≤? y0 then
    emit k x0 (merge12 x1 y0 y1)
  else
    emit k y0 (merge21 x0 x1 y1).

Lemma wp_merge22 {A} x0 x1 y0 y1 k (Q : A → Prop) :
  x0 ≤ x1 → y0 ≤ y1 →
  (∀ z0 z1 z2 z3,
     z0 ≤ z1 → z1 ≤ z2 → z2 ≤ z3 →
     [x0; x1] ++ [y0; y1] ≃ [z0; z1; z2; z3] →
     wp (k z0 z1 z2 z3) Q
  ) →
  wp (merge22 x0 x1 y0 y1 k) Q.
Proof.
  intros ?? Hret. unfold merge22.
  wp_if.
  + eapply wp_merge12; eauto 2.
    intros z0 z1 z2 ?? Hpermut. simpl in Hpermut.
    eapply Hret; eauto 2 with sort.
    - eapply exploit_swap_pairwise; eauto 2 with sort.
      eapply pairwise_cons; eauto with sort.
  + eapply wp_merge21; eauto 2.
    intros z0 z1 z2 ?? Hpermut.
    eapply Hret; eauto 2 with sort.
    - eapply exploit_swap_pairwise; eauto 2 with sort.
      eapply pairwise_cons; eauto with sort.
    - rewrite <- Hpermut. simpl.
      (* Wow. *)
      eapply perm_trans; [ | eapply perm_swap ].
      eapply perm_skip.
      eapply perm_trans; [ | eapply perm_swap ].
      eapply perm_skip.
      reflexivity.
Qed.

Definition merge23 {A} x0 x1 y0 y1 y2 k : A :=
  if x0 ≤? y0 then
    emit k x0 (merge13 x1 y0 y1 y2)
  else
    emit k y0 (merge22 x0 x1 y1 y2).

Definition merge32 {A} x0 x1 x2 y0 y1 k : A :=
  if x0 ≤? y0 then
    emit k x0 (merge22 x1 x2 y0 y1)
  else
    emit k y0 (merge31 x0 x1 x2 y1).

Definition merge33 {A} x0 x1 x2 y0 y1 y2 k : A :=
  if x0 ≤? y0 then
    emit k x0 (merge23 x1 x2 y0 y1 y2)
  else
    emit k y0 (merge32 x0 x1 x2 y1 y2).

Eval compute in merge33.

Definition sort2 {A} x0 x1 k : A :=
  merge11 x0 x1 k.

Definition wp_sort2 :=
  @wp_merge11.

Definition sort3 {A} x0 x1 x2 k : A :=
  sort2 x0 x1 @@ λ x0 x1,
  merge21 x0 x1 x2 k.

Lemma wp_sort3 {A} x0 x1 x2 k (Q : A → Prop) :
  (∀ z0 z1 z2,
     z0 ≤ z1 → z1 ≤ z2 →
     [x0; x1; x2] ≃ [z0; z1; z2] →
     wp (k z0 z1 z2) Q
  ) →
  wp (sort3 x0 x1 x2 k) Q.
Proof.
  intros Hret. unfold sort3.
  eapply wp_sort2.
  intros z0 z1 ? Hpermut1. simpl in Hpermut1.
  eapply wp_merge21; eauto 2.
  intros w0 w1 w2 ? ? Hpermut2.
  rewrite <- Hpermut1 in Hpermut2. simpl in Hpermut2.
  eapply Hret; eauto 2.
Qed.

Definition sort4 {A} x0 x1 x2 x3 k : A :=
  sort2 x0 x1 @@ λ x0 x1,
  sort2 x2 x3 @@ λ y0 y1,
  merge22 x0 x1 y0 y1 k.

Lemma wp_sort4 {A} x0 x1 x2 x3 k (Q : A → Prop) :
  (∀ z0 z1 z2 z3,
     z0 ≤ z1 → z1 ≤ z2 → z2 ≤ z3 →
     [x0; x1; x2; x3] ≃ [z0; z1; z2; z3] →
     wp (k z0 z1 z2 z3) Q
  ) →
  wp (sort4 x0 x1 x2 x3 k) Q.
Proof.
  intros Hret. unfold sort4.
  eapply wp_sort2.
  intros w0 w1 ? Hpermut1. simpl in Hpermut1.
  eapply wp_sort2; eauto 2.
  intros y0 y1 ? Hpermut2. simpl in Hpermut2.
  eapply wp_merge22; eauto 2.
  intros z0 z1 z2 z3 ??? Hpermut.
  rewrite <- Hpermut1, <- Hpermut2 in Hpermut.
  eapply Hret; eauto 2.
Qed.

Definition sort5 {A} x0 x1 x2 x3 x4 k : A :=
  sort3 x0 x1 x2 @@ λ x0 x1 x2,
  sort2 x3 x4 @@ λ y0 y1,
  merge32 x0 x1 x2 y0 y1 k.

Definition sort6 {A} x0 x1 x2 x3 x4 x5 k : A :=
  sort3 x0 x1 x2 @@ λ x0 x1 x2,
  sort3 x3 x4 x5 @@ λ y0 y1 y2,
  merge33 x0 x1 x2 y0 y1 y2 k.

Eval compute in sort6.

Definition sort4_tuple '(x0, x1, x2, x3) :=
  sort4 x0 x1 x2 x3 @@ λ x0 x1 x2 x3, (x0, x1, x2, x3).

Section S.
Open Scope uint63.

Definition sort2_segment a _i _k :=
  do x0 ← get a _i ;
  do x1 ← get a (_i + 1) ;
  sort2 x0 x1 @@ λ x0 x1,
  do a ← set a _k x0 ;
  do a ← set a (_k + 1) x1 ;
  a.

Definition sort3_segment a _i _k :=
  do x0 ← get a _i ;
  do x1 ← get a (_i + 1) ;
  do x2 ← get a (_i + 2) ;
  sort3 x0 x1 x2 @@ λ x0 x1 x2,
  do a ← set a _k x0 ;
  do a ← set a (_k + 1) x1 ;
  do a ← set a (_k + 2) x2 ;
  a.

Definition sort4_segment a _i _k :=
  do x0 ← get a _i ;
  do x1 ← get a (_i + 1) ;
  do x2 ← get a (_i + 2) ;
  do x3 ← get a (_i + 3) ;
  sort4 x0 x1 x2 x3 @@ λ x0 x1 x2 x3,
  do a ← set a _k x0 ;
  do a ← set a (_k + 1) x1 ;
  do a ← set a (_k + 2) x2 ;
  do a ← set a (_k + 3) x3 ;
  a.

End S.

Definition sort2seg :=
  Eval compute -[bind Nat.leb] in sort2_segment.

Definition sort3seg :=
  Eval compute -[bind Nat.leb] in sort3_segment.

Definition sort4seg :=
  Eval compute -[bind Nat.leb] in sort4_segment.

(* Disable Notation "t .[ i ]" := (get t i). *)
(* Disable Notation "t .[ i <- a ]" := (set t i a). *)
(* Print sort2seg. *)
(* Print sort3seg. *)
(* Print sort4seg. *)

Definition wp_sort_seg_spec sort_seg n :=
  ∀ a xs _i i _k k,
  isArray a xs →
  isInt _i i →
  isInt _k k →
  valid_seg i (i + n) xs →
  valid_seg k (k + n) xs →
  (* Sorted R' (seg i (i + n) xs) → *) (* TODO stability *)
  wp (sort_seg a _i _k) (λ a, ∃ xs',
    isArray a xs' ∧
    len xs = len xs' ∧
    unmodified_outside_seg xs xs' k (k + n) ∧
    seg k (k + n) xs' ≃ seg i (i + n) xs ∧
    Sorted le (seg k (k + n) xs')
  ).

Lemma wp_sort2seg :
  wp_sort_seg_spec sort2seg 2.
Proof.
  unfold wp_sort_seg_spec. intros.
  change sort2seg with sort2_segment. unfold sort2_segment.
  wp_get x0.
  wp_get x1.
  eapply wp_sort2.
  intros. wp_last Hpermut.
  repeat wp_set.
  wp_ret.
  eexists. pack.
  + eauto.
  + list. eauto.
  + list. eauto.
  + list. rewrite <- Hpermut. eapply identity_permutation.
    listx_total o.
    assert (o = 0 ∨ o = 1) as [|] by lia;
    subst o; simpl; list; assumption.
  + list.
    repeat (eapply sorted_app_boundary; eauto using Sorted_singleton).
Qed.

Lemma wp_sort3seg :
  wp_sort_seg_spec sort3seg 3.
Proof.
  unfold wp_sort_seg_spec. intros.
  change sort3seg with sort3_segment. unfold sort3_segment.
  assert (isInt 2 2) by eauto using introIsInt. (* UGLY *)
  wp_get x0.
  wp_get x1.
  wp_get x2.
  eapply wp_sort3.
  intros. wp_last Hpermut.
  repeat wp_set.
  wp_ret.
  eexists. pack.
  + eauto.
  + list. eauto.
  + list. eauto.
  + list. rewrite <- Hpermut. eapply identity_permutation.
    listx_total o.
    assert (o = 0 ∨ o = 1 ∨ o = 2) as [|[|]] by lia;
    subst o; simpl; list; assumption.
  + list.
    repeat (eapply sorted_app_boundary; eauto using Sorted_singleton).
Qed.

Lemma wp_sort4seg :
  wp_sort_seg_spec sort4seg 4.
Proof.
  unfold wp_sort_seg_spec. intros.
  change sort4seg with sort4_segment. unfold sort4_segment.
  assert (isInt 2 2) by eauto using introIsInt. (* UGLY *)
  assert (isInt 3 3) by eauto using introIsInt. (* UGLY *)
  wp_get x0.
  wp_get x1.
  wp_get x2.
  wp_get x3.
  eapply wp_sort4.
  intros ???? ??? Hpermut.
  repeat wp_set.
  wp_ret.
  eexists. pack.
  + eauto.
  + list. eauto.
  + list. eauto.
  + list. rewrite <- Hpermut. eapply identity_permutation.
    listx_total o.
    assert (o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3) as [|[|[|]]] by lia;
    subst o; simpl; list; assumption.
  + list.
    repeat (eapply sorted_app_boundary; eauto using Sorted_singleton).
Qed.

(* TODO abandoned
Lemma wp_sort4seg a xs _i i _k k :
  let n := 4 in
  isArray a xs →
  isInt _i i →
  isInt _k k →
  valid_seg i (i + n) xs →
  valid_seg k (k + n) xs →
  (* Sorted R' (seg i (i + n) xs) → *)
  wp (sort4seg a _i _k) (λ a, ∃ xs',
    isArray a xs' ∧
    len xs = len xs' ∧
    unmodified_outside_seg xs xs' k (k + n) ∧
    seg k (k + n) xs' ≃ seg i (i + n) xs
    (* Sorted R (seg k (k + n) xs') *)
  ).
Proof.
  intros. unfold sort4seg. subst n.
  assert (isInt 2 2) by eauto using introIsInt. (* UGLY *)
  assert (isInt 3 3) by eauto using introIsInt. (* UGLY *)
  wp_get x0.
  wp_get x1.
  wp_get x2.
  wp_get x3.
  repeat wp_if. (* 4! = 24 subgoals *)
  do 4 wp_set;
  wp_ret;
  eexists;
  split; [ eauto |
  split; [ list; lia |
  split; [ intros; list; reflexivity |
  ]]].
  subst;
  repeat rewrite seg_insert by (list; lia); repeat (case_decide; try lia); nat.
Abort.

 *)
