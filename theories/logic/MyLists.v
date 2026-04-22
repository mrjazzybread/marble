Set Implicit Arguments.
From Stdlib Require Export List.

(* A fact about lists. *)
Lemma head_of_append:
  forall (A : Type) (y : A) xs ys zs,
  y :: xs = ys ++ zs ->
  ys <> nil ->
  exists ys',
  y :: ys' = ys /\ xs = ys' ++ zs.
Proof.
  do 5 intro. intros h ?. destruct ys; [ congruence | ].
  injection h; clear h; intros. subst. eauto.
Qed.

(* A fact about lists. *)
Lemma rev_not_nil:
  forall (A : Type) (xs : list A),
  xs <> nil ->
  rev xs <> nil.
Proof.
  intros. destruct xs; [ congruence | ].
  simpl.
  intro h. generalize (app_eq_nil _ _ h); intros [ ? ? ].
  congruence.
Qed.
