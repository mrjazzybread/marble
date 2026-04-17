(* We use a formulation as a tail-recursive function where the parameter
   [_n] decreases. This lets us use well-founded recursion over [_n]. *)

(* We use structural induction over a proof of accessibility, as
   described by Xavier Leroy:
   https://xavierleroy.org/publi/wf-recursion.pdf *)

(* In the second branch, [Hnz] is a proof that [_n] is nonzero. We use
   it to build a proof that [_n - 1] is less than [_n]. This proof is
   used to argue that the recursive call is permitted. *)

Section Code.
Open Scope uint63.

Fixpoint simple_blit_aux a _i b _j _n (ACC : Acc ilt _n) :=
  IFC _n =? 0 THEN
    λ _, b
  ELSE
    λ (Hnz : (_n =? 0) = false),
    do x ← get a _i ;
    do b ← set b _j x ;
    simple_blit_aux a (_i + 1) b (_j + 1) (_n - 1)
                    (Acc_inv ACC (ilt_n_minus_1 _n Hnz)).

Definition simple_blit a _i b _j _n :=
  simple_blit_aux a _i b _j _n ltac:(tc).

(* A technical lemma: regardless of which proof [ACC] is used,
   [simple_blit_aux a _i b _j _n ACC] always returns the same
   result, which can be expressed in terms of [simple_blit]. *)

(* This is a proof irrelevance result. *)

(* As an immediate consequence of this lemma, [simple_blit]
   satisfies the desired fixed point equation. *)

Lemma simple_blit_aux_eq _n ACC :
  ∀ a _i b _j,
  simple_blit_aux a _i b _j _n ACC =
  if _n =? 0 then
    b
  else
    do x ← get a _i ;
    do b ← set b _j x ;
    simple_blit a (_i + 1) b (_j + 1) (_n - 1).
Proof.
  (* Following Leroy's paper, page 2, top right,
     we COULD begin the proof like this: *)
    (* by well-founded induction on _n along ilt. *)
    (* intros; destruct ACC; simpl. *)

  (* However, such a start is slightly unsatisfactory, insofar as it
     relies on the fact that the relation [ilt] is well-founded. Yet
     we should not need to use this fact: [ACC] is a witness of
     accessibility of [_n], so it should suffice to do (dependent)
     induction on [ACC]. Here is how (see equations.v): *)
  by dependent induction on _n ACC.
  intros. simpl.

  (* Then Xavier's method falls short! [destruct] does not work. *)
    (* Fail destruct (_n =? 0). *)
  (* The reason why [destruct] works in Xavier's setting is that he
     uses a non-dependent [match] construct to analyse the result of
     the test [Nat.eq_dec b 0], whose type is [{b = 0} + {b <> 0}];
     whereas we use a dependent [if] construct to analyze the result
     of the test [n =? 0], whose type is [bool]. *)

  (* Our work-around is to apply the lemma [IFC_if]. *)
  eapply IFC_if; [ eauto | intro ].

  (* There remains to prove the equality of the second branches.
     Fortunately, the induction hypothesis [IH] is exactly what
     is needed for this purpose. [setoid_rewrite] is used to
     rewrite in the continuation of [bind]. *)
  setoid_rewrite IH; [| tc2 | tc2 ].
  (* The goal is now trivial. *)
  reflexivity.
Qed.

End Code.

(* [simple_blit] is correct. *)

Lemma wp_simple_blit :
  ∀Int _n n,
  blit_spec (λ a _i b _j, simple_blit a _i b _j _n) n.
Proof.
  by well-founded induction on _n along ilt.
  unfold blit_spec, simple_blit. intros. arrays.
  rewrite simple_blit_aux_eq.
  wp_if.
  (* Base case. *)
  { wp_ret. isArray. }
  (* Step case. *)
  { wp_get x.
    wp_set.
    wp_op IH shadowing: b.
    isArray. }
Qed.
