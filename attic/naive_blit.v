Section Code.
Open Scope uint63.

(* We begin with a naive definition, using [iter_up] so as to save
   the trouble of writing a loop. *)

(* We compute [_delta] outside of the loop so as to save one addition
   inside the loop. This is a bit subtle, as the difference [_j - _i]
   might be negative, yet we compute it as an unsigned integer. This
   yields the correct result in the end anyway. *)

Definition naive_blit a _i b _j _n :=
  do _delta ← _j - _i ;
  iter_up _i (_i + _n) b @@ λ _k b,
  do x ← get a _k ;
  do b ← set b (_k + _delta) x ;
  b.

End Code.

(* [naive_blit] is correct. *)

Lemma wp_naive_blit :
  ∀Int _n n,
  blit_spec (λ a _i b _j, naive_blit a _i b _j _n) n.
Proof.
  unfold blit_spec, naive_blit. intros. arrays.
  wp_bind_eq.
  wp_op wp_iter_up with invariant: (λ k, blit_post xs i ys j (k - i));
  last wp_shadow b.
  (* Initialization. *)
  { isArray. }
  (* Preservation. *)
  { clear dependent b. wp_iter_up_body _k k b.
    wp_get x. subst x.
    (* The use of unsigned arithmetic in the computation of [_delta]
       does not cause any problem. Once upon a time, this proof used
       natural numbers as the logical model of machine integers; then
       we had to explicitly say [rewrite int.add_sub_exch] in order to
       pretend that we never created a negative number. Now this trick
       is unnecessary. *)
    wp_set. wp_ret. isArray. }
  (* Completion. *)
  { isArray. }
Qed.
