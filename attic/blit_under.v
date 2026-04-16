(* [static_blit_under] handles all sizes [_n] comprised in the semi-open
   interval [lo, lo+delta). The parameters [lo] and [delta] have type
   [nat]; they exist at compile time only. *)

(* This logic is largely independent of [static_blit] and could be
   generalized. *)

Section BU.
Local Opaque Nat.div. (* This prevents unfolding and helps [lia]. *)

Equations static_blit_under a _i b _j _n (lo delta : nat) : array A
by wf delta lt :=
static_blit_under a _i b _j _n lo delta :=
  IF (delta <=? 1)%nat THEN
    static_blit a _i b _j lo 0
  ELSE
    let half := (delta / 2)%nat in
    let midpoint := (lo + half)%nat in
    if (_n <? of_nat midpoint)%uint63 then
      static_blit_under a _i b _j _n lo half
    else
      static_blit_under a _i b _j _n midpoint (delta - half).

End BU.

(* [static_blit_under] is correct. *)

Lemma wp_static_blit_under delta :
  ∀ lo,
  ∀IntU _n n,
  (lo ≤ Z.to_nat n < lo + delta)%nat →
  unsigned (Z.of_nat (lo + delta)) →
  blit_spec (λ a _i b _j, static_blit_under a _i b _j _n lo delta) n.
Proof.
  by well-founded induction on delta along lt.
  unfold blit_spec. intros.
  autorewrite with static_blit_under.
  destruct (delta <=? 1)%nat eqn:Heq.
  (* Case [delta ≤ 1]. In fact, [delta] cannot be zero, as [n] lies
     within the semi-open interval of [lo] to [lo + delta]. So, we
     must in fact have [delta = 1]. *)
  { wp_op wp_static_blit shadowing: b.
    isArray. }
  (* Case [1 < delta]. *)
  { wp_if; eapply IH; tc. }
Qed.

(* We can now specialize [static_blit_under] for the size [N]. *)

(* This scheme generates code of quadratic size, because each size [k] up
   to the limit [N] requires a code fragment of size [k]. If we could use
   Duff's device then we could generate code of linear size. That would
   require the ability to programmatically generate named (toplevel)
   functions and function calls. *)

Transparent static_blit_under.
Definition blit_underN a _i b _j _n :=
  Eval compute -[bind] in static_blit_under a _i b _j _n 0 N.

(* Disable Notation "t .[ i ]" := (get t i). *)
(* Disable Notation "t .[ i <- a ]" := (set t i a). *)
(* Print blit_underN. *)

(* [blit_underN] is correct. It handles all sizes less than [N]. *)

Lemma wp_blit_underN :
  ∀Int _n n,
  (0 ≤ n < NZ)%Z →
  blit_spec (λ a _i b _j, blit_underN a _i b _j _n) n.
Proof.
  unfold NZ.
  intros.
  unfold blit_spec. intros.
  change (blit_underN a _i b _j _n)
    with (static_blit_under a _i b _j _n 0 N).
  unfold N.
  eapply wp_static_blit_under; tc.
Qed.
