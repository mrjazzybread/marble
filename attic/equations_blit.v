(* -------------------------------------------------------------------------- *)

(* From array.v: *)

(* In order to allow a fair comparison, let's define a third naive [blit],
   this time using Equations, but without a higher-order function. *)

(* A micro-benchmark (benchmark.v) suggests that, when running inside Rocq
   using [vm_compute], [equations_blit] can be 75 times slower than
   [simple_blit]. *)

Section Code.
Open Scope uint63.

Equations equations_blit a _i b _j _n : array A
by wf _n ilt :=
equations_blit a _i b _j _n :=
  IF _n =? 0 THEN
    b
  ELSE
    do x ← get a _i ;
    do b ← set b _j x ;
    equations_blit a (_i + 1) b (_j + 1) (_n - 1).

End Code.

(* [equations_blit] is correct. *)

Lemma wp_equations_blit :
  ∀Int _n n,
  blit_spec (λ a _i b _j, equations_blit a _i b _j _n) n.
Proof.
  by well-founded induction on _n along ilt.
  unfold blit_spec. intros. arrays.
  autorewrite with equations_blit.
  wp_if.
  (* Base case. *)
  { wp_ret. isArray. }
  (* Step case. *)
  { wp_get x.
    wp_set.
    wp_op IH shadowing: b.
    isArray. }
Qed.

(* -------------------------------------------------------------------------- *)

(* From benchmark.v: *)

(* The times in comments use OCaml 4.14.2+flambda. *)

Time Definition a : array int :=
  Eval vm_compute in
  init n data.
    (* 0.05 seconds : 1 million elements/second *)

Time Definition b : array int :=
  Eval vm_compute in
  init n data.
    (* same as [a] *)

Time Definition time_equations_blit :=
  Eval vm_compute in
  (equations_blit a 0 b 0 n)%uint63.
    (* 4.7 seconds : 10,500 elements/second *)
