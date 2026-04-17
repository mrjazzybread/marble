From stdpp Require Import numbers well_founded.
From Stdlib Require Export ZifyNat.
  (* [ZifyNat] magically makes [lia] more powerful,
     including on goals that involve division in Z *)
From Stdlib Require Import Uint63 ZifyUint63.
  (* [ZifyUint63] magically makes [lia] more powerful *)
From Stdlib Require Import Wellfounded.Wellfounded.
Notation Succ := S. (* avoid name clash *)
From listz Require Import listz.
From marble Require Import tactics bool wp iteration int.
From marble Require Import equations.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

(* This file defines several higher-order functions that implement
   loops and interruptible loops over semi-open intervals of the
   unsigned primitive integers. *)

Open Scope Z_scope.
Implicit Types _i _j _k : int.
Implicit Types  i : Z.
Implicit Types  z : Z.

Local Ltac wp_intro_hook Hx ::=
  z in Hx; unpack in Hx.

(* -------------------------------------------------------------------------- *)

(* This tactic uses [lia] to resolve comparisons among machine integers. *)

(* We do not need it when we reason in Hoare style, because the reasoning
   rule [wp_if] and the type class [isBool] do the job then. We do need it
   when we perform equational reasoning. We use this style of reasoning
   to prove that an unrolled loop is equal to an ordinary loop. *)

Local Ltac resolve :=
  match goal with
  | |- context[(?lhs =? ?rhs)%uint63] =>
    first [
      replace (lhs =? rhs)%uint63 with true by lia
    | replace (lhs =? rhs)%uint63 with false by lia
    ]
  | |- context[(?lhs ≤? ?rhs)%uint63] =>
    first [
      replace (lhs ≤? rhs)%uint63 with true by lia
    | replace (lhs ≤? rhs)%uint63 with false by lia
    ]
  end.

(* -------------------------------------------------------------------------- *)

(* [N] is the unrolling factor that we use in our unrolled loops. *)

Definition N  : nat := 8.
Definition NZ : Z   := Eval compute in Z.of_nat N.
Definition Ni : int := Eval compute in Uint63.of_nat N.

Lemma ilt_n_minus_N {_n} :
  (_n <? Ni)%uint63 = false →
  ilt (_n - Ni)%uint63 _n.
Proof. unfold Ni. eauto with marble. Qed.
Local Hint Resolve ilt_n_minus_N : marble.

(* -------------------------------------------------------------------------- *)

(* A loop, counting down, using machine integers. *)

(* [iter_down _i _k s body] applies the loop body [body] to every machine
   integer from [_k], excluded, down to [_i], included. A state of type [S]
   is carried, whose initial value is [s]. *)

Section IterDown.
Context {S : Type}.
Implicit Types s : S.
Open Scope uint63.

(* We make [body] a section variable so that it is lambda-abstracted above
   [Fixpoint iter_down_aux]. In other words, it is not a parameter of the
   fixed point itself. This allows us to later easily specialize the code
   for a specific loop body, just by inlining. *)

Section Body.
Variable body : int → S → S.

(* We are careful to test the condition [_k =? _i] before decrementing [_k].
   Because our semi-open intervals are closed at the bottom end, we cannot
   first decrement and then test the condition [_k <? _i]. If [_i] is zero
   then this would underflow. *)

(* We define [iter_down_aux] by well-founded recursion over the index [_k].
   In the second branch, the fact that [_k =? _i] is false is needed in
   order to prove that [_k - 1] is less than [_k], a fact which itself is
   required by the termination argument. *)

(* It is worth noting that the termination argument does not need the
   hypothesis [φ _i ≤ φ _k]. Even in the absence of this hypothesis,
   termination is guaranteed, thanks to underflow. This said, later on, when
   we give a specification of [iter_down_aux], we assume [i ≤ k]. It would
   be unnatural and inconvenient to propose a specification that allows
   underflow to take place. *)

Fixpoint iter_down_aux _i _k s (ACC : Acc (rilt _i) _k) :=
  IFC _k =? _i THEN λ _,
    s
  ELSE λ Hki,
    let _k' := _k - 1 in
    do s ← body _k' s ;
    iter_down_aux _i _k' s (Acc_inv ACC (rilt_n_minus_1 _k _i Hki)).

End Body.

Definition iter_down _i _k s body :=
  if _k ≤? _i then s
  else iter_down_aux body _i _k s ltac:(tc).

(* A specification of [iter_down_aux]. *)

(* This specification requires [i ≤ k]: that is, the top index [k] must
   be greater than or equal to the bottom index [i]. This hypothesis is
   natural: it is required to guarantee that no underflow takes place. *)

Lemma wp_iter_down_aux (body : int → S → S) :
  ∀IntU _i i ,
  ∀IntU _k k ,
  i ≤ k →
  ∀ ACC,
  ITER_Z i k Down
    (λ j s Q, ∀ _j, isInt _j j → wp (body _j s) Q)
    (λ s Q, wp (iter_down_aux body _i _k s ACC) Q).
Proof.
  intros _i i ? ?.
  by well-founded induction on _k along (rilt _i).
  intros. ITER. expand_ITER in IH.
  intros; destruct ACC; simpl.
  wp_if; z.
  (* Case [k = i]. *)
  { wp_ret. }
  (* Case [k ≠ i]. *)
  { wp_op Hbody shadowing: s.
    wp_op IH shadowing: s.
    eauto. }
Qed.

(* A specification of [iter_down]. *)

Lemma wp_iter_down (body : int → S → S) :
  ∀IntU _i i ,
  ∀IntU _k k ,
  ITER_Z i k Down
    (λ j s Q, ∀ _j, isInt _j j → wp (body _j s) Q)
    (λ s Q, wp (iter_down _i _k s body) Q).
Proof.
  intros. ITER. unfold iter_down.
  wp_if; z.
  (* Case [k ≤ i]. *)
  { wp_ret. }
  (* Case [i < k]. *)
  { wp_op wp_iter_down_aux shadowing: s.
    eauto. }
Qed.

(* -------------------------------------------------------------------------- *)

(* A "static" variant of [iter_down], where the difference [k - i] is
   statically known and is represented by a natural number [n]. *)

Section Body.
Variable body : int → S → S.

Fixpoint static_iter_down_aux _k s (n : nat) :=
  match n with
  | O =>
      s
  | Succ n =>
      do _k ← _k - 1 ;
      do s ← body _k s ;
      static_iter_down_aux _k s n
  end.

Lemma wp_static_iter_down_aux :
  ∀ n,
  ∀IntU _k k ,
  unsigned (k - Z.of_nat n) →
  ITER_Z (k - Z.of_nat n) k Down
    (λ j s Q, ∀ _j, isInt _j j → wp (body _j s) Q)
    (λ s Q, wp (static_iter_down_aux _k s n) Q).
Proof.
  induction n as [| n]; simpl static_iter_down_aux;
  intros; ITER; z in *; [| expand_ITER in IHn ].
  (* Base case. *)
  { wp_ret. }
  (* Step case. *)
  { wp_bind_eq.
    wp_op Hbody shadowing: s.
    wp_op IHn shadowing: s.
    tc. }
Qed.

End Body.

(* Specialize [static_iter_down] for [N]. *)

Definition iter_down_N _k s body :=
  Eval compute -[bind] in static_iter_down_aux body _k s N.

(* Print iter_down_N. *)

Lemma wp_iter_down_N (body : int → S → S) :
  ∀IntU _k k ,
  unsigned (k - NZ) →
  ITER_Z (k - NZ) k Down
    (λ j s Q, ∀ _j, isInt _j j → wp (body _j s) Q)
    (λ s Q, wp (iter_down_N _k s body) Q).
Proof.
  intros. ITER.
  change (iter_down_N _k s body) with (static_iter_down_aux body _k s N).
  unfold NZ. z.
  wp_op wp_static_iter_down_aux shadowing: s.
  tc.
Qed.

(* -------------------------------------------------------------------------- *)

(* An unrolled variant of [iter_down]. *)

(* [iter_down_N] is used at each iteration, so the cost of the
   comparison and conditional jump is paid only once in [N]
   iterations. *)

Section Body.
Variable body : int → S → S.

Fixpoint iter_down_unrolled_aux _k _n s (ACC : Acc ilt _n) :=
  IFC _n <? Ni THEN λ _,
    iter_down (_k - _n) _k s body
  ELSE λ Hn,
    do s ← iter_down_N _k s body ;
    do _k ← _k - Ni ;
    let _n := _n - Ni in
    iter_down_unrolled_aux _k _n s (Acc_inv ACC (ilt_n_minus_N Hn)).

Lemma wp_iter_down_unrolled_aux :
  ∀IntU _n n ,
  ∀IntU _k k ,
  n ≤ k →
  ∀ ACC,
  ITER_Z (k - n) k Down
    (λ j s Q, ∀ _j, isInt _j j → wp (body _j s) Q)
    (λ s Q, wp (iter_down_unrolled_aux _k _n s ACC) Q).
Proof.
  by well-founded induction on _n along ilt.
  intros. ITER. expand_ITER in IH.
  intros; destruct ACC; simpl.
  wp_if; z.
  (* Case [n < N]. *)
  { wp_op wp_iter_down with invariant: inv; last wp_shadow s.
    eauto. }
  (* Case [N ≤ n]. *)
  { wp_op wp_iter_down_N shadowing: s.
    { unfold NZ. lia. }
    { clear dependent s.
      wp_body ? j s introducing: (fun _ => z_step; intros _j ?).
      unfold NZ in *.
      wp_apply Hbody. }
    subst. unfold NZ in *. z in *.
    wp_bind_eq.
    wp_op IH shadowing: s.
    tc. }
Qed.

End Body.

Definition iter_down_unrolled _i _k s body :=
  if _k ≤? _i then s
  else iter_down_unrolled_aux body _k (_k - _i) s ltac:(tc).

Lemma wp_iter_down_unrolled :
  ∀IntU _i i ,
  ∀IntU _k k ,
  ∀ body,
  ITER_Z i k Down
    (λ j s Q, ∀ _j, isInt _j j → wp (body _j s) Q)
    (λ s Q, wp (iter_down_unrolled _i _k s body) Q).
Proof.
  intros. ITER. unfold iter_down_unrolled.
  wp_if.
  { wp_ret. }
  { z. wp_op wp_iter_down_unrolled_aux shadowing: s. eauto. }
Qed.

End IterDown.

(* -------------------------------------------------------------------------- *)

(* The tactic [wp_iter_down_body _j j s] should be used upon entry into
   the loop body. It introduces the index [_j] and its integer model [j]
   as well as the state [s]. *)

(* Prior to using this tactic, one can use [clear dependent] to clear any
   pre-existing variables by the same names. *)

Tactic Notation "wp_iter_down_body"
  simple_intropattern(_j) simple_intropattern(j) simple_intropattern(s) :=
  wp_body ? j s introducing: (fun _ => z_step; intros _j ?).

(* -------------------------------------------------------------------------- *)

(* An exitable loop, counting down. The loop can be broken via an early
   exit: the loop body receives two continuations [continue] and [break] and
   must invoke either [continue s] or [break s x]. An invocation of the loop
   body takes the form [body _j s continue break]. *)

Section XIterDown.
Context {S A : Type}.
Implicit Types s : S.
Open Scope uint63.

Section Body.
Variable body : ∀ {W}, int → S → (S → W) → (S → A → W) → W.

Fixpoint xiter_down_aux _i _k s
  (ACC : Acc (rilt _i) _k)
: S * outcome A :=
  IFC _k =? _i THEN λ _,
    let continue s := (s, Continue) in
    let break s x := (s, Break x) in
    body _k s continue break
  ELSE λ Hki,
    let continue s := xiter_down_aux _i (_k - 1) s
                        (Acc_inv ACC (rilt_n_minus_1 _k _i Hki)) in
    let break s x := (s, Break x) in
    body _k s continue break.

End Body.

Definition xiter_down _i _k s body :=
  if _k ≤? _i then (s, Continue)
  else xiter_down_aux body _i (_k - 1) s ltac:(tc).

End XIterDown.

(* A specification of [xiter_down_aux]. *)

Lemma wp_xiter_down_aux {S A}
  (body : ∀ {W}, int → S → (S → W) → (S → A → W) → W) :
  ∀IntU _i i ,
  ∀IntU _k k ,
  i ≤ k →
  ∀ ACC,
  XITER_Z i (k + 1) Down
    (λ j _ s continue break Q, ∀ _j, isInt _j j → wp (body _j s continue break) Q)
    (λ s Q, wp (xiter_down_aux (@body) _i _k s ACC) Q).
Proof.
  intros _i i ? ?.
  by well-founded induction on _k along (rilt _i).
  intros. XITER. expand_ITER in IH.
  destruct ACC; simpl.
  wp_if; z.
  (* Case [k = i]. *)
  { wp_apply Hbody; intros; wp_ret. }
  (* Case [k ≠ i]. *)
  { wp_apply Hbody; intros.
    (* Normal continuation. *)
    + wp_op IH introducing: (s' & out). eauto.
    (* Exit continuation. *)
    + wp_ret. eauto. }
Qed.

(* A specification of [xiter_down]. *)

Lemma wp_xiter_down {S A}
  (body : ∀ {W}, int → S → (S → W) → (S → A → W) → W) :
  ∀IntU _i i ,
  ∀IntU _k k ,
  XITER_Z i k Down
    (λ j _ s continue break Q, ∀ _j, isInt _j j → wp (body _j s continue break) Q)
    (λ s Q, wp (xiter_down _i _k s (@body)) Q).
Proof.
  intros. XITER. unfold xiter_down.
  wp_if; z.
  (* Case [k ≤ i]. *)
  { wp_ret. }
  (* Case [i < k]. *)
  { wp_op wp_xiter_down_aux.
    clear dependent s. wp_intro (s & out).
    eauto. }
Qed.

(* The tactic [wp_xiter_down_body _j j s] should be used upon entry into
   the loop body. It introduces the index [_j] and its integer model [j]
   as well as the state [s]. *)

(* Prior to using this tactic, one can use [clear dependent] to clear any
   pre-existing variables by the same names. *)

Tactic Notation "wp_xiter_down_body"
  simple_intropattern(_j) simple_intropattern(j) simple_intropattern(s) :=
  wp_body ? j s ?????? introducing: (fun _ => z_step; intros _j ?).

(* -------------------------------------------------------------------------- *)

(* A simplified exitable loop with a state of type [unit]. *)

(* The calling convention of the body is [body _i continue break]. *)

Section UXIterDown.
Context {A : Type}.
Open Scope uint63.

Section Body.
Variable body : ∀ {W}, int → (unit → W) → (A → W) → W.

Fixpoint uxiter_down_aux _i _k (ACC : Acc (rilt _i) _k) : outcome A :=
  IFC _k =? _i THEN λ _,
    let continue '() := Continue in
    let break x := Break x in
    body _k continue break
  ELSE λ Hki,
    let continue '() := uxiter_down_aux _i (_k - 1)
                         (Acc_inv ACC (rilt_n_minus_1 _k _i Hki)) in
    let break x := Break x in
    body _k continue break.

End Body.

Definition uxiter_down _i _k
  (body : ∀ {W}, int → (unit → W) → (A → W) → W) :=
  if _k ≤? _i then Continue
  else uxiter_down_aux (@body) _i (_k - 1) ltac:(tc).

End UXIterDown.

(* A specification of [uxiter_down_aux]. *)

Lemma wp_uxiter_down_aux {A}
  (body : ∀ {W}, int → (unit → W) → (A → W) → W) :
  ∀IntU _i i ,
  ∀IntU _k k ,
  i ≤ k →
  ∀ ACC,
  UXITER_Z i (k + 1) Down
    (λ j _ continue break Q, ∀ _j, isInt _j j → wp (body _j continue break) Q)
    (λ Q, wp (uxiter_down_aux (@body) _i _k ACC) Q).
Proof.
  intros _i i ? ?.
  by well-founded induction on _k along (rilt _i).
  intros. UXITER. expand_ITER in IH.
  destruct ACC; simpl.
  wp_if.
  (* Case [k = i]. *)
  { wp_apply Hbody; intros; wp_ret. }
  (* Case [k ≠ i]. *)
  { wp_apply Hbody; intros.
    (* Normal continuation. *)
    + wp_op IH introducing: out. eauto.
    (* Exit continuation. *)
    + wp_ret. eauto. }
Qed.

(* A specification of [uxiter_down]. *)

Lemma wp_uxiter_down {A}
  (body : ∀ {W}, int → (unit → W) → (A → W) → W) :
  ∀IntU _i i ,
  ∀IntU _k k ,
  UXITER_Z i k Down
    (λ j _ continue break Q, ∀ _j, isInt _j j → wp (body _j continue break) Q)
    (λ Q, wp (uxiter_down _i _k (@body)) Q).
Proof.
  intros. UXITER. unfold uxiter_down.
  wp_if; z.
  (* Case [k ≤ i]. *)
  { wp_ret. }
  (* Case [i < k]. *)
  { wp_op wp_uxiter_down_aux; wp_intro out.
    eauto. }
Qed.

(* The tactic [wp_uxiter_down_body _j j] should be used upon entry into
   the loop body. It introduces the index [_j] and its integer model [j]. *)

(* Prior to using this tactic, one can use [clear dependent] to clear any
   pre-existing variables by the same names. *)

Tactic Notation "wp_uxiter_down_body"
  simple_intropattern(_j) simple_intropattern(j) :=
  wp_body ? j ?????? introducing: (fun _ => z_step; intros _j ?).

(* -------------------------------------------------------------------------- *)

(* A loop, counting up from [i] to [k], using machine integers. *)

(* Our intervals are semi-open on the right end: [i] is included,
   [k] is excluded. *)

(* [iter_up _i _k s body] applies the loop body [body] to every
   machine integer from [_i], included, up to [_k], excluded. A state
   of type [S] is carried, whose initial value is [s]. *)

Section IterUp.
Context {S : Type}.
Implicit Types s : S.
Open Scope uint63.

Section Body.
Variable body : int → S → S.

(* We define [iter_up_aux] by well-founded recursion over a proof of
   accessibility of the index [_i]. In the first branch, the fact that
   [_i <? _k] is true is needed in order to prove that [_i + 1] is
   less than [_i], a fact which itself is required by the termination
   argument. *)

Fixpoint iter_up_aux _i _k s (ACC : Acc igt _i) :=
  IFC _i <? _k THEN λ Hik,
    do s ← body _i s ;
    iter_up_aux (_i + 1) _k s
                (Acc_inv ACC (igt_n_plus_1 _i _k Hik))
  ELSE λ _,
    s.

End Body.

Definition iter_up _i _k s body :=
  iter_up_aux body _i _k s ltac:(tc).

(* The proof irrelevance and fixed point lemmas. *)

(* I keep these lemmas for the record, but one could establish the
   Hoare-style reasoning rules [wp_iter_up_aux] and [wp_iter_up] without
   using them. See [xiter_up], where the reasoning rules are established
   directly, without proving proof irrelevance first. *)

Lemma iter_up_aux_eq _i : ∀ _k s body (ACC : Acc igt _i),
  iter_up_aux body _i _k s ACC =
  if _i <? _k then
    do s ← body _i s ;
    iter_up (_i + 1) _k s body
  else
    s.
Proof.
  by well-founded induction on _i along igt.
  intros; destruct ACC; simpl.
  eapply IFC_if; [| eauto ]. intro.
  setoid_rewrite IH; tc2.
Qed.

Lemma iter_up_eq _i _k s body :
  iter_up _i _k s body =
  if _i <? _k then
    do s ← body _i s ;
    iter_up (_i + 1) _k s body
  else
    s.
Proof.
  unfold iter_up. eapply iter_up_aux_eq.
Qed.

(* A specification of [iter_up]. *)

Lemma wp_iter_up (body : int → S → S) :
  ∀IntU _i i ,
  ∀IntU _k k ,
  ITER_Z i k Up
    (λ j s Q, ∀ _j, isInt _j j → wp (body _j s) Q)
    (λ s Q, wp (iter_up _i _k s body) Q).
Proof.
  by well-founded induction on _i along igt.
  intros. ITER. expand_ITER in IH.
  unfold iter_up. rewrite iter_up_aux_eq.
  wp_if.
  (* Case [i < k]. *)
  { wp_op Hbody shadowing: s.
    wp_op IH shadowing: s.
    wp_ret. }
  (* Case [¬ i < k]. *)
  { wp_ret. }
Qed.

(* -------------------------------------------------------------------------- *)

(* A "static" variant of [iter_up], where the difference [k - i] is
   statically known and is represented by a natural number [n]. *)

Section Body.
Variable body : int → S → S.

Fixpoint static_iter_up_aux _i s (n : nat) :=
  match n with
  | O =>
      s
  | Succ n =>
      do s ← body _i s ;
      do _i ← _i + 1 ;
      static_iter_up_aux _i s n
  end.

Lemma wp_static_iter_up_aux :
  ∀ n,
  ∀IntU _i i ,
  unsigned (i + Z.of_nat n) →
  ITER_Z i (i + Z.of_nat n) Up
    (λ j s Q, ∀ _j, isInt _j j → wp (body _j s) Q)
    (λ s Q, wp (static_iter_up_aux _i s n) Q).
Proof.
  induction n as [| n]; simpl static_iter_up_aux;
  intros; ITER; z in *; [| expand_ITER in IHn ].
  (* Base case. *)
  { wp_ret. }
  (* Step case. *)
  { wp_op Hbody shadowing: s.
    wp_bind_eq.
    wp_op IHn shadowing: s.
    tc. }
Qed.

End Body.

(* Specialize [static_iter_up] for [N]. *)

Definition iter_up_N _i s body :=
  Eval compute -[bind] in static_iter_up_aux body _i s N.

(* Print iter_up_N. *)

Lemma wp_iter_up_N (body : int → S → S) :
  ∀IntU _i i ,
  unsigned (i + NZ) →
  ITER_Z i (i + NZ) Up
    (λ j s Q, ∀ _j, isInt _j j → wp (body _j s) Q)
    (λ s Q, wp (iter_up_N _i s body) Q).
Proof.
  intros. ITER.
  change (iter_up_N _i s body) with (static_iter_up_aux body _i s N).
  wp_apply wp_static_iter_up_aux.
Qed.

(* -------------------------------------------------------------------------- *)

(* An unrolled variant of [iter_up]. *)

Section Body.
Variable body : int → S → S.

Fixpoint iter_up_unrolled_aux _i _n s (ACC : Acc ilt _n) :=
  IFC _n <? Ni THEN λ _,
    iter_up _i (_i + _n) s body
  ELSE λ Hn,
    do s ← iter_up_N _i s body ;
    do _i ← _i + Ni ;
    let _n := _n - Ni in
    iter_up_unrolled_aux _i _n s (Acc_inv ACC (ilt_n_minus_N Hn)).

Lemma wp_iter_up_unrolled_aux :
  ∀IntU _n n ,
  ∀IntU _i i ,
  unsigned (i + n) →
  ∀ ACC,
  ITER_Z i (i + n) Up
    (λ j s Q, ∀ _j, isInt _j j → wp (body _j s) Q)
    (λ s Q, wp (iter_up_unrolled_aux _i _n s ACC) Q).
Proof.
  by well-founded induction on _n along ilt.
  intros. ITER. expand_ITER in IH.
  intros; destruct ACC; simpl.
  wp_if; z.
  (* Case [n < N]. *)
  { wp_op wp_iter_up with invariant: inv; last wp_shadow s.
    eauto. }
  (* Case [N ≤ n]. *)
  { wp_op wp_iter_up_N shadowing: s.
    { unfold NZ. lia. }
    { clear dependent s.
      wp_body ? j s introducing: (fun _ => z_step; intros _j ?).
      unfold NZ in *.
      wp_apply Hbody. }
    subst. unfold NZ in *. z in *.
    wp_bind_eq.
    wp_op IH shadowing: s.
    tc. }
Qed.

End Body.

Definition iter_up_unrolled _i _k s body :=
  if _k ≤? _i then s
  else iter_up_unrolled_aux body _i (_k - _i) s ltac:(tc).

Lemma wp_iter_up_unrolled :
  ∀IntU _i i ,
  ∀IntU _k k ,
  ∀ s body,
  ITER_Z i k Up
    (λ j s Q, ∀ _j, isInt _j j → wp (body _j s) Q)
    (λ s Q, wp (iter_up_unrolled _i _k s body) Q).
Proof.
  intros. ITER. unfold iter_up_unrolled.
  wp_if.
  { wp_ret. }
  { z. wp_op wp_iter_up_unrolled_aux shadowing: s. eauto. }
Qed.

End IterUp.

(* -------------------------------------------------------------------------- *)

(* The tactic [wp_iter_up_body _j j s] should be used upon entry into the
   loop body. It introduces the index [_j] and its integer model [j] as well
   as the state [s]. *)

(* Prior to using this tactic, one can use [clear dependent] to clear any
   pre-existing variables by the same names. *)

Tactic Notation "wp_iter_up_body"
  simple_intropattern(_j) simple_intropattern(j) simple_intropattern(s) :=
  wp_body j ? s introducing: (fun _ => z_step; intros _j ?).

(* -------------------------------------------------------------------------- *)

(* An exitable loop, counting up from [i] to [k]. The loop can be broken
   via an early exit: the loop body receives two continuations [continue]
   and [break] and must invoke either [continue s] or [break s x]. An
   invocation of the loop body takes the form [body _i s continue break]. *)

Section XiterUp.
Context {S A : Type}.
Implicit Types s : S.
Open Scope uint63.

Section Body.
Variable body : ∀ {W}, int → S → (S → W) → (S → A → W) → W.

Fixpoint xiter_up_aux _i _k s (ACC : Acc igt _i) : S * outcome A :=
  IFC _i <? _k THEN λ Hik,
    let continue s := xiter_up_aux (_i + 1) _k s
                        (Acc_inv ACC (igt_n_plus_1 _i _k Hik)) in
    let break s x := (s, Break x) in
    body _i s continue break
  ELSE λ _,
    (s, Continue).

End Body.

Definition xiter_up _i _k s body :=
  xiter_up_aux body _i _k s ltac:(tc).

End XiterUp.

(* We do not establish a proof irrelevance / fixed point lemma here,
   because that would be difficult: we would need to either use the
   axiom of functional extensionality or make a hypothesis about
   [body]. The difficulty is that the recursive call appears nested
   inside the continuation [continue], that is, under a lambda. *)

(* Instead, we proceed directly to the proof of Hoare-style reasoning
   rules for [xiter_up_aux] and [xiter_up]. *)

(* The specification of [xiter_up_aux]. *)

Lemma wp_xiter_up_aux {S A}
  (body : ∀ {W}, int → S → (S → W) → (S → A → W) → W) :
  ∀IntU _i i ,
  ∀IntU _k k ,
  ∀ ACC,
  XITER_Z i k Up
    (λ j _ s continue break Q, ∀ _j, isInt _j j → wp (body _j s continue break) Q)
    (λ s Q, wp (xiter_up_aux (@body) _i _k s ACC) Q).
Proof.
  by well-founded induction on _i along igt.
  intros. XITER. expand_ITER in IH.
  destruct ACC; simpl.
  wp_if; z.
  (* Case [i < k]. *)
  { wp_apply Hbody; intros.
    (* Normal continuation. *)
    + wp_op IH introducing: (s' & out). eauto.
    (* Exit continuation. *)
    + wp_ret. eauto. }
  (* Case [k ≤ i]. *)
  { wp_ret. }
Qed.

(* The specification of [xiter_up]. *)

Lemma wp_xiter_up {S A}
  (body : ∀ {W}, int → S → (S → W) → (S → A → W) → W) :
  ∀IntU _i i ,
  ∀IntU _k k ,
  XITER_Z i k Up
    (λ j _ s continue break Q, ∀ _j, isInt _j j → wp (body _j s continue break) Q)
    (λ s Q, wp (xiter_up _i _k s (@body)) Q).
Proof.
  unfold xiter_up. eauto using wp_xiter_up_aux.
Qed.

Tactic Notation "wp_xiter_up_body"
  simple_intropattern(_j) simple_intropattern(j) simple_intropattern(s) :=
  wp_body j ? s ?????? introducing: (fun _ => z_step; intros _j ?).

(* -------------------------------------------------------------------------- *)

(* A simplified exitable loop with a state of type [unit]. *)

(* The calling convention of the body is [body _i continue break]. *)

Section UXIterUp.
Context {A : Type}.
Open Scope uint63.

Section Body.
Variable body : ∀ {W}, int → (unit → W) → (A → W) → W.

Fixpoint uxiter_up_aux _i _k (ACC : Acc igt _i) : outcome A :=
  IFC _i <? _k THEN λ Hik,
    let continue '() := uxiter_up_aux (_i + 1) _k
                         (Acc_inv ACC (igt_n_plus_1 _i _k Hik)) in
    let break x := Break x in
    body _i continue break
  ELSE λ _,
    Continue.

End Body.

Definition uxiter_up _i _k body :=
  uxiter_up_aux body _i _k ltac:(tc).

End UXIterUp.

(* The specification of [uxiter_up_aux]. *)

Lemma wp_uxiter_up_aux {A}
  (body : ∀ {W}, int → (unit → W) → (A → W) → W) :
  ∀IntU _i i ,
  ∀IntU _k k ,
  ∀ ACC,
  UXITER_Z i k Up
    (λ j _ continue break Q, ∀ _j, isInt _j j → wp (body _j continue break) Q)
    (λ Q, wp (uxiter_up_aux (@body) _i _k ACC) Q).
Proof.
  by well-founded induction on _i along igt.
  intros. UXITER. expand_ITER in IH.
  destruct ACC; simpl.
  wp_if; z.
  (* Case [i < k]. *)
  { wp_apply Hbody; intros.
    (* Normal continuation. *)
    + wp_op IH introducing: out. eauto.
    (* Exit continuation. *)
    + wp_ret. eauto. }
  (* Case [k ≤ i]. *)
  { wp_ret. }
Qed.

(* The specification of [uxiter_up]. *)

Lemma wp_uxiter_up {A} (body : ∀ {W}, int → (unit → W) → (A → W) → W) :
  ∀IntU _i i ,
  ∀IntU _k k ,
  UXITER_Z i k Up
    (λ j _ continue break Q, ∀ _j, isInt _j j → wp (body _j continue break) Q)
    (λ Q, wp (uxiter_up _i _k (@body)) Q).
Proof.
  unfold uxiter_up. eauto using wp_uxiter_up_aux.
Qed.

(* The tactic [wp_uxiter_up_body _j j] should be used upon entry into the
   loop body. It introduces the index [_j] and its integer model [j]. *)

(* Prior to using this tactic, one can use [clear dependent] to clear any
   pre-existing variables by the same names. *)

Tactic Notation "wp_uxiter_up_body"
  simple_intropattern(_j) simple_intropattern(j) :=
  wp_body j ? ?????? introducing: (fun _ => z_step; intros _j ?).
