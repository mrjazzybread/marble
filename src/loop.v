From stdpp Require Import numbers well_founded.
From Stdlib Require Export ZifyNat.
  (* [ZifyNat] magically makes [lia] more powerful,
     including on goals that involve division in Z *)
From Stdlib Require Import Uint63 ZifyUint63.
  (* [ZifyUint63] magically makes [lia] more powerful *)
From Stdlib Require Import Wellfounded.Wellfounded.
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
  (* Perform arithmetic simplification. *)
  z in Hx;
  (* Decompose existential quantifiers and conjunctions. *)
  unpack in Hx.

(* -------------------------------------------------------------------------- *)

(* A loop, counting down, using machine integers. *)

(* [iter_down _i _k s body] applies the loop body [body] to every machine
   integer from [_k], excluded, down to [_i], included. A state of type [S]
   is carried, whose initial value is [s]. *)

(* [iter_down_aux _i _k s body] applies the loop body [body] to every
   machine integer from [_k], INCLUDED, down to [_i], included. *)

Section IterDown.
Context {S : Type}.
Implicit Types s : S.
Implicit Types body : int → S → S.
Open Scope uint63.

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

Fixpoint iter_down_aux _i _k s body (ACC : Acc (rilt _i) _k) :=
  IFC _k =? _i THEN λ _,
    do s ← body _k s ;
    s
  ELSE λ Hki,
    do s ← body _k s ;
    iter_down_aux _i (_k - 1) s body (Acc_rilt_n_minus_1 _k _i ACC Hki).

Definition iter_down _i _k s body :=
  if _k ≤? _i then s
  else iter_down_aux _i (_k - 1) s body (Wf_rilt _i (_k - 1)).

End IterDown.

(* A specification of [iter_down_aux]. *)

(* This specification requires [i ≤ k]: that is, the top index [k] must
   be greater than or equal to the bottom index [i]. This hypothesis is
   natural: it is required to guarantee that no underflow takes place. *)

Lemma wp_iter_down_aux {S} (body : int → S → S) :
  ∀IntU _i i ,
  ∀IntU _k k ,
  i ≤ k →
  ∀ ACC,
  ITER_Z i (k + 1) Down
    (λ j s Q, ∀ _j, isInt _j j → wp (body _j s) Q)
    (λ s Q, wp (iter_down_aux _i _k s body ACC) Q).
Proof.
  intros _i i ? ?.
  by well-founded induction on _k along (rilt _i).
  intros. ITER. expand_ITER in IH.
  intros; destruct ACC; simpl.
  wp_if; z.
  (* Case [k = i]. *)
  { wp_op Hstep shadowing: s.
    wp_ret. }
  (* Case [k ≠ i]. *)
  { wp_op Hstep shadowing: s.
    wp_op IH shadowing: s.
    eauto. }
Qed.

(* A specification of [iter_down]. *)

Lemma wp_iter_down {S} (body : int → S → S) :
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

(* The tactic [wp_iter_down_body _j j s] should be used upon entry into
   the loop body. It introduces the index [_j] and its integer model [j]
   as well as the state [s]. *)

(* Prior to using this tactic, one can use [clear dependent] to clear any
   pre-existing variables by the same names. *)

Tactic Notation "wp_iter_down_body"
  simple_intropattern(_j) simple_intropattern(j) simple_intropattern(s) :=
  wp_body ? j s introducing: (fun _ => z_step; intros _j ?).

(* -------------------------------------------------------------------------- *)

(* An exitable loop, counting down]. The loop can be broken via an early
   exit: the loop body receives two continuations [continue] and [break] and
   must invoke either [continue s] or [break s x]. An invocation of the loop
   body takes the form [body _j s continue break]. *)

Section XIterDown.
Context {S A : Type}.
Implicit Types s : S.
Open Scope uint63.

Fixpoint xiter_down_aux _i _k s
  (body : ∀ {W}, int → S → (S → W) → (S → A → W) → W)
  (ACC : Acc (rilt _i) _k)
: S * outcome A :=
  IFC _k =? _i THEN λ _,
    let continue s := (s, Continue) in
    let break s x := (s, Break x) in
    body _k s continue break
  ELSE λ Hki,
    let continue s := xiter_down_aux _i (_k - 1) s (@body)
                        (Acc_rilt_n_minus_1 _k _i ACC Hki) in
    let break s x := (s, Break x) in
    body _k s continue break.

Definition xiter_down _i _k s body :=
  if _k ≤? _i then (s, Continue)
  else xiter_down_aux _i (_k - 1) s body (Wf_rilt _i (_k - 1)).

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
    (λ s Q, wp (xiter_down_aux _i _k s (@body) ACC) Q).
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

Fixpoint uxiter_down_aux _i _k
  (body : ∀ {W}, int → (unit → W) → (A → W) → W)
  (ACC : Acc (rilt _i) _k)
: outcome A :=
  IFC _k =? _i THEN λ _,
    let continue '() := Continue in
    let break x := Break x in
    body _k continue break
  ELSE λ Hki,
    let continue '() := uxiter_down_aux _i (_k - 1) (@body)
                         (Acc_rilt_n_minus_1 _k _i ACC Hki) in
    let break x := Break x in
    body _k continue break.

Definition uxiter_down _i _k
  (body : ∀ {W}, int → (unit → W) → (A → W) → W) :=
  if _k ≤? _i then Continue
  else uxiter_down_aux _i (_k - 1) (@body) (Wf_rilt _i (_k - 1)).

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
    (λ Q, wp (uxiter_down_aux _i _k (@body) ACC) Q).
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
Implicit Types body : int → S → S.
Open Scope uint63.

(* We define [iter_up_aux] by well-founded recursion over a proof of
   accessibility of the index [_i]. In the first branch, the fact that
   [_i <? _k] is true is needed in order to prove that [_i + 1] is
   less than [_i], a fact which itself is required by the termination
   argument. *)

Fixpoint iter_up_aux _i _k s body (ACC : Acc igt _i) :=
  IFC _i <? _k THEN λ Hik,
    do s ← body _i s ;
    iter_up_aux (_i + 1) _k s body
                (Acc_igt_n_plus_1 _i _k ACC Hik)
  ELSE λ _,
    s.

Definition iter_up _i _k s body :=
  iter_up_aux _i _k s body (Wf_igt _i).

(* The proof irrelevance and fixed point lemmas. *)

(* I keep these lemmas for the record, but one could establish the
   Hoare-style reasoning rules [wp_iter_up_aux] and [wp_iter_up] without
   using them. See [xiter_up], where the reasoning rules are established
   directly, without proving proof irrelevance first. *)

Lemma iter_up_aux_eq _i : ∀ _k s body (ACC : Acc igt _i),
  iter_up_aux _i _k s body ACC =
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

End IterUp.

(* A specification of [iter_up]. *)

Lemma wp_iter_up {S} (body : int → S → S) :
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
  { wp_op Hstep shadowing: s.
    wp_op IH shadowing: s.
    wp_ret. }
  (* Case [¬ i < k]. *)
  { wp_ret. }
Qed.

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

Fixpoint xiter_up_aux _i _k s
  (body : ∀ {W}, int → S → (S → W) → (S → A → W) → W)
  (ACC : Acc igt _i)
: S * outcome A :=
  IFC _i <? _k THEN λ Hik,
    let continue s := xiter_up_aux (_i + 1) _k s (@body)
                        (Acc_igt_n_plus_1 _i _k ACC Hik) in
    let break s x := (s, Break x) in
    body _i s continue break
  ELSE λ _,
    (s, Continue).

Definition xiter_up _i _k s body :=
  xiter_up_aux _i _k s body (Wf_igt _i).

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
    (λ s Q, wp (xiter_up_aux _i _k s (@body) ACC) Q).
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

Fixpoint uxiter_up_aux _i _k
  (body : ∀ {W}, int → (unit → W) → (A → W) → W)
  (ACC : Acc igt _i)
: outcome A :=
  IFC _i <? _k THEN λ Hik,
    let continue '() := uxiter_up_aux (_i + 1) _k (@body)
                         (Acc_igt_n_plus_1 _i _k ACC Hik) in
    let break x := Break x in
    body _i continue break
  ELSE λ _,
    Continue.

Definition uxiter_up _i _k body :=
  uxiter_up_aux _i _k body (Wf_igt _i).

End UXIterUp.

(* The specification of [uxiter_up_aux]. *)

Lemma wp_uxiter_up_aux {A}
  (body : ∀ {W}, int → (unit → W) → (A → W) → W) :
  ∀IntU _i i ,
  ∀IntU _k k ,
  ∀ ACC,
  UXITER_Z i k Up
    (λ j _ continue break Q, ∀ _j, isInt _j j → wp (body _j continue break) Q)
    (λ Q, wp (uxiter_up_aux _i _k (@body) ACC) Q).
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
