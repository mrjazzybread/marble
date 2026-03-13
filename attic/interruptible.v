(* -------------------------------------------------------------------------- *)

(* Generic specifications for an interruptible loop. *)

(* An interruptible loop lets the loop body return an instruction to either
   continue or stop (break). We write [out] for such an instruction, because
   it is an option, and it is the outcome of the loop body. *)

(* An interruptible loop is essentially a normal loop where the user state
   is a pair [(s, out)]. When [out] is [break _], the loop stops. In the
   contrapositive form, if the loop body is invoked, then [out] must be
   [continue]. Thus the loop body may assume [out = continue]. Furthermore,
   once the loop terminates, one cannot assume [complete k], as usual;
   instead one must assume [complete k ∨ broken out]. *)

(* We could adopt an even more abstract point of view, where the user state
   is not necessarily a pair, and a predicate of type [S → Prop] determines
   whether the user state allows or forbids continuing. But adopting a more
   specific convention is more comfortable. *)

Section UserState.

(* The first component of the user's state has type [S]. *)
Context {S : Type}.
Implicit Types s : S.

(* The second component of the user state has type [option A].
   In other words, [A] is the type of [x] in [break x]. *)
Context {A : Type}.
Implicit Types out : option A.
Implicit Types x : A.

(* The complete user state has type [S * option A]. *)
Local Notation U := (S * option A)%type.

(* In the type of the loop body, we use [S → WP U] instead of [U → WP U]
   because when the loop body is invoked, the second component of the user
   state is known; it must be [continue]. *)
Variable body : O → P → S → WP U.

(* Same convention here *)
Variable loop : S → WP U.

(* The user's loop invariant takes the form [inv i s out] where [i] is
   the current logical producer state and [(s, out)] is the current user
   state. We use a curried form for increased comfort. *)
Implicit Types inv : P → S → option A → Prop.

(* The specification of a loop takes the following form. This is a
   variant of [ITER]; we highlight just on the differences. *)

Definition ITERX :=
  ∀ inv s ,
  (* Initially, [out] is continue. *)
  inv init s continue →
  (* When the loop body is invoked, it can assume that [out] is [continue]. *)
  ( ∀ j0 o j j1 s ,
    inv j0 s continue →
    step j0 o j j1 →
    body o j s (λ '(s, out), inv j1 s out)
  ) →
  (* Once the loop ends, we have either [complete k] or [broken out]. *)
  loop s (λ '(s, out), ∃ k, (complete k ∨ broken out) ∧ inv k s out).

End UserState.

(* -------------------------------------------------------------------------- *)

Definition ITERX_UP {S A}
  (i k : nat)
  (body : int → nat → S → WP (S * option A))
  (loop : S → WP (S * option A))
:=
  ITERX (step_up i k) i (complete_up i k) body loop.

(* -------------------------------------------------------------------------- *)

(* An interruptible loop, counting up from [a] to [b]. The loop can be
   broken via an early exit: the loop body [f] returns an instruction to
   either continue or stop (break). *)

Section InterruptibleUpAux.
Context {S A : Type}.
Implicit Types _a : int.
Implicit Types s : S.

(* We hoist the loop-invariant parameters out of the loop, because
   otherwise Equations produces ugly code where these parameters are
   carried around in a tuple, itself encoded using nested pairs. *)

Variable _b : int.
Variable f : int → S → S * option A.

(* [interruptible_up_aux _a s] applies the loop body [f] to every machine
   integer from [_a], included, up to [_b], excluded. A state of type [S]
   is carried, whose initial value is [s]. If [f] returns [break x] then
   the loop stops and returns the pair [(s, break x)] where [s] is the
   current state. If [f] returns [continue] then the loop continues. If
   [f] never returns [break _] then the loop runs all the way to the end
   and returns [(s, continue)] where [s] is the final state. *)

(* Another possible convention for an interruptible loop would be to
   assume that the loop-carried state contains the continuation flag
   (i.e., the state typically has type [S * option A]) and to let the
   user provide a function that inspects the current state and
   determines whether the loop should continue or stop. *)

Equations interruptible_up_aux _a s : S * option A
by wf _a igt :=
interruptible_up_aux _a s with inspect (_a <? _b)%uint63 => {
| inspected true :=
    do so ← f _a s ;
    let '(s, o) := so in
    match o with
    | continue =>
        interruptible_up_aux (_a+1)%uint63 s
    | break _ =>
        so
    end
| inspected false :=
    (s, continue)
}.
Next Obligation.
  eauto using safe_increment'.
Qed.

End InterruptibleUpAux.

Section InterruptibleUp.
Context {S A : Type}.
Implicit Types _a _b : int.
Implicit Types s : S.
Implicit Types f : int → S → S * option A.

(* A specification of [interruptible_up_aux]. *)

Lemma wp_interruptible_up_aux f :
  ∀ _a a _b b ,
  isInt _a a →
  isInt _b b →
  representable a →
  representable b →
  ITERX_UP
    a b
    (λ _j j s Q, a ≤ j < b → representable j → wp (f _j s) Q)
    (λ s Q, wp (interruptible_up_aux _b f _a s) Q).
Proof.
  intros. ITER.
  funelim (interruptible_up_aux _b f _a s); cleanup; clear Heqcall;
  isBool_magic; autorewrite with nat.
  (* [funelim] creates an induction hypothesis that contains
     spurious parameters of type [S * option A] and [option A]. *)
  assert (dummy: option A). { exact continue. }
  (* Case [a < b]. *)
  { wp_op Hstep s'. clear dependent s. destruct s' as [ s [x|] ].
    (* Subcase: [out] is [break x]. *)
    + wp_ret. eauto with lia.
    (* Subcase: [out] is [continue]. *)
    + eapply wp_conseq.
      - eapply H; itc.
      - autorewrite with nat. eauto. }
  (* Case [b ≤ a]. *)
  { wp_ret. eauto with lia. }
Qed.

(* A definition of [interruptible_up], with reordered parameters. *)

Definition interruptible_up _a _b s f :=
  interruptible_up_aux _b f _a s.

(* Copying the specification of [interruptible_up_aux],
   to obtain a specification of [interruptible_up],
   would be useless; they are the same up to the order of parameters. *)

Definition wp_interruptible_up :=
  wp_interruptible_up_aux.

End InterruptibleUp.

(* -------------------------------------------------------------------------- *)

(* A variant of [interruptible_up] that does not carry a state. *)

Section InterruptibleUpUnitAux.
Context {A : Type}.
Implicit Types _a : int.

Variable _b : int.
Variable f : int → option A.

Equations interruptible_up_unit_aux _a : option A
by wf _a igt :=
interruptible_up_unit_aux _a with inspect (_a <? _b)%uint63 => {
| inspected true :=
    do o ← f _a ;
    match o with
    | continue =>
        interruptible_up_unit_aux (_a+1)%uint63
    | break _ =>
        o
    end
| inspected false :=
    continue
}.
Next Obligation.
  eauto using safe_increment'.
Qed.

End InterruptibleUpUnitAux.

(* Instead of proving a specification of [interruptible_up_unit_aux],
   we first prove that it is related with [interruptible_up_aux]. *)

(* The relation is [wus], which stands for [with_unit_state]. *)

Definition wus {A} (a : A) (sa' : unit * A) :=
  a =
    do sa' ← sa' ;
    let '(s', a') := sa' in
    a'.

Lemma interruptible_up_unit_aux_eq {A} _a _b
  (f : int → option A)
  (f' : int → unit → unit * option A) :
  (∀ _i, wus (f _i) (f' _i tt)) →
  wus
    (interruptible_up_unit_aux _b f _a)
    (interruptible_up_aux _b f' _a tt).
Proof.
  intros Hf.
  funelim (interruptible_up_unit_aux _b f _a); cleanup; clear Heqcall;
  autorewrite with interruptible_up_aux; simpl; rewrite e.
  (* [funelim] introduces a spurious parameter: *)
  assert (dummy: option A). { exact continue. }
  { rewrite Hf. destruct (f' _a ()) as [ [] [|] ]; unfold bind.
    + unfold wus. eauto.
    + eauto. }
  { unfold wus. eauto. }
Qed.

Section InterruptibleUpUnit.
Context {A : Type}.
Implicit Types _a _b : int.
Implicit Types f : int → option A.

Definition interruptible_up_unit _a _b f :=
  interruptible_up_unit_aux _b f _a.

End InterruptibleUpUnit.

(* When used with [rewrite], the following lemma allows replacing a call
   to [interruptible_up_unit] with a call to [interruptible_up]. *)

Lemma interruptible_up_unit_eq {A} _a _b (f : int → option A) :
  wus
    (interruptible_up_unit _a _b f)
    (interruptible_up _a _b tt (λ _i s, do o ← f _i ; (s, o))).
Proof.
  intros.
  unfold interruptible_up_unit, interruptible_up.
  eapply interruptible_up_unit_aux_eq.
  unfold wus, bind. eauto.
Qed.

(* We do not provide a specification of [interruptible_up_unit].
   Instead, the user is expected to rewrite using the above lemma
   and to use the specification of [interruptible_up]. This can
   introduce a little noise in the proof, but seems bearable. *)
