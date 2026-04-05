From listz Require Import listz.
From marble Require Import tactics wp.

(* -------------------------------------------------------------------------- *)

(* [wp_intros x] introduces [x] and a hypothesis [Hx] and simplifies this
   hypothesis. It is typically used in the second subgoal of [wp_bind] and
   [wp_conseq]. *)

(* TODO decide whether the default definition of [wp_intros_hook]
   should include [list in Hx; zring in Hx]. *)

Global Ltac wp_intros_hook Hx :=
  (* Decompose existential quantifiers and conjunctions. *)
  unpack in Hx.

Global Ltac wp_intros x :=
  (* Eliminate a beta redex, if there is one. *)
  cbv beta;
  let Hx := fresh in
  intros x Hx;
  (* Perform simplification. *)
  wp_intros_hook Hx.

(* -------------------------------------------------------------------------- *)

(* [wp_intros_shadow x] first invokes [wp_intros x'], where [x'] is fresh,
   then forgets everything about [x] and renames [x'] into [x]. It should
   (must) be used when [x'] represents a new array that has been obtained by
   updating the array [x], or more generally, a new mutable data structure
   that has been obtained by updating the data structure [x]. This helps
   keep the goal readable and ensures mutable data structures are used
   linearly. *)

Global Ltac wp_intros_shadow x :=
  let x' := fresh in
  wp_intros x';
  clear dependent x;
  rename x' into x.

(* -------------------------------------------------------------------------- *)

(* [wp_op_nude lemma] applies the lemma [lemma], which is typically a
   reasoning rule for some operation [op], then attempts to solve its
   preconditions. The goal should have the form [wp (op ...) ?Q] where
   [?Q] is a metavariable. *)

Global Ltac wp_op_nude lemma :=
  (* Apply the reasoning rule for this operation. *)
  simple eapply lemma;
  (* Attempt to solve the preconditions. *)
  (* This incantation is not very elegant, but seems effective,
     so good enough for now. Note that the semi-colon in Ltac
     is left-associative, so each tactic in the sequence below
     is applied to *all* preconditions before the next tactic
     in the sequence is applied. *)
  list;
  intros; unpack; try subst;
  tc;
  list;
  tc.
  (* TODO try to make this incantation simpler / less costly *)

(* [wp_op lemma x] applies either [wp_bind] or [wp_conseq], then applies
   the lemma [lemma] in the first subgoal and introduces the result under
   the name [x] in the second subgoal. The goal should have the form
   [wp (op ...) Q] or [wp (do x ← op ... ; ...) Q]. *)

(* [wp_op_shadow lemma x] is identical, except it uses
   [wp_intros_shadow x] instead of [wp_intros x]. *)

Global Ltac wp_op lemma x :=
  first [ simple eapply wp_bind | simple eapply wp_conseq ];
  [ wp_op_nude lemma | wp_intros x ].

Global Ltac wp_op_shadow lemma x :=
  first [ simple eapply wp_bind | simple eapply wp_conseq ];
  [ wp_op_nude lemma | wp_intros_shadow x ].

(* [wp_op_shadow_pair lemma x y] is an ad hoc variant of [wp_op_shadow] that
   should be used when the result of an operation is a pair (x, y). It is
   needed because [clear dependent] does not accept an intropattern as an
   argument, I believe. *)

Ltac wp_op_shadow_pair lemma x y :=
  let p := fresh in
  first [ simple eapply wp_bind | simple eapply wp_conseq ];
  [ wp_op_nude lemma
  | wp_intros p;
    clear dependent x; clear dependent y;
    destruct p as [x y] ].

(* To see example uses of the above tactics, look at the definitions
   of the tactics [wp_get] and [wp_set] in array.v. *)

(* -------------------------------------------------------------------------- *)

(* [wp_last H] renames the most recently introduced hypothesis [H]. *)

(* The tactics [wp_intros] and [wp_intros_shadow] do not allow naming the
   hypotheses that they introduce. In case there is only one such
   hypothesis, [wp_last] allows renaming it after the fact. *)

Ltac wp_last H :=
  match goal with h: _ |- _ =>
    rename h into H
  end.
