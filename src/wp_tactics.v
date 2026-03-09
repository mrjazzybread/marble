From array Require Import tactics list_extra wp.

(* [wp_intros x] introduces [x] and a hypothesis [Hx] and simplifies this
   hypothesis. It is typically used in the second subgoal of [wp_bind] and
   [wp_conseq]. *)

Global Ltac wp_intros x :=
  (* Eliminate a beta redex, if there is one. *)
  cbv beta;
  let Hx := fresh in
  intros x Hx;
  (* Simplify expressions that involve lists. *)
  list in Hx;
  (* Decompose existential quantifiers and conjunctions. *)
  unpack in Hx.

(* [wp_intros x] first invokes [wp_intros x'], where [x'] is fresh,
   then forgets everything about [x] and renames [x'] into [x]. It
   should (must) be used when [x'] represents a new array that has
   been obtained by updating the array [x], or more generally,
   a new mutable data structure that has been obtained by updating
   the data structure [x]. This helps keep the goal readable and
   ensures mutable data structures are used linearly. *)

Global Ltac wp_intros_overwrite x :=
  let x' := fresh in
  wp_intros x';
  clear dependent x;
  rename x' into x.

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

(* [wp_loop lemma I] applies the lemma [lemma], which is typically a
   reasoning rule for a loop, with the invariant (inv := I).
   It is essentially a special case of [wp_op_nude] where we want to
   specialize the lemma. *)

Ltac wp_loop lemma I :=
  (* Apply the reasoning rule for this operation. We infer the type [S]
     from the type of the invariant [I]. *)
  match type of I with ?P -> ?S -> Prop =>
  simple eapply (@lemma S) with (inv := I);
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
  tc
  end.

(* [wp_op lemma x] applies either [wp_bind] or [wp_conseq], then applies
   the lemma [lemma] in the first subgoal and introduces the result under
   the name [x] in the second subgoal. The goal should have the form
   [wp (op ...) Q] or [wp (do x ← op ... ; ...) Q]. *)

(* [wp_op_overwrite lemma x] is identical, except it uses
   [wp_intros_overwrite x] instead of [wp_intros x]. *)

Global Ltac wp_op lemma x :=
  (* If several [bind]s are nested, normalize them. *)
  repeat rewrite bind_bind;
  first [ simple eapply wp_bind | simple eapply wp_conseq ];
  [ wp_op_nude lemma | wp_intros x ].

Global Ltac wp_op_overwrite lemma x :=
  (* If several [bind]s are nested, normalize them. *)
  repeat rewrite bind_bind;
  first [ simple eapply wp_bind | simple eapply wp_conseq ];
  [ wp_op_nude lemma | wp_intros_overwrite x ].

(* To see example uses of the above tactics, look at the definitions
   of the tactics [wp_get] and [wp_set] in array.v. *)
