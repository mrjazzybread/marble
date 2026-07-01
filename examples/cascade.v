(******************************************************************************)
(*                                                                            *)
(*                                  Marble                                    *)
(*                                                                            *)
(*                       François Pottier, Inria Paris                        *)
(*                                                                            *)
(*       Copyright 2026--2026 Inria. All rights reserved. This file is        *)
(*       distributed under the terms of the GNU Library General Public        *)
(*       License, with an exception, as described in the file LICENSE.        *)
(*                                                                            *)
(******************************************************************************)

From stdpp Require Import list.
From listz Require Import listz.
(* TODO for some reason, {[x]} is not opaque *)
Opaque singleton.
From marble Require Import tactics wp iteration cascade.

Unset Universe Minimization ToSet.
Generalizable All Variables.
Set Universe Polymorphism.

(* This file offers examples of iterating on a tree, in several styles,
   including fold in direct style, fold in CPS style, and cascades. *)

(* -------------------------------------------------------------------------- *)

(* A type of trees. *)

Inductive tree (A : Type) :=
| Leaf : tree A
| Node : tree A → A → tree A → tree A.

Arguments Leaf {A}.
Arguments Node {A}.

(* The fringe of a tree. *)

Fixpoint fringe {A} (t : tree A) :=
  match t with
  | Leaf => []
  | Node l x r => fringe l ++ {[x]} ++ fringe r
  end.

(* Iterating on a tree in direct style. *)

Fixpoint fold {S A} (consume : S → A → S) (s : S) (t : tree A) : S :=
  match t with
  | Leaf =>
      s
  | Node l x r =>
      do s ← fold consume s l ;
      do s ← consume s x ;
      do s ← fold consume s r ;
      s
  end.

(* Iterating on a tree in CPS style. *)

Fixpoint fold_cps {S A R} (consume : S → A → CPS R S) (s : S) (t : tree A) : CPS R S :=
  λ (k : S → R),
  match t with
  | Leaf =>
      k s
  | Node l x r =>
      fold_cps consume s l @@ λ s,
      consume s x @@ λ s,
      fold_cps consume s r @@ λ s,
      k s
  end.

(* -------------------------------------------------------------------------- *)

(* The specification of [fold]. *)

Lemma wp_fold {S A} (consume : S → A → S) :
  ∀ t past,
  ITER_LIST
    past (past ++ fringe t)
    (λ _ x s Q, wp (consume s x) Q)
    (λ s Q, wp (fold consume s t) Q).
Proof.
  expand_ITER.
  induction t as [| l IHl x r IHr ]; intro past; ITER; simpl fold.
  { list. wp_ret. }
  { wp_op IHl shadowing: s.
    { tc. }
    wp_op Hbody shadowing: s.
    { complete in *. subst. tc. }
    { complete in *. subst. tc. }
    wp_op IHr shadowing: s.
    { complete in *. subst. list. tc. }
    wp_ret.
    { complete in *. subst. list in *. tc. }
  }
Qed.

(* The specification of [fold_cps]. *)

Lemma wp_fold_cps {R S A} (consume : S → A → CPS R S) (ψ : list A → R → Prop) :
  ∀ t past,
  ITER_LIST
    past (past ++ fringe t)
    (λ history x s Q, wp_gcps (consume s x) Q (ψ (history ++ {[x]})) (ψ history))
    (λ s Q, wp_gcps (fold_cps consume s t) Q (ψ (past ++ fringe t)) (ψ past)).
Proof.
  expand_ITER.
  induction t as [| l IHl x r IHr ]; intro past; ITER; simpl fold_cps.
  { list. eapply wp_gcps_ret. tc. }
  { eapply wp_gcps_bind.
    { eapply IHl; tc. }
    clear dependent s. cbv beta. intros s Hs.
    unpack in Hs. complete in *. subst.
    eapply wp_gcps_bind.
    { eapply Hbody; tc. }
    clear dependent s. cbv beta. intros s Hs.
    eapply wp_gcps_bind.
    { eapply IHr; tc7. }
    clear dependent s. cbv beta. intros s Hs.
    unpack in Hs. subst.
    simpl fringe. list in *.
    eapply wp_gcps_ret.
    { tc. }
  }
Qed.
