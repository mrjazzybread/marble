(* Hints that use [lia] in a fine-grained way. *)

(* In the case of disjunction and existential quantification, applying a
   left injection or a right injection is incomplete; we must try [lia],
   which may succeed. Furthermore, in the case of conjunction and *)

Hint Extern 1 (_ ∨ _) => lia : marble.
Hint Extern 1 (_ ∧ _) => lia : marble.
Hint Extern 1 (¬ _ )  => lia : marble.

(* To handle negation, one might wish to instruct [eauto] to unfold
   [not] and to invoke [lia] when the goal is [False]. In practice,
   this does not seem to work well *)

Hint Unfold not : marble.
Hint Extern 1 (False) => lia : marble.

(* Recognize the arithmetic comparison operators on Z. *)

Hint Extern 1 (@eq Z _ _) => lia : marble.
Hint Extern 1 (Z.lt _ _)  => lia : marble.
Hint Extern 1 (Z.le _ _)  => lia : marble.
Hint Extern 1 (Z.gt _ _)  => lia : marble.
Hint Extern 1 (Z.ge _ _)  => lia : marble.
