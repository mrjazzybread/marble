# Changes

## 2026/XX/XX

* In `equations`:
  + New lemma `IFC_if_dep`.

* In `bool`:
  + New lemma `isBool_trivial`.
  + Remove the lemma `isBool1_variance`, which was a duplicate of `isBool1_conseq`.

* In `int`:
  + New instance `isInt_mod`.

* In `iteration`:
  + New definitions `ITER_SET` and `ITER_SET_UNIQUE`.
  + Modified definition of `ITER`.
    The definition now includes the requirement for the user invariant `inv`
    to be compatible with a notion of equality on producer states.

* In `wp`:
  + New lemmas `bind_eq_dep` and `bind_eq_dep_dep`.
  + New judgement `wpd` together with a set of reasoning rules.
  + New tactic `prove_Proper`.
  + The tactic `wp_loop_precondition_hook` now calls `prove_Proper`
    so as to automatically prove that the loop invariant is compatible
    with equality of producer states (if this is easy to prove).

* In `arrays`:
  + New lemma `isArray_to_list`.
  + New lemma `ltb_length_spec`.
  + New lemma `get_spec`.
  + New lemma `set_spec`.
  + New function `sum_with`.
  + New lemma `wp_sum_with`.
  + New lemma `sum_with_spec`.
  + New lemma `wp_make_default`.
  + New lemma `wp_set_default`.
  + New lemma `wp_init_default`.
  + New lemma `default_init`.
  + In the lemma `wp_init`, make `ψ` the first parameter.
    Allow `f` to rely on the hypothesis `0 ≤ i < n`.

* Resurrected the theory of directed graphs and depth-first search that appars
  in the paper [Depth-first search and strong connectivity in
  Coq](https://cambium.inria.fr/~fpottier/publis/fpottier-dfs-scc.pdf).

## 2026/04/21

* First release.
