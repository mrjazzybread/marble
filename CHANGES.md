# Changes

## 2026/XX/XX

* New file `darray`, offering a type of arrays whose default value is tracked.
  This type (and its reasoning rules) can be useful when a proof of termination
  requires keeping track of the default value of an array.

* In `equations`:
  + New lemma `IFC_if_dep`.
  + Change the tactic `by dependent induction on x Ax` to introduce
    the three hypotheses `x`, `Achild`, `IH`.

* In `bool`:
  + New lemma `isBool_trivial`.
  + Remove the lemma `isBool1_variance`, which was a duplicate of `isBool1_conseq`.

* In `int`:
  + New instance `isInt_mod`.
  + New functions `iter_up_cps`, `iter_down_cps`.
  + The functions `xiter_up`, `xiter_down`, `uxiter_up`, `uxiter_down`
    have been removed.

* In `iteration`:
  + New definition `HITER`,
    a specialized version of `ITER`
    where the producer state is a history,
    that is, a list of the elements produced so far.
  + New definitions `ITER_SET` and `ITER_SET_UNIQUE`,
    where the producer state is a set,
    as well as their variants `ITER_SET'` and `ITER_SET_UNIQUE'`,
    where the producer state is a list.
    A proof of equivalence is provided in `misc.v`.
  + Modified definition of `ITER`.
    The definition now includes the requirement for the user invariant `inv`
    to be compatible with a notion of equality on producer states.
  + The specifications `XITER` and `UXITER` have been removed.
    Higher-order iteration functions in CPS style are now preferred.
  + `ITERI_LIST` has been removed.
    It is now a special case of `ITER_LIST`.

* In `wp`:
  + New tactic `wp_destruct_post`.
  + New notation `exist`.
    Beware of the potential confusion with the function `array.exist`.
  + New lemmas `bind_eq_dep` and `bind_eq_dep_dep`.
  + New lemma `wp_exist`.
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
