# Changes

## 2026/XX/XX

* In `bool`:
  + New lemma `isBool_trivial`.

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
  + In the lemma `wp_make`, reveal `default a = x`.
  + In the lemma `wp_init`, reveal `default a = inhabitant`.
    Make `ψ` the first parameter.

* Resurrected the theory of directed graphs and depth-first search that appars
  in the paper [Depth-first search and strong connectivity in
  Coq](https://cambium.inria.fr/~fpottier/publis/fpottier-dfs-scc.pdf).

## 2026/04/21

* First release.
