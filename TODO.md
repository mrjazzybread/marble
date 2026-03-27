# To Do

## Short term

* array.v: some operations do not have a dedicated tactic.
  Define dedicated tactics or indicate what tactic to use,
  e.g. `wp_loop`.

* Plug the `sortto_segment` functions into merge sort,
  instead of insertion sort.
  Can we get rid of insertion sort entirely?
  May need to generalize the spec of `sortto_segment`
  to cover the case of two arrays.

* Offer a public `merge` function, with and without stability.

* `sort.v`: try to use uniform conventions regarding names and order
   of parameters; also, regarding end offset versus length.

* Instead of using insertion sort at the leaves, stick to merge sort
  all the way?

* Can the loops in `int.v` use `IF/THEN/ELSE` instead of `inspected`?

* `isInt 12 12` still does not work. Ask for help on Zulip.

* In anticipation of vectors, many operations on arrays should also
  work on array segments.
  + `segment_find_index`
  + `segment_exist`
  + `segment_for_all`

* Tactics:
  + automate the search for a specification
  + every (user) function that modifies an array should be
    accompanied by a tactic that performs clear-and-rename

* Missing functions on arrays:
  + `init` on lists and arrays
  + `map`
  + `compare`
  + `merge`

* Offer a generic way of obtaining a 2-way
  comparison out of a 3-way comparison?

* More lemmas should be marked `Local`.

* Once released (Rocq 9.2?), use `autorewrite*`.

# OCaml Extraction

* Set up extraction to use defensive, non-persistent arrays.
  + Can offer more than just the 4 primitive operations,
    e.g., `blit` should use OCaml's `Array.blit`.
  + Safety in the face of concurrent usage requires CAS or a lock.
  + A straightforward approach involves an option on an array,
    but it is possible to get rid of the option by using an empty array
    and by relying the bounds checks. (The failure message will be less clear.)

* Also set up extraction to use persistent arrays
  and to use ordinary (non-persistent, non-defensive) arrays.
  Benchmark.

* Do Rocq's default persistent arrays have good behavior
  in the presence of a large number of updates?
  One should copy the whole array from time to time
  so that the cost of reverting to an old version remains bounded.
  Test, and implement a new PArray module, if needed.

## Partial Evaluation / Specialization

* Can the extracted code be improved?
  + Specialization of higher-order functions (e.g., loops)
  + Inline all small functions
  + Inline (not necessarily small) functions where useful
  + Elimination of useless parameters (e.g., loop-carried state of type `unit`)
  Attempting to derive an improved version by using `Derive`
  and metavariables seems extremely difficult. Exercise:
  first define an improved version of `find_index`,
  then prove that it is equivalent to `find_index`.
  If successful then try to derive this code systematically.

* In insertion sort and/or merge sort, define specialized versions
  for the base cases where the length is statically known.
  Test and benchmark to find the best strategy at the leaves
  and the best cutoff value.

## Running inside Rocq

* Find out why `compute` is unable to execute `down_aux`.

* Find out how to enable `native_compute`.

## Documentation

* Document the public API.

* Explain the linear use discipline.

  While iterating on a collection (`array.iteri`, `vector.iteri`)
  one must not modify the collection (i.e., the state must not
  contain the array itself). [One could enforce this in a tactic
  by clearing `isArray a xs` in the subgoal that establishes the
  initial state.]

* Explain the need to avoid aliasing. Aliasing of arrays is permitted
  only in the case where both arrays are only read.

  necessary in order to ensure that the code always accesses the most
  recent version of the array, with time complexity O(1). If the same
  array was used as the source array and as the destination array in a
  call to [isortto] then every array access would become expensive, if a
  persistent array is used, or would fail, if a defensive non-persistent
  array is used (in OCaml).

* Explain the various extraction options.

## Applications.

* Vectors.
* Hash sets, hash maps.
* HAMTs.
* B-Trees.
* Chunked sequences.
* Priority queue within an array.
* Depth-first search, SCCs and other graph algorithms.
* Congruence closure.

* Ephemeral? Persistent? Transient?
  Can we have efficient transient chunks?
