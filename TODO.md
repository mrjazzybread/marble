# To Do

## Short term

* `isInt 12 12` still does not work. Ask for help on Zulip.

* Apply the generic loop spec to `list_iteri_aux` and `list_iteri`.

* Generalize the generic loop spec to allow non-determinism.
  (The final producer state should be identified by a predicate `complete`.)

* Define generic concepts so as to shorten the specifications of loops.
  Do so for non-interruptible and interruptible loops.

* In anticipation of vectors, many operations on arrays should also
  work on a segment of a larger array.
  + `segment_find_index`
  + `segment_exist`
  + `segment_for_all`

* Should `find_index_inv` and `equal_inv` be instances of `isOption`?
  Develop `isOption`, and extend `wp_if` to handle it?

* Tactics:
  + automate the search for a specification
  + every (user) function that modifies an array should be
    accompanied by a tactic that performs clear-and-rename

* Missing functions on integers:
  + `interruptible_down`
  + `interruptible_down_unit`

* Missing functions on arrays:
  + `init` on lists and arrays
  + `map`
  + `compare`
  + `merge`
  + `sort`

* More lemmas should be marked `Local`.

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

## Running inside Rocq

* Find out why `compute` is unable to execute `down_aux`.

* Find out how to enable `native_compute`.

## Documentation

* Explain the linear use discipline.

  While iterating on a collection (`array.iteri`, `vector.iteri`)
  one must not modify the collection (i.e., the state must not
  contain the array itself). [One could enforce this in a tactic
  by clearing `isArray a xs` in the subgoal that establishes the
  initial state.]

* Explain the various extraction options.

## Applications.

* Vectors.
* Hash sets, hash maps.
* HAMTs.
* B-Trees.
* Chunked sequences.

* Ephemeral? Persistent? Transient?
  Can we have efficient transient chunks?
