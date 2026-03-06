# To Do

## Short term

* `isInt 12 12` still does not work.

* In anticipation of vectors, many operations on arrays should also
  work on a segment of a larger array.
  + `segment_find_index`
  + `segment_exist`
  + `segment_for_all`

* Sjhould `find_index_inv` and `equal_inv` be instances of `isOption`?
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
