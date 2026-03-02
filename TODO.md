# To Do

## Short term

* Maybe `isInt` and `representable` should be type classes
  so we can use type class search instead
  of `eauto with int representable`.

* Seal `isBool` and other similar assertions.

* `find_index_inv` and `equal_inv` could be instances of `isOption`.
  Develop `isOption`, extend `wp_if` to handle it.

* In `find_index`, `exist`, `for_all`, `equal`,
  the user-provided function `f`
  should perhaps receive a spec involving `reflects`.

* Tactics:
  + decrease the amount of boilerplate required by `wp` tactics
  + automate the search for a specification
  + every (user) function that modifies an array should be
    accompanied by a tactic that performs clear-and-rename

* Missing functions:
  + `init` on lists and arrays
  + `map`
  + `equal`
  + `compare`
  + `merge`
  + `sort`
  + `fold_left`, `fold_left2`?

# OCaml Extraction

* Set up extraction to use defensive, non-persistent arrays.
  + Can offer more than just the 4 primitive operations,
    e.g., `blit` should use OCaml's `Array.blit`.
  + Safety in the face of concurrent usage requires CAS or a lock.
  + A straightforward approach involves an option on an array,
    but it is possible to get rid of the option by using an empty array
    and by relying the bounds checks. (The failure message will be less clear.)

* Can the extracted code be improved?
  + Specialization of higher-order functions (e.g., loops)
  + Inlining
  + Elimination of useless parameters (e.g., loop-carried state of type `unit`)
  Attempting to derive an improved version by using `Derive`
  and metavariables seems extremely difficult. Exercise:
  first define an improved version of `find_index`,
  then prove that it is equivalent to `find_index`.
  If successful then try to derive this code systematically.

## Running inside Rocq

* Find out why `compute` is unable to execute `down_aux`.

* Find out how to enable `native_compute`.
