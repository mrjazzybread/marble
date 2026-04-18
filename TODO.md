# To Do

## Loops

* Can we prove an equality between `iter_up` and `iter_up_unrolled`?
  This would allow deciding a posteriori whether unrolling is desired.

## Arrays

* Find out why `sort` is still 2x slower (in OCaml code) than `Array.sort`.
  Is the cost at the leaves too high?

* Many operations on arrays should also work on array segments.
  + `segment_find_index`
  + `segment_exist`
  + `segment_for_all`

* Missing functions:
  + a variant of `init` that carries a state
  + `map`
  + `compare`

## Vectors

* Refactor the code to offer unboxed vectors, where the components
  `n` and `a` are separately maintained by the user. Thus the user
  can call `get` and `set` without allocating new pairs. Use this
  API in `pqueue`.

## Rocq Technique

* Once released (Rocq 9.2?), use `autorewrite*`

* The proof of `pqueue.move_down` is slow, perhaps due to conversion
  problems with machine integers.

* Why is `of_to_Z` an axiom in Rocq's stdlib?

# OCaml Extraction

* Why does extraction sometimes change `if` to `match`?

* Are `let` constructs preserved through extraction?
  Check that no serious computation is duplicated.

* Set up extraction in a clean way (via `dune`?)
  so that the OCaml extracted code is neatly packaged.

* Offer a choice between unsafe, defensive, and persistent arrays
  at extraction time.

* Optionally cheat by using unverified versions of `blit`.

* Do Rocq's default persistent arrays have good behavior
  in the presence of a large number of updates?
  One should copy the whole array from time to time
  so that the cost of switching between versions remains bounded.
  Test, and implement a new PArray module, if needed.

## Partial Evaluation / Specialization

* Can the extracted code be improved?
  + Specialize of higher-order functions (e.g., loops)
  + Inline all small functions
  + Inline (not necessarily small) functions where useful
  + Eliminate useless parameters (e.g., loop-carried state of type `unit`)
  + Unroll loops
  Attempting to derive an improved version by using `Derive`
  and metavariables seems extremely difficult. Exercise:
  first define an improved version of `find_index`,
  then prove that it is equivalent to `find_index`.
  If successful then try to derive this code systematically.

## Documentation

* Complete the documentation (see TODOs there).

* Explain the linear use discipline.

  While iterating on a collection (`array.iteri`, `vector.iteri`)
  one must not modify the collection (i.e., the state must not
  contain the array itself). [One could enforce this in a tactic
  by clearing `isArray a xs` in the subgoal that establishes the
  initial state.]

* Explain the need to avoid aliasing. Aliasing of arrays is permitted
  only in the case where both arrays are only read.

  Avoiding aliasing is
  necessary in order to ensure that the code always accesses the most
  recent version of the array, with time complexity O(1). If the same
  array was used as the source array and as the destination array in a
  call to [isortto] then every array access would become expensive, if a
  persistent array is used, or would fail, if a defensive non-persistent
  array is used (in OCaml).

## Future Applications

* Hash sets, hash maps.
* HAMTs.
* B-Trees.
* Chunked sequences.
* Doubly-linked list (permutation) inside an array or vector.
* Union-find inside an array or vector.
* Depth-first search, SCCs and other graph algorithms.
  Number vertices from `0` to `n-1` and use arrays everywhere.
* Algorithms from `fix`.
* Congruence closure.

## Open Ideas

* Would it be possible, and make sense, to axiomatize the OCaml library
  `Store` in Rocq?
