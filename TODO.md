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
