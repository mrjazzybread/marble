# To Do

## CHANGES

* Mention the new file `olt.v`.
* Mention the new file `traverse.v`.

## Bugs

* `wp.v` should not use `autorewrite with z clength app_assoc`;
  this introduces a surprising dependency on `listz`.

## Arrays

* Rocq has `copy` (since when?). Use it.

* `for_all` : inline loop body and inline away `negb`.

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

## Priority Queues

* Verify a loop that extracts and inserts elements into the queue.

## DFS

* Replace ⊤ with a smaller set where needed,
  so we can reason about finite graphs.

* Extend the documentation with a section on DFS.

## Traverse

* Define and verify the toplevel function.
* Should its postcondition mention that a DFS forest has been
  built, and relate this DFS forest with the events that have
  been emitted earlier?

* Define a simplified function where only `Enter` events are
  observed. (Check that the code is simplified.) Prove that it
  enumerates the reachable vertices (in an unspecified order).

* Define an incremental/interruptible variant of DFS,
  as a sequence (cascade) of events.
  (No need for a user state there.)

* Define a function that detects the existence of a cycle.
  This requires more physical state (another array to keep
  track of grey vertices? or a three-color scheme?) and
  possibly a new kind of event (rediscovering a vertex).
  Use the interruptible DFS, so we can stop at the first cycle.

* Extend the documentation with a section on `wpd`.

* Extend the documentation with a section on `traverse`.

## Rocq Technique

* Once released (Rocq 9.2?), use `autorewrite*`

* The proof of `pqueue.move_down` is slow, perhaps due to conversion
  problems with machine integers.

* Why is `of_to_Z` an axiom in Rocq's stdlib?

* Add more axioms to Rocq, e.g., `blit` and `blit'`?

* Build an experimental version of Rocq that uses unsafe defensive
  arrays, and measure its performance.

* Protest against the small magnitude of `max_array_length`.

# OCaml Extraction

* Set up random testing of the library using defensive arrays.

* Why does extraction sometimes change `if` to `match`?

* Are `let` constructs preserved through extraction?
  Check that no serious computation is duplicated.

* We could offer a super-unsafe variant
  where our arrays use `Array.unsafe_get` and `Array.unsafe_set`.

* Our implementations of unsafe arrays and defensive arrays
  should use OCaml's uniform arrays (once they exist).

* Optionally cheat by using unverified versions of `blit`, `fill`,
  or other functions.

* Use verified extraction?

## Partial Evaluation / Specialization

* Can the extracted code be improved?
  + Specialize higher-order functions (e.g., loops)
  + Inline all small functions
  + Inline (not necessarily small) functions where useful
  + Eliminate useless parameters (e.g., loop-carried state of type `unit`)
  + Unroll loops

## Future Applications

* Hash sets, hash maps. Compare with [Diqt](https://github.com/valoran-M/diqt).
* HAMTs.
* B-Trees.
* Chunked sequences.
* Doubly-linked list (permutation) inside an array or vector.
* Union-find inside an array or vector.
* Depth-first search, SCCs, Dijkstra, and other graph algorithms.
  Number vertices from `0` to `n-1` and use arrays everywhere.
* Algorithms from `fix`.
* Congruence closure.

## Open Ideas

* Would it be possible, and make sense, to axiomatize the OCaml library
  `Store` in Rocq?
