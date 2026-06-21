# To Do

## CHANGES

* Mention the new file `olt.v`.
* Mention the new file `traverse.v`.
* Mention the new file `list.v`.

## Documentation

* Document `darray`.

* Document `iter_up_cps` and `iter_down_cps`.

## Bugs

* `wp.v` should not use `autorewrite with z clength app_assoc`;
  this introduces a surprising dependency on `listz`.

## Iteration

* In DFS-CPS, use `foreach_cps` functions on the start vertices and on the
  successors of each vertex.

* In `HITER`, should `body` be allowed to depend on `history`?
  This should allow the exceptional postcondition to vary at each
  loop iteration. But perhaps this is not useful.

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

* Extend the documentation with a section on DFS.

## Traverse

* Instead of making the state a pair `(m, u)`,
  we could make it just `u` and assume that
  there is a way of getting/setting marks.
  This would remove a level of indirection when `u` itself
  needs to be a tuple (or when `u` is unit).
  Also, perhaps this would open the way to an optional 3-color scheme.
  The hook would have to prove that it preserves the Boolean view
  of the marks (grey → black allowed).
  Also, this should allow numbering vertices in discovery order
  and using the numbers as marks.
  Also, this should lead us to more general code where the vertices
  are not necessarily numbers in [0, n).

* In `traverse` and `traverse_cps`, the user does not have access
  to the marks array during the traversal. (In `traverse`, the user
  has access to it at the end; in `traverse_cps`, not at all.) This
  can probably be fixed.

* Recreate the "beautiful hack" that allows us to not test whether
  a vertex is out of bounds?
  If we do not recreate this hack then we can use `make`
  instead of `init` to allocate the array of marks.

* Define a function that detects the existence of a cycle.
  This requires more physical state (another array to keep
  track of grey vertices? or a three-color scheme?).
  This probably requires proving that every edge is examined
  and causes either an `Enter` event or a `Rediscover` event.
  Use the interruptible DFS, so we can stop at the first cycle.

* Prove that if the graph is acyclic then, when a vertex is exited,
  all of its descendants are marked already. (Topological property.)
  The user should be allowed to exploit this property.
  This is true also if there is a cycle detection mechanism
  (then, no need to assume absence of cycles).

* `group` and Kosaraju: ideally we should be able to prove that each
  group forms a strongly connected component *on the fly*, not just
  once the traversal is finished. Also, one might to prove that the
  components are produced in topological order.

* Kosaraju: currently the algorithm is not interactive. Can we define and
  verify an interactive version, where the components are produced one by one
  (in topological order) and immediately submitted to a consumer?

* Test whether depth-first search can be executed inside Rocq.

* Extend the documentation with sections on `wp_cps` and `wpd`.
  Document the loops in CPS style.

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
* Sparse sets in the style of [Briggs and Torczon](https://dl.acm.org/doi/pdf/10.1145/176454.176484).
  See also Cristiá and Dubois, JFLA 2024.
  Inside an array OR vector.
* Union-find inside an array or vector.
* First-order unification.
* Depth-first search, SCCs, Dijkstra, and other graph algorithms.
  Number vertices from `0` to `n-1` and use arrays everywhere.
* Algorithms from `fix`.
* Congruence closure.

## Open Ideas

* Would it be possible, and make sense, to axiomatize the OCaml library
  `Store` in Rocq?
