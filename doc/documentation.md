# Marble

[[_TOC_]]

## Arrays

An array should be viewed as an abstract data structure, which holds
a sequence of elements.

The proposition [`isArray a xs`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L103) means
that the elements of the array `a` form the list `xs`. This
proposition allows reasoning about the content of the array; it
appears in the specification of every operation on arrays. This
proposition is in fact equivalent to `to_list a = xs`
([lemma](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L513));
nevertheless it is recommended to always prefer writing `isArray a xs`
and to treat this proposition as abstract.

### Primitive Operations

There are four primitive operations on arrays:

* `make _n x` ([specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L301))
  creates a new array of length `_n`
  where every slot is filled with the value `x`.
  The parameter `_n`, a machine integer,
  must not exceed `max_array_length`.

  To reason about this operation,
  use the tactic [`wp_make a`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L374),
  where `a` is the name under which you would like
  the newly allocated array to be known in the proof.

* `length a` ([specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L350))
  returns the length of the array `a`.

  To reason about this operation,
  use the tactic [`wp_length n`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L363),
  where `n` is the name under you would like the length
  of this array to be known in the proof.

* `get a _i` ([specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L314))
  returns the element stored at index `_i` in the array `a`.

  To reason about this operation,
  use the tactic [`wp_get x`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L366),
  where `x` is the name under you would like this element
  to be known in the proof.

* `set a _i x` ([specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L326))
  stores the element `x` at index `_i` in the array `a`.
  It returns an updated array.
  Thereafter, the previous array should no longer be used.
  It is recommended to name the new array also `a` so as to reduce
  the risk of accessing the previous array by mistake.

  To reason about this operation,
  use the tactic [`wp_set`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L369).
  This tactic intentionally clears the previous array `a`
  and names the new array `a` in the proof.

### More Operations

* [`segment_to_list a _i _k`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L408)
  [(specification)](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L431)
  converts the array segment determined by the array `a`
  and the start and end indices `_i` and `_k` into a list.

* [`to_list a`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L417)
  [(specification)](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L453)
  converts the array `a` into a list.

  For this operation,
  we provide [a second specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L474).
  This specification is unusual in that it does not require `isArray a _`
  as a precondition: on the contrary, its postcondition indicates that
  it returns a list `xs` such that `isArray a xs` holds.
  This allows obtaining a proposition of the form `isArray a xs`
  about an array of arbitrary provenance.

  In a related vein, the lemma [`isArray_iff`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L513)
  establishes that `isArray a xs` is equivalent to `to_list a = xs`.

* [`of_list xs`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L743)
  [(specification)](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L757)
  converts the list `xs` to an array.

  This operation requires `len xs ≤ max_array_length`: that is, the
  length of the list `xs` must not exceed `max_array_length`.

  The lemma [`to_list_of_list`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L785)
  states that converting a list to an array, then back to a list,
  is the identity.

  The reverse round-trip property (which would state that converting
  an array to a list, then back to an array, is the identity)
  [is not true](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L822),
  because an array is defined not only by its content
  but also by its default value.

* [`init _n @@ body`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1950)
  ([specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1956))
  creates an array of length `_n` whose elements
  are computed by the function `body`.

  At each iteration, the loop body `body : int → A`
  receives the current index `_i` and returns an element.

  To reason about this operation,
  use the tactic [`wp_init`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1976).

* [`list_length xs`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L704)
  ([specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L712))
  returns the length of the list `xs` as a machine integer.

  Although this is not an operation on arrays, it can be useful.
  It is used in the implementation of `of_list`.

* [`list_iteri _i xs s @@ body`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L542)
  ([specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L569))
  is a loop on the list `xs`, with initial index `_i` and initial state `s`.
  At each iteration, the loop body `body : S → int → A → S`
  receives the current state `s`, the current index `_i`,
  and the current list element `x`, and returns a new state.

  Although this is not an operation on arrays, it can be useful.
  It is used in the implementation of `of_list`.

* [`blit a _i b _j _n`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L903)
  [(specification)](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1138)
  copies the array segment determined by the array `a`,
  the start index `_i`, and the length `_n`
  to the array segment determined by the array `b`,
  the start index `_j`, and the length `_n`.
  It returns an updated version of the array `b`.

  The arrays `a` and `b` must not be aliased: that is, they should be
  two *independent* arrays. To move data within a single array, use
  `blit'`.

  To reason about this operation,
  use the tactic [`wp_blit`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1371).
  This tactic intentionally clears the previous array `b`
  and names the new array `b` in the proof.

* [`blit' a _i _j _n`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1305)
  [(specification)](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1325)
  copies the array segment determined by the array `a`,
  the start index `_i`, and the length `_n`
  to the array segment determined by the array `a`,
  the start index `_j`, and the length `_n`.
  It returns an updated version of the array `a`.
  Thus, the array `a` is both read and written.
  The source and destination segments may overlap.

  To reason about this operation,
  use the tactic [`wp_blit`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1371).
  This tactic intentionally clears the previous array `a`
  and names the new array `a` in the proof.

* [`copy a`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1390)
  [(specification)](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1397)
  creates a fresh copy of the array `a`,
  that is, a new array whose content
  is the same as the content of the array `a`.

  To reason about this operation,
  use the tactic [`wp_copy b`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1409)
  where `b` is the name under which you would like
  the new array to be known.

* [`sub a _i _n`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1423)
  [(specification)](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1429)
  creates a new array whose content
  is the same as the content of the array segment
  determined by the array `a`, the start index `_i`,
  and the length `_n`.

  To reason about this operation,
  use the tactic [`wp_sub b`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1443)
  where `b` is the name under which you would like
  the new array to be known.

* [`append a b`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1460)
  [(specification)](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1472)
  creates a new array whose content is the concatenation
  of the content of the arrays `a` and `b`.

  To reason about this operation,
  use the tactic [`wp_append c`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1488)
  where `c` is the name under which you would like
  the new array to be known.

* [`fill a _i _n x`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1505)
  [(specification)](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1514)
  fills the array segment determined by the array `a`,
  the start index `_i`, and the length `_n`
  with the value `x`.
  It returns an updated version of the array `a`.

  To reason about this operation,
  use the tactic [`wp_fill`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1539).
  This tactic intentionally clears the previous array `a`
  and names the new array `a` in the proof.

* [`find_index f a`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1559)
  [(specification)](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1595)
  searches the array `a`, from left to right,
  for an element `x` such that `f x` is true.
  Its result has type [`outcome int`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/iteration.v?ref_type=heads#L39).

  To reason about this operation,
  use the tactic [`wp_find_index out`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1657)
  where `out` is the name under which you would like
  the result to be known.

* [`exist f a`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1671)
  [(specification)](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1684)
  searches the array `a`, from left to right,
  for an element `x` such that `f x` is true.
  Its result is `true` if such an element exists
  and `false` otherwise.

  To reason about this operation,
  use the tactic [`wp_exist b`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1700)
  where `b` is the name under which you would like
  the result to be known.

* [`for_all f a`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1716)
  [(specification)](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1729)
  tests whether every element `x` of the array `a`
  is such that `f x` is true.
  If so, its result is `true`;
  otherwise, its result is `false`.

  To reason about this operation,
  use the tactic [`wp_for_all b`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1745)
  where `b` is the name under which you would like
  the result to be known.

* [`equal eq a b`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1764)
  ([specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1808))
  tests whether the arrays `a` and `b` have the same length
  and have equal elements at every index `i`.
  The function `eq` is used to check two elements for equality.

  A [simpler specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1808) is given
  in the case where the function `eq` is an equality test.

* [`segment_iteri a _i _k s @@ body`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1886)
  ([specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1898))
  is a loop over the array segment determined by the array `a`,
  start index `_i`, and end index `_k`,
  with initial state `s`.

  At each iteration, the loop body `body : S → int → A → S`
  receives the current state `s`, the current index `_i`,
  and the current list element `x`, and returns a new state.

* [`iteri a s @@ body`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1892)
  ([specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1916))
  is a loop over the array `a`
  with initial state `s`.

  At each iteration, the loop body `body : S → int → A → S`
  receives the current state `s`, the current index `_i`,
  and the current list element `x`, and returns a new state.

### Tactics

The tactic [`isArray`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L384) is applicable when the
goal has the form `isArray a ys` and there is a hypothesis of the form
`isArray a xs`. The goal is then reduced to the equation `xs = ys` and
this equation is simplified. If the equation is found to be true then
the goal is solved.

The tactic [`arrays`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L146) looks for every hypothesis
of the form `isArray a xs` and introduces the fact `representable (len
xs)`. This fact is then possibly simplified (in cases where `xs` is a
complex expression). Using this tactic at the beginning of a proof can
help preserve information about the fact that certain integers are
representable. This information could otherwise become obscured as the
array `a` is updated and the assertion `isArray a _` becomes more
complex.
