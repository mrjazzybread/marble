<!--- THIS FILE HAS BEEN GENERATED based on documentation.md.pre -->
# Marble

[[_TOC_]]

<!--------------------------------------------------------------------------->

## Writing Programs

The code in this library is ordinary Rocq code. It is purely functional.
It uses Rocq's
[primitive arrays](https://rocq-prover.org/doc/master/refman/language/core/primitive.html#primitive-arrays).
They are persistent arrays, whose implementation exploits mutable arrays.
When an array is updated, a new array is returned.
In principle, the previous array still exists and can still be accessed;
in practice, however, for efficiency, it should not be accessed:
[a section of this document](#the-linear-use-discipline) explains why.

Because updating a data structure produces a new data structure,
all code must naturally be written in state-passing style.
We provide the notation [`do x ← e1 ; e2`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/wp.v?ref_type=heads#L37)
to facilitate this. It should typically be used when one thinks
of `e1` as a (possibly complex) *computation* whose result one wants to name `x`.
Rocq's native notation `let x := e1 in e2` can also be used.
It should typically be used when `e1` is a (small) *expression*,
such as an arithmetic expression.

We also provide the notation [`f @@ x`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/wp.v?ref_type=heads#L27)
for function application. This notation allows the parentheses around the
argument `x` to be omitted, even if this argument is a complex expression.
This is very useful when `f` is a higher-order function and `x` itself is a
function: in particular, this leads to a rather nice way of writing
[loops](#iteration-on-machine-integers).

We offer syntactic sugar for two dependent conditional constructs,
[`IFC e0 THEN e1 ELSE e2`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/equations.v?ref_type=heads#L13)
and
[`IF e0 THEN e1 ELSE e2`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/equations.v?ref_type=heads#L16).
These constructs are useful and necessary
when the status of condition `e0`
is needed in a proof of termination,
that is,
when a proof of termination
needs a hypothesis of type `e0 = true` or `e0 = true`.
The definition of [`iter_down`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/loop.v?ref_type=heads#L65)
offers an example of this.

<!--------------------------------------------------------------------------->

## Verifying Programs

To help users write specifications and verify programs, we define a simple
program logic, in the style of Hoare logic.
The judgement [`wp e Q`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/wp.v?ref_type=heads#L83)
means that the expression `e` admits the postcondition `Q`:
that is, result of `e` satisfies the property `Q`.
Naturally, Rocq does not distinguish between a computation and its result:
they are considered equal. Thus, the definition of `wp e Q` is just `Q e`.
Nevertheless, the judgement `wp` is useful: applying its reasoning rules lets
us reason step by step about the behavior of a program.

The basic reasoning rules are
[return](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/wp.v?ref_type=heads#L103),
[sequencing](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/wp.v?ref_type=heads#L115),
[conditional](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/wp.v?ref_type=heads#L90),
and
[consequence](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/wp.v?ref_type=heads#L197).

To apply these reasoning rules, we offer a number of tactics.

The tactic [`wp_ret`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/wp.v?ref_type=heads#L227) should be used when the goal is
`wp e Q` where `e` is a variable or a simple expression,
such as an arithmetic expression. It transforms the goal into `Q e`
and attempts to solve it using the tactic
[`wp_ret_hook`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/wp.v?ref_type=heads#L222), which can be customized.

The tactic [`wp_if`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/wp.v?ref_type=heads#L240) should be used when the goal is
`wp e Q` where `e` is a conditional construct (that is, `if/then/else`
or `IF/THEN/ELSE` or `IFC/THEN/ELSE`). It generates one subgoal for the
Boolean condition (which ideally should be automatically solved) and
one subgoal for each branch.

The tactic [`wp_op`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/wp.v?ref_type=heads#L389) is the main workhorse of
this small tactic library. It should be used when the goal is a function call
or begins with a function call: that is, when the goal is `wp (f y z ...) Q`
or `wp (do x ← f y z ... ; e) Q`. This tactic expects one argument, namely a
lemma that offers a specification of the function `f`. First, it automatically
applies the sequencing rule or the consequence rule (whichever is applicable);
then, it applies the lemma whose name is provided. If this lemma has
hypotheses (which are usually known as preconditions) then it attempts
to solve these subgoals by applying the tactics
[`wp_precondition_primary_hook`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/wp.v?ref_type=heads#L316)
and
[`wp_precondition_secondary_hook`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/wp.v?ref_type=heads#L320),
which can be customized.
It produces two kinds of subgoals:
first, the preconditions that it was not able to solve;
second, the subgoal that represents
the continuation of the operation `f y z ...`.

In the last subgoal of `wp_op <lemma>`,
one typically uses either [`wp_intro x`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/wp.v?ref_type=heads#L269)
or
[`wp_shadow x`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/wp.v?ref_type=heads#L288).

[`wp_intro x`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/wp.v?ref_type=heads#L269)
introduces the result of the operation `f y z ...`
under the name `x`. (`x` can be a variable or a composite pattern.)
It also introduces a hypothesis about `x`,
which represents the postcondition of the operation `f y z ...`,
and uses the tactic [`wp_intro_hook`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/wp.v?ref_type=heads#L260),
which can be customized, to destruct or simplify this postcondition.

[`wp_shadow x`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/wp.v?ref_type=heads#L288)
also introduces the result of the operation `f y z ...`
under the name `x`. (In this case, `x` must be a variable.)
It assumes that there is already a variable named `x`, and
intentionally shadows it: that is, before introducing the new
variable `x`, it uses `clear dependent x`
to forget about the previous variable `x`.
This tactic should be used when the operation `f y z ...`
updates a data structure. This ensures that the previous version
of the data structure cannot be used by mistake: in other words,
this enforces [the linear use discipline](#the-linear-use-discipline).

The tactic `wp_op <lemma> introducing: x`
is sugar for `wp_op <lemma>; last wp_intro x`.

The tactic `wp_op <lemma> shadowing: x`
is sugar for `wp_op <lemma>; last wp_shadow x`.

The tactic `wp_op <lemma> with invariant: I`
is sugar for (roughly) `wp_op <lemma with inv := I>`.
It is useful when invoking a higher-order [iteration](#iteration) function:
it allows providing a *loop invariant*.
At this time,
this form cannot be combined with `introducing:` or `shadowing:`.

A small number of generally useful tactics are provided in the file
(`tactics.v`)[../src/tactics.v]. In particular, the tactic
[`tc`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/tactics.v?ref_type=heads#L74)
and its depth-indexed variants [`tc0` to `tc7`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/tactics.v?ref_type=heads#L65)
perform type class search and can solve arithmetic side conditions
using `lia`. They can be extended
by adding hints (via `Hint Resolve` or `Hint Extern`)
to the hint database `marble`.

<!--------------------------------------------------------------------------->

## Booleans

The most basic conditional construct, `if b then ... else ...`,
involves a Boolean expression `b`. To verify such a construct,
it is desirable to have a standard and convenient way
of relating the Boolean value `b` with the logical proposition `P`
that this value represents.

For this purpose,
we define the type class [`isBool b P Q`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/bool.v?ref_type=heads#L26).
The assertion `isBool b P Q` means that `b = true` implies `P`
and that `b = false` implies `Q`.
We do not require `Q` to be the negation of `P`, that is, `¬P`.
We allow the opposite situation, where `P` is the negation of `Q`,
and we allow `P` and `Q` to be unrelated propositions.
This buys us extra flexibility and (often) lets us avoid
the use of negation, which in Rocq is inconvenient,
because (unless explicitly requested by the user)
the law of the excluded middle is not available.
Because the case where `Q` is `¬P` is still common,
we write `isBool1 b P`
as an abbreviation for `isBool b P (¬P)`.

A hypothesis of the form `isBool b P Q` appears in the statement of the
reasoning rule [`wp_if`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/wp.v?ref_type=heads#L90), so (provided suitable instances of
the type class `isBool` are available) the tactic `wp_if` automatically
transforms a Boolean condition into the logical proposition that it
represents.

We provide instances of the type class `isBool` for the most common logical
connectives:
[conjunction](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/bool.v?ref_type=heads#L78),
[disjunction](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/bool.v?ref_type=heads#L86),
and
[negation](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/bool.v?ref_type=heads#L94).

We also provide instances of the type class `isBool`
for the primitive comparison operations
on [machine integers](#machine-integers).
Some of these instances have side conditions:
for example, [`isBool_ltb`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/int.v?ref_type=heads#L392),
which concerns a comparison between two machine integers `_i` and `_j`,
has the side conditions `unsigned i` and `unsigned j`.
Thus, when the tactic `wp_if` leaves an unsolved subgoal of the form
`isBool (_i <? _j)%uint63 ?P ?Q`, very likely,
this means that the tactic `tc` was unable to prove
one or both of the subgoals `unsigned i` and `unsigned j`.
In such an event, adding hypotheses about `i` or `j` may be necessary.

<!--------------------------------------------------------------------------->

## Machine Integers

Rocq's
[primitive arrays](https://rocq-prover.org/doc/master/refman/language/core/primitive.html#primitive-arrays)
are indexed with
[primitive integers](https://rocq-prover.org/doc/master/refman/language/core/primitive.html#primitive-integers).
We also refer to them as *machine integers*.
They are unsigned 63-bit integers.
They are axiomatized in the standard library modules
[`Uint63`](https://rocq-prover.org/doc/v9.1/stdlib/Stdlib.Numbers.Cyclic.Int63.Uint63.html)
and
[`Uint63Axioms`](https://rocq-prover.org/doc/V9.0.1/corelib/Corelib.Numbers.Cyclic.Int63.Uint63Axioms.html).

Although we write code where machine integers are used,
while reasoning about this code,
we usually prefer to think in terms of ideal integers.
Therefore, we establish a connection between machine integers
and ideal integers, by defining the type class
[`isInt _i i`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/int.v?ref_type=heads#L202).
The assertion `IsInt _i i` means that the machine integer `_i`
(whose type is `int`)
is the result of *projecting* the ideal integer `i`
(whose type is `Z`)
into the semi-open interval [0, 2^63).

This assertion, alone, does *not* mean that the ideal integer `i`
lies within the interval [0, 2^63).
For example, `isInt (1)%uint63 (1)%Z` is true,
and `isInt (1)%uint63 (2^63+1)%Z` is true as well.
For each machine integer `_i`, there is an infinite family
of ideal integers `i` such that `isInt _i i` holds.
Exactly one member of this family lies within the interval [0, 2^63).

We write `unsigned i` as an abbreviation for `0 ≤ i < 2^63`.
We write `isIntU _i i` as an abbreviation for `isInt _i i ∧ unsigned i`.
Thus, for each machine integer `_i`, there is exactly one ideal integer `i`
such that `isIntU _i i` holds.

In practice, which should be used: `isInt` or `isIntU`?
The answer varies.
Some operations need just `isInt` and guarantee just `isInt`;
some operations need `isIntU` and guarantee `isIntU`.
For example,
[addition](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/int.v?ref_type=heads#L289),
[subtraction](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/int.v?ref_type=heads#L302),
and
[multiplication](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/int.v?ref_type=heads#L312)
require `isInt` and ensure `isInt`.
In other words, these operations tolerate overflow
and have wrap-around semantics:
they do not require their arguments to lie within the interval [0, 2^63)
and they do not guarantee that their result lies within this interval.
In contrast,
[division](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/int.v?ref_type=heads#L486),
[minimum](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/int.v?ref_type=heads#L435),
[maximum](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/int.v?ref_type=heads#L444),
and the three primitive comparison operators
([`=?`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/int.v?ref_type=heads#L364),
 [`<?`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/int.v?ref_type=heads#L392),
 [`≤?`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/int.v?ref_type=heads#L416))
require their arguments to lie within this interval.

Most of the time, we do not use `isIntU _i i`,
which is an abbreviation for the conjunction `isInt _i i ∧ unsigned i`;
we prefer to treat `isInt _i i` and `unsigned i` as two separate facts.
We write `∀Int _i i, P` as sugar for `∀ _i i, isInt _i i → P`.
We write `∀IntU _i i, P` as sugar for `∀ _i i, isInt _i i → unsigned i → P`.

It is often necessary to write recursive functions whose termination argument
involves machine integers. Four well-founded orderings on machine integers are
commonly used in termination arguments:

+ `ilt` (which stands for *integer-less-than*)
  is used when a machine integer decreases towards 0,
  and cannot cross this threshold.
  That is, it cannot go below 0;
  or in other words, it cannot wrap around and become positive again.
+ `igt` (for *integer-greater-than*)
  is used when a machine integer increases towards 2^63-1
  and cannot cross this threshold.
+ `rilt _a` (which stands for *relative-integer-less-than*)
  is used when a machine integer decreases towards `_a`
  and cannot cross this threshold.
  In this case it is possible to start *below* `_a`
  and (by decreasing below 0) to wrap around
  and move into the very large positive integers;
  but it is not possible to cross `_a`,
  that is, to move from `_a` to a number that is less than `_a`.
+ `rigt _a` (which stands for *relative-integer-greater-than*)
  is used when a machine integer increases towards `_a`
  and cannot cross this threshold.

The tactic `tc` understands these orderings
and can prove goals that involve them.

<!--------------------------------------------------------------------------->

## Iteration

TODO: `iteration.v`

<!--------------------------------------------------------------------------->

## Iteration on Machine Integers

TODO: `loop.v`

<!--------------------------------------------------------------------------->

## Arrays

Rocq's
[primitive arrays](https://rocq-prover.org/doc/master/refman/language/core/primitive.html#primitive-arrays).
are persistent arrays, whose implementation exploits mutable arrays.
They are defined in the standard library modules
[PrimArray](https://rocq-prover.org/doc/V9.0.1/corelib/Corelib.Array.PrimArray.html),
[ArrayAxioms](https://rocq-prover.org/doc/V9.0.1/corelib/Corelib.Array.ArrayAxioms.html),
and
[PArray](https://rocq-prover.org/doc/v9.1/stdlib/Stdlib.Array.PArray.html).

An array should be viewed as an abstract data structure,
which holds a sequence of elements.

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

* [`init _n @@ body`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1949)
  ([specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1955))
  creates an array of length `_n` whose elements
  are computed by the function `body`.

  At each iteration, the loop body `body : int → A`
  receives the current index `_i` and returns an element.

  To reason about this operation,
  use the tactic [`wp_init`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1975).

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
  [(specification)](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1137)
  copies the array segment determined by the array `a`,
  the start index `_i`, and the length `_n`
  to the array segment determined by the array `b`,
  the start index `_j`, and the length `_n`.
  It returns an updated version of the array `b`.

  The arrays `a` and `b` must not be aliased: that is, they should be
  two *independent* arrays. To move data within a single array, use
  `blit'`.

  To reason about this operation,
  use the tactic [`wp_blit`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1370).
  This tactic intentionally clears the previous array `b`
  and names the new array `b` in the proof.

* [`blit' a _i _j _n`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1304)
  [(specification)](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1324)
  copies the array segment determined by the array `a`,
  the start index `_i`, and the length `_n`
  to the array segment determined by the array `a`,
  the start index `_j`, and the length `_n`.
  It returns an updated version of the array `a`.
  Thus, the array `a` is both read and written.
  The source and destination segments may overlap.

  To reason about this operation,
  use the tactic [`wp_blit`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1370).
  This tactic intentionally clears the previous array `a`
  and names the new array `a` in the proof.

* [`copy a`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1389)
  [(specification)](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1396)
  creates a fresh copy of the array `a`,
  that is, a new array whose content
  is the same as the content of the array `a`.

  To reason about this operation,
  use the tactic [`wp_copy b`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1408)
  where `b` is the name under which you would like
  the new array to be known.

* [`sub a _i _n`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1422)
  [(specification)](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1428)
  creates a new array whose content
  is the same as the content of the array segment
  determined by the array `a`, the start index `_i`,
  and the length `_n`.

  To reason about this operation,
  use the tactic [`wp_sub b`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1442)
  where `b` is the name under which you would like
  the new array to be known.

* [`append a b`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1459)
  [(specification)](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1471)
  creates a new array whose content is the concatenation
  of the content of the arrays `a` and `b`.

  To reason about this operation,
  use the tactic [`wp_append c`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1487)
  where `c` is the name under which you would like
  the new array to be known.

* [`fill a _i _n x`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1504)
  [(specification)](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1513)
  fills the array segment determined by the array `a`,
  the start index `_i`, and the length `_n`
  with the value `x`.
  It returns an updated version of the array `a`.

  To reason about this operation,
  use the tactic [`wp_fill`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1538).
  This tactic intentionally clears the previous array `a`
  and names the new array `a` in the proof.

* [`find_index f a`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1558)
  [(specification)](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1594)
  searches the array `a`, from left to right,
  for an element `x` such that `f x` is true.
  Its result has type [`outcome int`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/iteration.v?ref_type=heads#L39).

  To reason about this operation,
  use the tactic [`wp_find_index out`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1656)
  where `out` is the name under which you would like
  the result to be known.

* [`exist f a`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1670)
  [(specification)](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1683)
  searches the array `a`, from left to right,
  for an element `x` such that `f x` is true.
  Its result is `true` if such an element exists
  and `false` otherwise.

  To reason about this operation,
  use the tactic [`wp_exist b`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1699)
  where `b` is the name under which you would like
  the result to be known.

* [`for_all f a`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1715)
  [(specification)](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1728)
  tests whether every element `x` of the array `a`
  is such that `f x` is true.
  If so, its result is `true`;
  otherwise, its result is `false`.

  To reason about this operation,
  use the tactic [`wp_for_all b`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1744)
  where `b` is the name under which you would like
  the result to be known.

* [`equal eq a b`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1763)
  ([specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1807))
  tests whether the arrays `a` and `b` have the same length
  and have equal elements at every index `i`.
  The function `eq` is used to check two elements for equality.

  A [simpler specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1807) is given
  in the case where the function `eq` is an equality test.

* [`segment_iteri a _i _k s @@ body`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1885)
  ([specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1897))
  is a loop over the array segment determined by the array `a`,
  start index `_i`, and end index `_k`,
  with initial state `s`.

  At each iteration, the loop body `body : S → int → A → S`
  receives the current state `s`, the current index `_i`,
  and the current list element `x`, and returns a new state.

* [`iteri a s @@ body`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1891)
  ([specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1915))
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

<!--------------------------------------------------------------------------->

## Sorting

TODO: `sorting.v`
TODO: `sort.v`

<!--------------------------------------------------------------------------->

## Vectors

TODO: `vector.v`

<!--------------------------------------------------------------------------->

## Priority Queues

TODO: `pqueue.v`

<!--------------------------------------------------------------------------->

## The Linear Use Discipline

<!--------------------------------------------------------------------------->

## Execution inside Rocq

TODO

<!--------------------------------------------------------------------------->

## Extraction to OCaml

TODO

<!--------------------------------------------------------------------------->
