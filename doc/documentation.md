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
We provide the notation [`do x ← e1 ; e2`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/wp.v?ref_type=heads#L49)
to facilitate this. It should typically be used when one thinks
of `e1` as a (possibly complex) *computation* whose result one wants to name `x`.
Rocq's native notation `let x := e1 in e2` can also be used.
It should typically be used when `e1` is a (small) *expression*,
such as an arithmetic expression.

We also provide the notation [`f @@ x`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/wp.v?ref_type=heads#L39)
for function application. This notation allows the parentheses around the
argument `x` to be omitted, even if this argument is a complex expression.
This is very useful when `f` is a higher-order function and `x` itself is a
function: in particular, this leads to a rather nice way of writing
[loops](#iteration-on-machine-integers).

We offer syntactic sugar for two dependent conditional constructs,
[`IFC e0 THEN e1 ELSE e2`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/equations.v?ref_type=heads#L26)
and
[`IF e0 THEN e1 ELSE e2`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/equations.v?ref_type=heads#L29).
These constructs are useful and necessary
when the status of condition `e0`
is needed in a proof of termination,
that is,
when a proof of termination
needs a hypothesis of type `e0 = true` or `e0 = true`.
The definition of [`iter_down`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/loop.v?ref_type=heads#L94)
offers an example of this.

<!--------------------------------------------------------------------------->

## Verifying Programs

To help users write specifications and verify programs, we define a simple
program logic, in the style of Hoare logic.
The judgement [`wp e Q`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/wp.v?ref_type=heads#L103)
means that the expression `e` admits the postcondition `Q`:
that is, result of `e` satisfies the property `Q`.
Naturally, Rocq does not distinguish between a computation and its result:
they are considered equal. Thus, the definition of `wp e Q` is just `Q e`.
Nevertheless, the judgement `wp` is useful: applying its reasoning rules lets
us reason step by step about the behavior of a program.

The basic reasoning rules are
[return](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/wp.v?ref_type=heads#L123),
[sequencing](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/wp.v?ref_type=heads#L135),
[conditional](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/wp.v?ref_type=heads#L110),
and
[consequence](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/wp.v?ref_type=heads#L217).

To apply these reasoning rules, we offer a number of tactics.

The tactic [`wp_ret`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/wp.v?ref_type=heads#L247) should be used when the goal is
`wp e Q` where `e` is a variable or a simple expression,
such as an arithmetic expression. It transforms the goal into `Q e`
and attempts to solve it using the tactic
[`wp_ret_hook`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/wp.v?ref_type=heads#L242), which can be customized.

The tactic [`wp_if`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/wp.v?ref_type=heads#L260) should be used when the goal is
`wp e Q` where `e` is a conditional construct (that is, `if/then/else`
or `IF/THEN/ELSE` or `IFC/THEN/ELSE`). It generates one subgoal for the
Boolean condition (which ideally should be automatically solved) and
one subgoal for each branch.

The tactic [`wp_op`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/wp.v?ref_type=heads#L409) is the main workhorse of
this small tactic library. It should be used when the goal is a function call
or begins with a function call: that is, when the goal is `wp (f y z ...) Q`
or `wp (do x ← f y z ... ; e) Q`. This tactic expects one argument, namely a
lemma that offers a specification of the function `f`. First, it automatically
applies the sequencing rule or the consequence rule (whichever is applicable);
then, it applies the lemma whose name is provided. If this lemma has
hypotheses (which are usually known as preconditions) then it attempts
to solve these subgoals by applying the tactics
[`wp_precondition_primary_hook`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/wp.v?ref_type=heads#L336)
and
[`wp_precondition_secondary_hook`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/wp.v?ref_type=heads#L340),
which can be customized.
It produces two kinds of subgoals:
first, the preconditions that it was not able to solve;
second, the subgoal that represents
the continuation of the operation `f y z ...`.

In the last subgoal of `wp_op <lemma>`,
one typically uses either [`wp_intro x`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/wp.v?ref_type=heads#L289)
or
[`wp_shadow x`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/wp.v?ref_type=heads#L308).

[`wp_intro x`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/wp.v?ref_type=heads#L289)
introduces the result of the operation `f y z ...`
under the name `x`. (`x` can be a variable or a composite pattern.)
It also introduces a hypothesis about `x`,
which represents the postcondition of the operation `f y z ...`,
and uses the tactic [`wp_intro_hook`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/wp.v?ref_type=heads#L280),
which can be customized, to destruct or simplify this postcondition.

[`wp_shadow x`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/wp.v?ref_type=heads#L308)
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
[`tc`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/tactics.v?ref_type=heads#L86)
and its depth-indexed variants [`tc0` to `tc7`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/tactics.v?ref_type=heads#L77)
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
we define the type class [`isBool b P Q`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/bool.v?ref_type=heads#L38).
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
reasoning rule [`wp_if`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/wp.v?ref_type=heads#L110), so (provided suitable instances of
the type class `isBool` are available) the tactic `wp_if` automatically
transforms a Boolean condition into the logical proposition that it
represents.

We provide instances of the type class `isBool` for the most common logical
connectives:
[conjunction](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/bool.v?ref_type=heads#L90),
[disjunction](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/bool.v?ref_type=heads#L98),
and
[negation](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/bool.v?ref_type=heads#L106).

We also provide instances of the type class `isBool`
for the primitive comparison operations
on [machine integers](#machine-integers).
Some of these instances have side conditions:
for example, [`isBool_ltb`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/int.v?ref_type=heads#L404),
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
[`isInt _i i`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/int.v?ref_type=heads#L214).
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
[addition](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/int.v?ref_type=heads#L301),
[subtraction](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/int.v?ref_type=heads#L314),
and
[multiplication](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/int.v?ref_type=heads#L324)
require `isInt` and ensure `isInt`.
In other words, these operations tolerate overflow
and have wrap-around semantics:
they do not require their arguments to lie within the interval [0, 2^63)
and they do not guarantee that their result lies within this interval.
In contrast,
[division](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/int.v?ref_type=heads#L498),
[minimum](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/int.v?ref_type=heads#L447),
[maximum](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/int.v?ref_type=heads#L456),
and the three primitive comparison operators
([`=?`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/int.v?ref_type=heads#L376),
 [`<?`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/int.v?ref_type=heads#L404),
 [`≤?`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/int.v?ref_type=heads#L428))
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

In functional programming languages, it is common to write iteration functions
as higher-order functions. The producer (the function that produces elements)
takes the consumer (the function that processes elements) as an argument. One
can also think of the producer function as a *loop* that takes the *loop body*
as an argument. We typically name these functions `iter`, although (since they
carry a state) they could also be named `fold`.

To facilitate reasoning about these functions, we provide several very general
specifications, which, once suitably instantiated, can describe a wide variety
of iteration functions. Here, we do not describe these definitions in detail,
but provide a brief summary:

+ [`ITER`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/iteration.v?ref_type=heads#L130) is a very general specification
  for an `iter` function. Its parameters `init` and `complete` describe
  the initial state and final state of the producer; the parameter `body`
  describes at the same time the evolution of the producer's state and
  the calling convention of the loop body; the parameter `loop` describes
  the calling convention of the loop itself.

+ [`XITER`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/iteration.v?ref_type=heads#L204) is a variant of `ITER` where the
  loop is exitable: the loop body has access to two continuations,
  `break` and `continue`, allowing it to indicate whether it wishes to
  terminate early or to continue.

+ [`UXITER`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/iteration.v?ref_type=heads#L229) is a degenerate variant of
  `XITER` where the loop-carried state has type `unit`.

We instantiate these general specifications for several common situations:

+ [`ITERI_LIST`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/iteration.v?ref_type=heads#L263) and
  [`ITER_LIST`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/iteration.v?ref_type=heads#L296) are
  specialized versions of `ITER`
  where the producer iterates, *in order* (from left to right), over a list `xs`.
  The producer's state is a history of the elements produced so far:
  it forms a prefix of the list `xs`.

+ [`ITERI_MULTISET`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/iteration.v?ref_type=heads#L326) and
  [`ITER_MULTISET`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/iteration.v?ref_type=heads#L344) are
  specialized versions of `ITER`
  where the producer iterates, *in an arbitrary order*,
  over a multiset `xs`.
  The producer's state is a history of the elements produced so far:
  it forms a sub(multi)set of the multiset `xs`.

+ [`ITER_Z`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/iteration.v?ref_type=heads#L532),
  [`XITER_Z`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/iteration.v?ref_type=heads#L543), and
  [`UXITER_Z`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/iteration.v?ref_type=heads#L554)
  are specialized versions of `ITER`, `XITER`, and `UXITER`
  where the producer iterates (either upwards or downwards)
  over a semi-open interval [i, k) of the integers.
  The producer's state is just an integer index:
  when going up, it is the index that will be produced next;
  when going down, it is the index that has been produced last.

It is worth noting that the type of the producer state is not necessarily
the type of the elements that the consumer receives. Therefore,
`ITER_Z` *can* be used to describe a loop where the
consumer receives, say, machine integers
(as in [`loop.iter_down`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/loop.v?ref_type=heads#L146)),
or array elements
(as in [`array.iteri`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1632)).

We provide several tactics that help work with these specifications:

+ The tactics
  [`ITER`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/iteration.v?ref_type=heads#L602),
  [`XITER`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/iteration.v?ref_type=heads#L606), and
  [`UXITER`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/iteration.v?ref_type=heads#L610)
  should be used when the goal is `ITER ...`, `XITER ...`,
  or `UXITER ...`. They unfold definitions in the goal and
  introduce the hypotheses under fixed conventional names.

+ At the beginning of the loop body, the tactic
  [`wp_body`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/iteration.v?ref_type=heads#L283) should be used.
  It is a higher-order tactic; it is meant to be specialized
  so as to define more palatable tactics for use by end users.
  For example, in the file `array.v`,
  the tactic [`wp_iteri_body`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1655)
  concerns a loop that takes the form of a call to the higher-order function
  [`array.iteri`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1607).
  This tactic should be used at the beginning of the loop body.

+ In the body of an exitable loop, the tactics
  [`wp_continue`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/iteration.v?ref_type=heads#L618) and
  [`wp_break`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/iteration.v?ref_type=heads#L630)
  should be used to reason about calls to the continuations.

<!--------------------------------------------------------------------------->

## Iteration on Machine Integers

The file [`loop.v`](../src/loop.v)
offers several higher-order functions
that implement loops over an interval of the machine integers.

By convention,
in loops that go *up*,
the *current index* is the index that is about to be produced.
In loops that go *down*,
the *current index* is the last index that has been produced.
This is visible in the definition of
[`ITER_Z`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/iteration.v?ref_type=heads#L532)
and in the auxiliary definition
[`z_step`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/iteration.v?ref_type=heads#L507)

+ [`iter_down _i _k s @@ body`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/loop.v?ref_type=heads#L136)
  applies the loop body `body` to every machine
  integer from `_k`, excluded, down to `_i`, included. A state of type `S`,
  whose initial value is `s`, is transformed at each iteration
  and eventually returned.

  To reason about a call to `iter_down`, use the tactic
  `wp_op wp_iter_down with invariant: ...`.
  At the beginning of the loop body, use the tactic
  [`wp_iter_down_body _j j s`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/loop.v?ref_type=heads#L404).
  This tactic introduces the current index `_j` and its integer model `j`
  as well as the current state `s`.

+ [`xiter_down _i _k s @@ body`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/loop.v?ref_type=heads#L438)
  applies the loop body `body` to every machine
  integer from `_k`, excluded, down to `_i`, included. This is an exitable
  loop. An invocation of the loop body takes the form `body _j s continue break`.
  That is, the loop body receives two continuations `continue` and `break`,
  and must invoke either `continue s` or `break s x`.
  It is useful when one wishes to scan an interval
  and stop as soon as something of interest is found.

  To reason about a call to `xiter_down`, use the tactic
  `wp_op wp_xiter_down with invariant: ...`.
  At the beginning of the loop body, use the tactic
  [`wp_xiter_down_body _j j s`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/loop.v?ref_type=heads#L498).

+ [`uxiter_down _i _k @@ body`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/loop.v?ref_type=heads#L528)
  is a variant of `xiter_down` without a state `s`.
  It is useful when one wishes to scan an interval
  and one does not need to accumulate information during the scan.

  To reason about a call to `uxiter_down`, use the tactic
  `wp_op wp_uxiter_down with invariant: ...`.
  At the beginning of the loop body, use the tactic
  [`wp_xiter_down_body _j j`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/loop.v?ref_type=heads#L587).

+ [`iter_up _i _k s @@ body`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/loop.v?ref_type=heads#L629)
  applies the loop body `body` to every machine integer
  from `_i`, included, up to `_k`, excluded.

  To reason about a call to `iter_up`, use the tactic
  `wp_op wp_iter_up with invariant: ...`.
  At the beginning of the loop body, use the tactic
  [`wp_iter_up_body _j j s`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/loop.v?ref_type=heads#L848).
  This tactic introduces the current index `_j` and its integer model `j`
  as well as the current state `s`.

+ [`xiter_up _i _k s @@ body`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/loop.v?ref_type=heads#L878)
  applies the loop body `body` to every machine integer
  from `_i`, included, up to `_k`, excluded.
  This is an exitable loop.

  To reason about a call to `xiter_up`, use the tactic
  `wp_op wp_xiter_up with invariant: ...`.
  At the beginning of the loop body, use the tactic
  [`wp_xiter_up_body _j j s`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/loop.v?ref_type=heads#L930).

+ [`uxiter_up _i _k @@ body`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/loop.v?ref_type=heads#L958)
  is a variant of `xiter_up` without a state `s`.

  To reason about a call to `uxiter_up`, use the tactic
  `wp_op wp_uxiter_up with invariant: ...`.
  At the beginning of the loop body, use the tactic
  [`wp_xiter_up_body _j j`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/loop.v?ref_type=heads#L1006).

<!--------------------------------------------------------------------------->

## Arrays

Rocq's
[primitive arrays](https://rocq-prover.org/doc/master/refman/language/core/primitive.html#primitive-arrays)
are persistent arrays, whose implementation exploits mutable arrays.
They are defined in the standard library modules
[PrimArray](https://rocq-prover.org/doc/V9.0.1/corelib/Corelib.Array.PrimArray.html),
[ArrayAxioms](https://rocq-prover.org/doc/V9.0.1/corelib/Corelib.Array.ArrayAxioms.html),
and
[PArray](https://rocq-prover.org/doc/v9.1/stdlib/Stdlib.Array.PArray.html).

An array should be viewed as an abstract data structure,
which holds a sequence of elements.

The proposition [`isArray a xs`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L116) means
that the elements of the array `a` form the list `xs`. This
proposition allows reasoning about the content of the array; it
appears in the specification of every operation on arrays. This
proposition is in fact equivalent to `to_list a = xs`
([lemma](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L541));
nevertheless it is recommended to always prefer writing `isArray a xs`
and to treat this proposition as abstract.

### Primitive Operations

There are four primitive operations on arrays:

* `make _n x` ([specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L314))
  creates a new array of length `_n`
  where every slot is filled with the value `x`.
  The parameter `_n`, a machine integer,
  must not exceed `max_array_length`.

  To reason about this operation,
  use the tactic [`wp_make a`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L387),
  where `a` is the name under which you would like
  the newly allocated array to be known in the proof.
  It is sugar for `wp_op wp_make introducing: a`.

* `length a` ([specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L363))
  returns the length of the array `a`.

  To reason about this operation,
  use the tactic [`wp_length n`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L376),
  where `n` is the name under you would like the length
  of this array to be known in the proof.
  It is sugar for `wp_op wp_length introducing: n`.

* `get a _i` ([specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L327))
  returns the element stored at index `_i` in the array `a`.

  To reason about this operation,
  use the tactic [`wp_get x`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L379),
  where `x` is the name under you would like this element
  to be known in the proof.
  It is sugar for `wp_op wp_get introducing: x`.

* `set a _i x` ([specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L339))
  stores the element `x` at index `_i` in the array `a`.
  It returns an updated array.
  Thereafter, the previous array should no longer be used.
  It is recommended to name the new array also `a` so as to reduce
  the risk of accessing the previous array by mistake.

  To reason about this operation,
  use the tactic [`wp_set`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L382).
  This tactic intentionally clears the previous array `a`
  and names the new array `a` in the proof.
  It behaves like `wp_op wp_set shadowing: a`.

### More Operations

* [`segment_to_list a _i _k`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L421)
  [(specification)](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L456)
  converts the array segment determined by the array `a`
  and the start and end indices `_i` and `_k` into a list.

* [`to_list a`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L442)
  [(specification)](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L480)
  converts the array `a` into a list.

  For this operation,
  we provide [a second specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L501).
  This specification is unusual in that it does not require `isArray a _`
  as a precondition: on the contrary, its postcondition indicates that
  it returns a list `xs` such that `isArray a xs` holds.
  This allows obtaining a proposition of the form `isArray a xs`
  about an array of arbitrary provenance.

  In a related vein, the lemma [`isArray_iff`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L541)
  establishes that `isArray a xs` is equivalent to `to_list a = xs`.

* [`of_list xs`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L778)
  [(specification)](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L792)
  converts the list `xs` to an array.

  This operation requires `len xs ≤ max_array_length`: that is, the
  length of the list `xs` must not exceed `max_array_length`.

  The lemma [`to_list_of_list`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L820)
  states that converting a list to an array, then back to a list,
  is the identity.

  The reverse round-trip property (which would state that converting
  an array to a list, then back to an array, is the identity)
  [is not true](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L857),
  because an array is defined not only by its content
  but also by its default value.

* [`init _n @@ body`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1670)
  ([specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1688))
  creates an array of length `_n` whose elements
  are computed by the function `body`.

  At each iteration, the loop body `body : int → A`
  receives the current index `_i` and returns an element.

* [`list_length xs`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L739)
  ([specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L747))
  returns the length of the list `xs` as a machine integer.

  Although this is not an operation on arrays, it can be useful.
  It is used in the implementation of `of_list`.

* [`list_iteri _i xs s @@ body`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L572)
  ([specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L604))
  is a loop on the list `xs`, with initial index `_i` and initial state `s`.
  At each iteration, the loop body `body : S → int → A → S`
  receives the current state `s`, the current index `_i`,
  and the current list element `x`, and returns a new state.

  Although this is not an operation on arrays, it can be useful.
  It is used in the implementation of `of_list`.

* [`blit a _i b _j _n`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L911)
  [(specification)](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L947)
  copies the array segment determined by the array `a`,
  the start index `_i`, and the length `_n`
  to the array segment determined by the array `b`,
  the start index `_j`, and the length `_n`.
  It returns an updated version of the array `b`.

  The arrays `a` and `b` must not be aliased: that is, they should be
  two *independent* arrays. To move data within a single array, use
  `blit'`.

  To reason about this operation,
  use the tactic [`wp_blit`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1073).
  This tactic intentionally clears the previous array `b`
  and names the new array `b` in the proof.
  It behaves like `wp_op wp_blit shadowing: b`.

* [`blit' a _i _j _n`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L991)
  [(specification)](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1038)
  copies the array segment determined by the array `a`,
  the start index `_i`, and the length `_n`
  to the array segment determined by the array `a`,
  the start index `_j`, and the length `_n`.
  It returns an updated version of the array `a`.
  Thus, the array `a` is both read and written.
  The source and destination segments may overlap.

  To reason about this operation,
  use the tactic [`wp_blit`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1073).
  This tactic intentionally clears the previous array `a`
  and names the new array `a` in the proof.
  It behaves like `wp_op wp_blit shadowing: a`.

* [`copy a`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1092)
  [(specification)](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1099)
  creates a fresh copy of the array `a`,
  that is, a new array whose content
  is the same as the content of the array `a`.

* [`sub a _i _n`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1122)
  [(specification)](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1128)
  creates a new array whose content
  is the same as the content of the array segment
  determined by the array `a`, the start index `_i`,
  and the length `_n`.

* [`append a b`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1156)
  [(specification)](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1168)
  creates a new array whose content is the concatenation
  of the content of the arrays `a` and `b`.

* [`fill a _i _n x`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1198)
  [(specification)](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1219)
  fills the array segment determined by the array `a`,
  the start index `_i`, and the length `_n`
  with the value `x`.
  It returns an updated version of the array `a`.

  To reason about this operation,
  use the tactic [`wp_fill`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1239).
  This tactic intentionally clears the previous array `a`
  and names the new array `a` in the proof.
  It behaves like `wp_op wp_fill shadowing: a`.

* [`find_index f a`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1259)
  [(specification)](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1309)
  searches the array `a`, from left to right,
  for an element `x` such that `f x` is true.
  Its result has type [`outcome int`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/iteration.v?ref_type=heads#L51).

* [`exist f a`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1382)
  [(specification)](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1395)
  searches the array `a`, from left to right,
  for an element `x` such that `f x` is true.
  Its result is `true` if such an element exists
  and `false` otherwise.

* [`for_all f a`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1424)
  [(specification)](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1437)
  tests whether every element `x` of the array `a`
  is such that `f x` is true.
  If so, its result is `true`;
  otherwise, its result is `false`.

* [`equal eq a b`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1469)
  ([specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1513))
  tests whether the arrays `a` and `b` have the same length
  and have equal elements at every index `i`.
  The function `eq` is used to check two elements for equality.

  A [simpler specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1513) is given
  in the case where the function `eq` is an equality test.

* [`segment_iteri a _i _k s @@ body`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1588)
  ([specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1613))
  is a loop over the array segment determined by the array `a`,
  start index `_i`, and end index `_k`,
  with initial state `s`.

  At each iteration, the loop body `body : S → int → A → S`
  receives the current state `s`, the current index `_i`,
  and the current list element `x`, and returns a new state.

  To reason about this operation, use the tactic
  `wp_op wp_segment_iteri`.
  At the beginning of the loop body, use the tactic
  [`wp_segment_iteri_body _j j x s`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1650).

* [`iteri a s @@ body`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1607)
  ([specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1632))
  is a loop over the array `a`
  with initial state `s`.

  At each iteration, the loop body `body : S → int → A → S`
  receives the current state `s`, the current index `_i`,
  and the current list element `x`, and returns a new state.

  To reason about this operation, use the tactic
  `wp_op wp_iteri`.
  At the beginning of the loop body, use the tactic
  [`wp_iteri_body _j j x s`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1655).

### Tactics

The tactic [`isArray`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L397) is applicable when the
goal has the form `isArray a ys` and there is a hypothesis of the form
`isArray a xs`. The goal is then reduced to the equation `xs = ys` and
this equation is simplified. If the equation is found to be true then
the goal is solved.

The tactic [`arrays`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L159) looks for every hypothesis of the
form `isArray a xs` and introduces the fact `0 ≤ len xs ≤ max_array_length`.
It also introduces the fact `unsigned max_array_length`. It is often useful
to invoke this tactic once at the beginning of a proof.

<!--------------------------------------------------------------------------->

## Sorting

The file [`sort.v`](../src/sort.v) contains algorithms that sort arrays and
merge sorted arrays.

The desired ordering, and comparison function, are provided in an implicit
way, via type class instances. The type class [`Leb`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/compare.v?ref_type=heads#L33)
provides a two-way comparison function; the type class
[`LebSpec`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/compare.v?ref_type=heads#L90) provides a proof that this function is
correct with respect to a certain pre-order `≤`. It is up to you, as a user,
to provide suitable instances of these type classes.

+ [`isortto`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/sort.v?ref_type=heads#L663) and
  [`isortto'`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/sort.v?ref_type=heads#L888) are
  insertion sort algorithms.
  They read an array segment, sort it,
  and write the sorted data into another array segment.
  They do not scale (they have quadratic complexity),
  but may be interesting when one wishes to sort very short arrays.
  They are currently unused, though one could decide to use them
  at the leaves of the merge sort algorithms.

+ [`sort_seg a _i _n`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/sort.v?ref_type=heads#L2488)
  ([specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/sort.v?ref_type=heads#L2496))
  is a merge sort algorithm.
  It sorts the array segment described by the array `a`,
  start index `_i`, and length `_n`.
  The data is sorted in place; an updated array is returned.
  This is a stable sort: if two elements are equivalent
  according to the pre-order `≤` then they are not exchanged.
  When stability is not useful,
  [a simpler specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/sort.v?ref_type=heads#L2700)
  can be used.

  To reason about this operation, use the tactic
  [`wp_sort_seg`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/sort.v?ref_type=heads#L2775).
  It intentionally shadows the array `a`.
  It uses the simpler specification of `sort_seg`, without stability.

+ [`sort a`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/sort.v?ref_type=heads#L2523)
  ([specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/sort.v?ref_type=heads#L2551))
  is a merge sort algorithm.
  It sorts the array `a`.
  The data is sorted in place; an updated array is returned.
  This is a stable sort: if two elements are equivalent
  according to the pre-order `≤` then they are not exchanged.
  When stability is not useful,
  [a simpler specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/sort.v?ref_type=heads#L2728)
  can be used.

  To reason about this operation, use the tactic
  [`wp_sort`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/sort.v?ref_type=heads#L2781).
  It intentionally shadows the array `a`.
  It uses the simpler specification of `sort`, without stability.

+ [`merge a b`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/sort.v?ref_type=heads#L2572)
  ([specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/sort.v?ref_type=heads#L2585))
  merges the sorted arrays `a` and `b`.
  In other words, `merge a b` first constructs a new array by concatenating
  the arrays `a` and `b`, then sorts this array.
  This is a stable merge: if two elements are equivalent
  according to the pre-order `≤` then they are not exchanged.
  When stability is not useful,
  [a simplified specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/sort.v?ref_type=heads#L2751)
  can be used.

  To reason about this operation, use the tactic
  `wp_op wp_merge sort introducing: c`
  where `c` is the name under which you would like
  the new array to be known in the proof.

A number of definitions, lemmas, and tactics related to sorting exist in the
file [`sorting.v`](../src/sorting.v). They are not intended to be used by end
users of the library.

<!--------------------------------------------------------------------------->

## Vectors

A vector is an abstract data structure, which holds a sequence of elements.
Internally, these elements are stored in an array, whose length is possibly
greater than the length of the sequence. The length of this array is usually
known as the vector's *capacity*, whereas the length of the sequence is
known as the vector's *length*.

The proposition [`isVector v xs`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/vector.v?ref_type=heads#L56)
means that the vector `v` stores the sequence `xs`.

### Operations

+ [`create()`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/vector.v?ref_type=heads#L194)
  ([specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/vector.v?ref_type=heads#L201))
  creates a new empty vector.

+ [`length v`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/vector.v?ref_type=heads#L212)
  ([specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/vector.v?ref_type=heads#L216))
  returns the length of the vector `v`.

+ [`get v _i`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/vector.v?ref_type=heads#L227)
  ([specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/vector.v?ref_type=heads#L231))
  returns the element found at index `_i` in the vector `v`.

+ [`set v _i x`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/vector.v?ref_type=heads#L240)
  ([specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/vector.v?ref_type=heads#L245))
  writes the element `x` at index `_i` in the vector `v`.
  An updated vector is returned.

  To reason about this operation, use the tactic
  `wp_op vector.wp_set shadowing: v`,
  where `v` is the name of the vector.

+ [`pop v`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/vector.v?ref_type=heads#L265)
  ([specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/vector.v?ref_type=heads#L275);
   [alternate specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/vector.v?ref_type=heads#L292))
  extracts and the last element of the vector `v`.
  The vector must be nonempty.
  A pair of the extracted element
  and an updated vector is returned.

+ [`push v x`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/vector.v?ref_type=heads#L414)
  ([specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/vector.v?ref_type=heads#L429))
  appends the element `x` onto the vector `v`.
  An updated vector is returned.

  To reason about this operation, use the tactic
  `wp_op vector.wp_push shadowing: v`,
  where `v` is the name of the vector.

+ [`reserve v`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/vector.v?ref_type=heads#L465)
  ([specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/vector.v?ref_type=heads#L479))
  reserves a new slot at the end of the vector `v`,
  but does not initialize it.
  An updated vector is returned.

  To reason about this operation, use the tactic
  `wp_op vector.wp_reserve shadowing: v`,
  where `v` is the name of the vector.

+ [`segment_iteri v _i _k s @@ body`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/vector.v?ref_type=heads#L512)
  ([specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/vector.v?ref_type=heads#L522))
  is a loop over the segment determined by the vector `v`,
  start index `_i`, and end index `_k`,
  with initial state `s`.

  To reason about this operation, use the tactic
  `wp_op vector.wp_segment_iteri`.
  At the beginning of the loop body, use the tactic
  [`wp_segment_iteri_body _j j x s`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1650).

+ [`iteri v s @@ body`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/vector.v?ref_type=heads#L516)
  ([specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/vector.v?ref_type=heads#L540))
  is a loop over the vector `v`
  with initial state `s`.

  To reason about this operation, use the tactic
  `wp_op vector.wp_iteri`.
  At the beginning of the loop body, use the tactic
  [`wp_iteri_body _j j x s`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/array.v?ref_type=heads#L1655).

+ [`steal_array a`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/vector.v?ref_type=heads#L566)
  ([specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/vector.v?ref_type=heads#L576))
  and
  [`of_array a`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/vector.v?ref_type=heads#L570)
  ([specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/vector.v?ref_type=heads#L588))
  both convert an array to a vector.
  In `steal_array`, the array becomes part of the representation
  of the vector, and should no longer be used.
  In `of_array`, the array is copied, so the array and the vector
  can be used independently.

+ [`of_list xs`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/vector.v?ref_type=heads#L641)
  ([specification](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/vector.v?ref_type=heads#L647))
  converts a list to a vector.

### The Unboxed Vector API

The [unboxed-vector API](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/vector.v?ref_type=heads#L663)
allows the two components of a vector,
namely its length `_n` and its backing array `a`,
to be separately maintained by the user.
This contrasts with the normal vector API,
where these components must form a pair `(_n, a)`.

The unboxed-vector API offers direct access to the array `a` and allows the
user to avoid needless allocations of pairs. This API is purely logical. It
does not offer any operations of its own. Instead, it offers a set of
reasoning rules, which allow the user to access the array `a` directly, while
still reasoning at the level of abstraction of the vector.

We do not describe this API here. For an example of its use,
see the file [`pqueue.v`](../src/pqueue.v),
where the function [`move_up`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/pqueue.v?ref_type=heads#L582)
uses direct array accesses,
and the [proof](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/pqueue.v?ref_type=heads#L671) of this function
uses the unboxed-vector API.

### Tactics

The tactic [`isVector`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/vector.v?ref_type=heads#L158) is applicable when the
goal has the form `isVector v ys` and there is a hypothesis of the form
`isVector v xs`. The goal is then reduced to the equation `xs = ys` and
this equation is simplified. If the equation is found to be true then
the goal is solved.

The tactic [`vectors`](https://gitlab.inria.fr/fpottier/marble/-/blob/main/src/vector.v?ref_type=heads#L131) looks for every hypothesis of
the form `isVector v xs` and introduces the fact `0 ≤ len xs ≤ max_array_length`.
It also introduces the fact `unsigned max_array_length`.
It is often useful to invoke this tactic once at the beginning of a proof.

<!--------------------------------------------------------------------------->

## Priority Queues

TODO: `pqueue.v`

<!--------------------------------------------------------------------------->

## The Linear Use Discipline

TODO

<!--------------------------------------------------------------------------->

## Execution inside Rocq

TODO

<!--------------------------------------------------------------------------->

## Extraction to OCaml

TODO

<!--------------------------------------------------------------------------->
