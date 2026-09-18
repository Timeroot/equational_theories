# E1485 spectrum: the remaining degree patterns

Research status, 18 September 2026. The full square/twice-square converse
is still open in this work. This note records reductions that include
all models with at most three distinct translation degrees, and all
models with a full central core, including every minimum-degree-two
model. The arguments
are pen-and-paper proofs, not new Lean declarations.

Let `M` be a nonempty finite E1485 magma of order `n`. The
[finite structure theorems](1485_graph_research.md) give
`d(x)=|Row(x)|=|Col(x)|`, uniform nonempty translation fibers, and a
sharp successor and predecessor of every element. An edge `x⇒y` is
sharp precisely when `d(x)d(y)=n`.

## Odd numbers of degree values force square order

Let `D={d(x):x∈M}` be the set of distinct degree values. If `d∈D`,
choose a vertex of degree `d` and a sharp successor. That successor
has degree `n/d`. Thus the map

\[
 d\longmapsto n/d
\]

is an involution of `D`. If `|D|` is odd, this involution has a fixed
point: its non-fixed orbits have size two. For a fixed degree `d`,
`d=n/d`, and hence

\[
 \boxed{|D|\text{ odd}\quad\Longrightarrow\quad n=d^2.}
\]

In particular this handles every model with one or three degree values,
and equally applies to five, seven, or any other odd number of values.
Equivalently, if `n` is not a square, its occurring degree values come
in distinct complementary pairs.

## Two degree values force twice-square order

If `D={r,s}` with `r<s`, the extremal product theorem gives `n=rs`.
The [three five-cycle counts](1485_two_degree_lower_bound.md) prove

\[
 \boxed{s=2r,\qquad n=2r^2.}
\]

No hypothesis about constancy of sharp-neighbor counts is used here.
Their constancy is a stronger structural question, still open in general;
it is not needed for this cardinality theorem.

Every product of two distinct primes is consequently excluded. Such an
order cannot have a constant row (constant-row models have power-of-two
order), and degree divisibility and the extremal product then force
exactly the two prime degrees. They cannot have ratio two.

## What a remaining counterexample would have to look like

A finite model whose order is neither a square nor twice a square must
have **an even number of distinct translation degrees, at least four**.
For four values, write them in increasing order as

\[
 r<a<b<s.
\]

The complementary-degree involution is order reversing, so

\[
 rs=ab=n.
\]

This does not yet force `b=2a`, or otherwise give the desired square
class of `n`. The two-degree proof cannot simply be applied to the
middle degree classes: their union need not be closed under multiplication.

## Full core now settles every number of degrees

Write `Z` for the central class. The
[full-core sharp-regularity theorem](1485_full_core_sharp_regularity.md)
and [Boolean quotient theorem](1485_full_core_quotient.md) prove

\[
\boxed{|Z|=r²\quad\Longrightarrow\quad n=r²2^m
\quad\text{for some integer }m\ge0.}
\]

This is a square when `m` is even and twice a square when `m` is odd.
It also gives the exact degree distribution:

\[
\#\{x:d(x)=r2^j\}=r²\binom mj\qquad(0\le j\le m).
\]

At minimum degree two, the [two-central](1485_two_central_exclusion.md)
and [three-central](1485_three_central_exclusion.md) exclusions prove
`|Z|=4` unconditionally. Thus every such model has order `4·2^m`,
not just those with four degree values. In particular, a counterexample
to the spectrum conjecture must have **minimum degree at least three**,
an even number of degree values at least four, and a non-full core.

The full-core quotient construction has no remaining unproved
compatibility or goodness-reflection requirement. The unproved step is
full core for arbitrary finite models. See the
[current proof frontier](1485_proof_status.md) for the exact chain.

## Completed small-order exclusions

The [order-twelve proof](1485_order_twelve.md) and
[order-twenty-eight proof](1485_order_twenty_eight_min_two_reduction.md)
exclude those orders. The [order-twenty-four proof](1485_order_twenty_four.md)
also excludes every central-cardinality case at minimum degree three;
its five formerly surviving incidence patterns are no longer open.
That proof explicitly separates its analytic arguments from two small
finite incidence enumerations. These enumerations are not Lean proofs.

## The remaining structural target

The [sharp-degree defect note](1485_sharp_degree_defect.md) gives a
separate global reduction. The integer

\[
 \Delta=\sum_x d(x)-\sum_x n/d(x)
\]

is nonnegative, and vanishes if and only if every sharp in-degree and
out-degree equals the minimum ordinary degree. Its vanishing remains
unproved. This structural target is stronger than the cardinality
conclusion already established for two-degree models; it must not be
treated as a necessary intermediate step for every spectrum proof.

The [equivalent-targets note](1485_full_core_equivalences.md) identifies
vanishing defect with full core, equality of the extreme degree-class
sizes, symmetry of central-valued products, and centrality of every top
element's square. None of these has been proved for arbitrary finite
models. The stronger full-core conjecture could conceivably fail at a
square or twice-square order without refuting the spectrum conjecture.

The [one-missing-vertex theorem](1485_near_full_core.md) excludes
`|Z|=r²−1` at every minimum degree. Consequently a putative
counterexample has `r≤|Z|≤r²−2`, as well as the degree restrictions
above. Larger central defects remain open.
The [general gap theorem](1485_small_central_defects.md) further gives
`δ(δ+1)>r` for every positive defect `δ=r²−|Z|`.

Uniform fibers of individual translations must not be confused with
uniform joint fibers of `x↦(h*x,x*h)` for central `h`: the latter
claim is false, as the explicit order-eight example in the
[projection note](1485_image_research.md) shows.
