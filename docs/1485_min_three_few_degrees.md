# Minimum degree three: further restrictions with few translation degrees

Research note, 18 September 2026. These are restrictions on the
unresolved cases, not a proof of the full spectrum conjecture. All
arguments below are analytic except two explicitly marked uses of
finite incidence lemmas for the degree-four and degree-five branches.
Both check the same 285 normalized central-incidence diagrams.
Write `n` for the order and `r=3` for the minimum translation degree.
All degrees divide `n`, their maximum is `n/3`, and their set is
closed under `d↦n/d`.

**Theorem.** A minimum-degree-three model with at most four distinct
translation degrees has full core. In particular its order is a
square or twice a square. With exactly four degrees, its order is
72, by the full-core four-degree theorem.

Thus every non-full model at minimum degree three needs at least
five distinct degrees; a counterexample to the spectrum conjecture
needs at least six, since an odd degree count forces square order.
The proof retains the finite-check dependencies for the four-central,
nine-top cases with least noncentral degree four or five.

## Three central vertices

The [three-central theorem](1485_three_central_minimum_top_output.md)
forces degree four and `12|n`. Let `A` be its degree-four class,
and `B` the degree-`n/4` class. Every member of `A` has exactly
one sharp successor and predecessor in `B`, while every member of
`B` needs one or more such neighbors. Hence `|B|≤|A|≤8`.

With exactly four degrees these are the only middle classes. There
are three central and nine top vertices, so

\[
n=12+|A|+|B|\le28.
\]

The four classes are nonempty and distinct. Divisibility by twelve
therefore leaves only order 24, whose three-central case has already
been excluded analytically: the [profile reduction](1485_order_twenty_four_three_central_reduction.md)
leaves only the [nine/three](1485_order_twenty_four_three_central.md)
and [six/six](1485_order_twenty_four_six_six_profiles.md) cases,
both impossible.

Three degrees would make the middle degree four self-complementary,
giving `n=16`, contrary to `3|n`. A single degree would make every
vertex central. Two degrees would force `n=18` by the
[two-degree cardinality theorem](1485_two_degree_lower_bound.md),
contrary to `12|n`. Thus at least five degrees are needed.

## Four central and ten top vertices

Use the [ten-top reductions](1485_four_central_residual.md). The least
noncentral degree is five: degree six is now excluded by the
[strict top-product gap](1485_strict_top_product_gap.md). Its class
and its reciprocal class have sizes `(1,1)` or `(3,9)`. With exactly four
degrees the order would therefore be either `4+10+1+1=16` or
`4+10+3+9=26`. Neither is divisible by five.

Three degrees are also impossible: degree five cannot be self-
complementary because `3|n`. A single degree cannot
have distinct central and top classes, while two degrees would make
the order both `4+10=14` and `18`. This proves the claimed
five-degree lower bound.

An odd number of degrees always forces square order, by the reciprocal
involution. Thus a nonsquare order in either of the two branches above
requires at least six distinct degrees.

## Four central and nine top vertices, exactly four degrees

Let `q>3` be the least noncentral degree and `b=n/q` the other
middle degree. Then `q<b`. A least-degree vertex has only sharp
non-top neighbors. If its common sharp in/out count is `k`, its
common top in/out count is `t=q−k`, where `1≤k≤3` and
`2≤t≤4`. Hence `q≤7`. The number of ordered top pairs
producing it is exactly `t(3−k)`.

For `q=4`, the [order-independent degree-four bound](1485_four_central_degree_four.md)
makes every degree-four vertex have sharp degree one, bounds its
class by four, and bounds the reciprocal class by the same number.
Consequently `n≤4+9+4+4=21`. But `12|n` and `b>4` give
`n≥24`, a contradiction. This uses the explicit finite profile bound.

For `q=6`, the [least-degree-six lemma](1485_four_central_nine_top.md#6-least-degree-six-is-sharp-regular)
makes every such vertex sharp-regular, with no top representations.
Thus all noncentral top products have degree `b`. The strict
top-product gap gives `6<b<9`, leaving `n=42` or `n=48`.
Both cases are excluded analytically: see the
[order-42 proof](1485_order_forty_two.md) and the
[order-48, least-degree-six proof](1485_order_forty_eight_min_three.md).
This excludes `q=6` with four degrees. In particular order 54,
the former saturation case `b=9`, is no longer a candidate.

For `q=7`, the [four-top-neighbor obstruction](1485_four_central_nine_top.md)
excludes the case independently of the order or degree count: its
`4×4` central-middle submatrix would have to be all ones, whereas
a singleton-successor row has at most two ones.

The remaining `q=5` case is excluded below. With three degrees,
the middle degree would be self-complementary. The surviving options
`q=4` or `q=6` would give respectively `n=16`, contrary to `3|n`,
or `n=36`, with no degree-eight top product as required by the
strict top-product gap's nine-top corollary. One degree gives full
core; two would force both `n=13` and `n=18`. This completes
the claimed five-degree lower bound in the nine-top branch.

## Degree five: a separately marked finite incidence step

The `q=5` branch needs a separate finite incidence lemma:

> At minimum degree three, with four central and nine top vertices,
> if five is the least noncentral degree, there is at most one
> irregular degree-five vertex. It has sharp degree two.

This lemma is presently justified by direct finite enumeration, not
by a hand classification or Lean proof. The existing
[central-rectangle enumeration](1485_order_twenty_four_four_central_finite.md)
generates all 285 normalized incidence diagrams; its exhaustiveness
depends only on the central/top profile, not on order 24. For each
diagram enumerate the top predecessor/successor profiles of common
size three or four which partition the central labels. The
central-middle submatrix must have every row and column sum two.
All valid profiles have size three, and any two in one diagram
share a noncentral good endpoint pair. Different degree-five
vertices cannot share such a pair, proving the lemma.

The standard-library implementation is independently inspectable and
uses no SAT solver or canonical-orbit pruning:

```sh
python3 scripts/1485_m4h9_incidence_check.py --degree-five
```

It checks all 285 diagrams and obtains profile counts
`263×0, 12×1, 10×2`; it asserts that every profile has exactly
three good pairs and that each pair of profiles overlaps. The
second assertion, not merely the profile count, gives the bound of
one realizable irregular vertex.

The [analytic two-by-two obstruction](1485_four_central_nine_top.md#5-no-sharp-regular-least-degree-five-vertices)
excludes all sharp-regular degree-five vertices. Thus the entire
degree-five class would be a singleton with sharp degree two.
Every reciprocal-degree vertex must have that singleton as both
its sharp predecessor and successor. Its two sharp successors would
then give two good paths from the singleton back to itself, impossible.

This [excludes least noncentral degree five](1485_four_central_degree_five.md)
independently of the number of degree classes, subject to the explicit
finite profile lemma above.
