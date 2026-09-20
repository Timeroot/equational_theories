# Order forty: four top neighbors force at most six central elements

Research theorem, 20 September 2026. This is a short analytic counting
obstruction, independently audited. No incidence enumeration, SAT
refutation, or Lean formalization is involved.

**Theorem.** Suppose a finite E1485 magma has order forty, minimum
translation degree four, and exactly four top predecessors and four
top successors at every vertex. Then its central count satisfies

\[
\boxed{|Z|\le6.}
\]

In particular this excludes the uniform-top-neighborhood branches at
central counts seven, eight, nine, and ten. It does not exclude the
remaining, nonuniform branches at those central counts.

## 1. Degree classes and sharp counts

The maximum degree is ten. Counting edges ending in the top class
gives `4·40=10|T|`, so `|T|=16`. Let `m=|Z|`, and let `A,B`
be the degree-five and degree-eight classes, of sizes `a,b`. A full
core would force order `16·2^j`, not forty. The
[first-output divisor gap](1485_first_top_output_divisor_gap.md)
therefore gives a first noncentral top-output degree at most seven,
necessarily five since degrees divide forty. Degree reciprocity also
gives degree eight; the only available degrees are `4,5,8,10`. Thus

\[
a+b=24-m.
\tag{1}
\]

Each member of `A` has one non-top neighbor in either direction;
these are sharp neighbors in `B`. At `x∈B`, the four non-top
neighbors consist of sharp `A` neighbors and ordinary internal `B`
neighbors. The [reciprocal-neighbor balance](1485_two_degree_research.md#a-weighted-balance-identity)
equates `36+3j` in the two directions, so the sharp counts agree.
Write them as `j_x`, with `1≤j_x≤4`. Counting sharp edges gives

\[
\sum_{x\in B}j_x=a,
\]

and each vertex has `4−j_x` internal predecessors and successors.

## 2. Count bad paths globally, not edge by edge

For an internal edge `x→y`, let `η(x,y)` count bad internal
predecessor paths `w→x→y`. The right-translation fiber
`R_y^{-1}(x)` has size five. Its non-top inputs are the four
non-top predecessors of `x`, except the `η` bad ones. Consequently
it has exactly `1+η(x,y)` top inputs.

There are four top predecessors of `x`, each contributing a
four-element left-translation fiber with output `x`. The sharp
successors in `A` account for `4j_x` input occurrences. The internal
successors account for

`4−j_x+Σ_(y:x→y)η(x,y)`

occurrences. All remaining inputs are top, so the number `g_x` of
ordered top pairs whose product is `x` satisfies

\[
g_x=12-3j_x-\sum_{y:x\to y}\eta(x,y).
\tag{2}
\]

Summing the last term over all `x` counts each bad internal two-edge
path exactly once. Count the same paths by their starting vertex.
A bad internal path starting at `x` must end at one of the `j_x`
distinct sharp two-step endpoints through `A`: a central replacement
is impossible for degree-eight endpoints, and the only other smaller
degree is five. Distinct such sharp middles have distinct endpoints
by uniqueness of good middles. There are `4−j_x` choices of its
ordinary internal middle. Therefore

\[
\sum_{x\in B}g_x
\ge12b-3a-\sum_xj_x(4-j_x)
=12b-7a+\sum_xj_x^2.
\tag{3}
\]

This argument does **not** assume equality of bad predecessor and
extension counts on individual edges. Only their global totals agree,
because both count the same paths.

For every positive integer `j`, `(j−1)(j−2)≥0`, so
`j²≥3j−2`. Substituting in (3) gives

\[
\sum_{x\in B}g_x\ge10b-4a.
\tag{4}
\]

## 3. Two bounds on the same degree-five class

Each central element is the product of exactly sixteen top pairs.
Each member of `A` has twelve such representations: its four top
fibers each contain its one sharp non-top successor and three tops.
There are only `16²=256` top pairs. Ignoring the other classes first,

\[
16m+12a\le256,
\qquad a\le\frac{64-4m}{3}.
\tag{5}
\]

Using (4) as well, then (1), gives

\[
256\ge16m+12a+10b-4a
=240+6m-2a,
\qquad a\ge3m-8.
\tag{6}
\]

Together (5)–(6) imply `13m≤88`, hence the integer bound `m≤6`.
This proves the theorem.

## Consequence for full central blocks

The [full-block argument](1485_order_forty_ten_central_full_blocks.md)
shows, at order forty and minimum four with `m≥5`, that a size-four
central block in either direction forces one in the other direction
at the same top, and then forces four top neighbors everywhere.
Thus no size-four central block can occur when `7≤m≤10`.

At `m=10`, every central block is therefore at most three. The
[ten-central theorem](1485_order_forty_ten_central_small_blocks.md)
and the [unit-or-large theorem](1485_unit_large_central_tiles.md)
then leave only seventeen or eighteen top elements. This removes the
formerly separate full-block branch without a finite check.
The later [unified ten-central argument](1485_order_forty_ten_central_exclusion.md)
eliminates both remaining values analytically.
