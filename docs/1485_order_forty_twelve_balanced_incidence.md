# Order forty: a small incidence check excludes the balanced twelve/eight case

Research note, 20 September 2026. This is a complete finite-assisted
exclusion of the remaining single-coset `(3,3,3,3)` by `(3,3,3,3)`
profile configuration. Its only finite step is a short, exhaustive
C++ incidence check; the final geometric contradiction is analytic.
It does not use SAT, an ATP, a search through Cayley tables, or an
enumeration of affine coordinate systems. It is not yet a Lean proof.

The source is
[1485_n40_twelve_thin_incidence_check.cpp](../scripts/1485_n40_twelve_thin_incidence_check.cpp).
The historical filename is retained, but **no thin-line hypothesis is
used**. The check was originally found while studying that subcase;
its actual premise is the uniform return weight proved in
[the balanced-return theorem](1485_order_forty_twelve_balanced_returns.md).

## 1. Necessary incidence conditions

Let `M,L⊆B` be the four sharp-degree-two and four sharp-degree-one
vertices. Label `M` by `0,…,3`, `L` by `4,…,7`. The binary matrices
`D,C` record ordinary adjacency and sharp two-step paths through `A`.
Their row and column degrees are respectively

\[
\deg D=(2,2,2,2,3,3,3,3),\qquad
\deg C=(2,2,2,2,1,1,1,1).
\]

The balanced-return theorem gives `β=η=1` on every `D` edge,
`C_{ML}=C_{LM}=0`, and `C_{LL}` a permutation matrix. In addition
the check imposes the following previously proved necessary conditions:

1. `(D²)_{ac}≥2` implies `C_{ac}=1`.
2. `aDbDcDd` and `C_{da}=1` imply `C_{ac}=C_{bd}`.
3. The return-matching capacities described next.

All vertices in these statements may repeat; loops are allowed.
There is no hidden irreflexivity or simple-cycle assumption.

For ordered endpoints `(b,d)`, write

\[
G_{db}=\#\{(x,y):dDxDyDb,\ C_{dy}=C_{xb}=0\},
\qquad K=CD+DC+G.
\]

The product `b*d` has degree five if `C_{bd}=1`, degree eight if
`C_{bd}=0` and `(D²)_{bd}>0`, and degree ten otherwise. Its return
fiber size is consequently `f_{bd}=8,5,4`, respectively. In the
degree-eight case the internal middle is unique by condition 1.

The [general return matching](1485_general_return_matching.md) has at
least `j_b+j_d` distinct matched edges incident to the independent
degree-five class. Every path counted by `G_{db}` gives a different
matched edge with both endpoints outside that class. Therefore

\[
G_{db}\le f_{bd}-j_b-j_d.                              \tag{1}
\]

The [mixed-return capacities](1485_order_forty_mixed_return_counts.md)
also give

\[
K_{db}\le4\quad\text{for every pair},\qquad
1\le K_{db}\le3\quad\text{for a degree-eight return}. \tag{2}
\]

The second bound specializes the general inequalities using the two
boundary weights `β=η=1`. The first is imposed even for top-valued
returns; omitting that case would weaken the finite check.

## 2. Complete normalization and enumeration

The check first enumerates all binary four-by-four matrices with both
margins two for `C_{MM}`. Each row is one of the six two-element
subsets, so only `6⁴` row choices are considered. After checking the
column margins it takes the lexicographically least representative
under all 24 simultaneous row/column relabelings. There are eight
representatives.

Likewise, the 24 permutations for `C_{LL}` give five representatives
under conjugation. The two label sets can be renamed independently,
so these give exactly `8·5=40` necessary `C` representatives. Every
permitted `C` is conjugate to one considered, and all imposed
conditions and reported conclusions are invariant under those
relabelings. No independent row and column permutations are used.

For each representative the program enumerates every `D` row of its
specified degree among the 256 eight-bit masks. It keeps the remaining
column capacities. A branch is discarded only when a column capacity
is exhausted, a capacity exceeds the number of remaining rows, an
already determined edge has `β≠1`, or two already determined
two-step paths repeat an endpoint outside `C`. Each discard is a
necessary violation, so an extendible partial matrix is never removed.

At a complete matrix the column margins are checked, followed by
`η=1`, the one-`A` closure condition, and (1)–(2). This enumerates
all required matrices, potentially with redundant isomorphic copies;
it does not assume any classification of the survivors.

Every survivor is tested directly for the following conclusion:

\[
\boxed{D_{MM}=0;\quad
\text{the medium-to-low neighbor pairs form a connected four-cycle,}
\text{ and so do the low-to-medium predecessor pairs}.}          \tag{3}
\]

More explicitly, view each medium vertex's two low successors as an
edge on the four low labels. The check verifies that every low label
has degree two and that these four edges give a connected graph.
It repeats precisely that test for the transpose matrix. Thus every
low vertex has exactly two medium and one low ordinary neighbor in
each direction. No recognition from a diagram is involved.

The exact counts are:

| Stage | Number |
|---|---:|
| `C` representatives | 40 |
| Partial search nodes | 3,984,137 |
| Complete `D` matrices after partial pruning | 21,272 |
| Also `η=1` | 21,025 |
| Also one-`A` closure | 316 |
| Also all return capacities | 56 |

The program asserts (3) for each of the 56 survivors. A concrete
positive necessary-incidence system passes every check, including
both cycle conclusions. A disconnected pair of doubled edges is
rejected by the cycle test. These are incidence controls, not claimed
E1485 multiplication tables. Assertions are essential, and compilation
with `NDEBUG` is explicitly rejected.

Reproduce with a standard C++17 compiler:

```sh
c++ -O3 -std=c++17 -Wall -Wextra -Werror scripts/1485_n40_twelve_thin_incidence_check.cpp -o /tmp/1485_n40_twelve_balanced_incidence
/tmp/1485_n40_twelve_balanced_incidence
```

A local run took approximately 6.4 seconds. It must print the stated
stage counts and report that both incidence graphs are four-cycles.
An independent warning-enabled `-O2` build and full rerun reproduced
every count and assertion in **9.74 seconds**. The analytic tail below
was also independently audited. A separately
[checked LRAT proof](../data/1485_certificates/A12_REGULAR_HOLES.md)
excludes this same branch using regular-hole fiber counts, without this
incidence classification; it is an alternative, not an extra premise.

## 3. The four-cycle conclusion makes every low profile affine

Fix `b∈L`. By (3), its internal predecessors consist of two medium
vertices and one low vertex. Their three sharp `F`-fibers contain
`2+2+1=5` vertices of `A`. Only these vertices can supply a non-top
middle for a product `a*b`. At least seven of the twelve products
therefore have a unique top middle, so at least seven incidences
`|V_a∩U_b|=1` occur.

All `V_a` profiles belong to a single four-line coset, with each
line occurring three times. A four-point set that is not transversal
to this partition can have intersection exactly one with at most
two lines, accounting for at most six vertices. Thus `U_b` is a
transversal. Its central-predecessor transversality makes its coordinate
map a permutation of four labels, hence affine over `F₂²`.

The dual argument uses the two medium and one low internal successors
of `b` to show that `V_b` is an affine transversal as well. This
establishes the previously unavailable low-profile affineness, not
merely a hypothesis about it.

## 4. Six good pairs contradict uniform translation fibers

By the balanced-return theorem, `g_b=6` for every low vertex. If
either affine profile had full-rank projection onto its own profile
labels, its line-intersection row would be `(1,1,1,1)`, allowing
at most four hole pairs. Rank zero is excluded by the no-line
theorem. Thus both profile projections have rank one, with support
two lines each.

In the [standard affine coordinates](1485_order_forty_thirteen_directions.md#1-affine-coordinates-and-the-attached-rank-one-profiles),
the central-successor labels on `U_b` have a two-element image,
and the central-predecessor labels on `V_b` also have a two-element
image. On either occupied line of each profile the two point labels
run once through the corresponding image. Let `c∈{0,1,2}` be
the intersection size of these two images, and `h` the number of
holes in the two-by-two support rectangle. The four holes form a
matching, so `h≤2`. Every active hole contributes `4−c` good
top pairs, giving

\[
6=g_b=h(4-c).
\]

Consequently `h=2,c=1`. In one active hole, the two first endpoints
therefore have respectively one and two good second endpoints: one
of their central labels matches a second-endpoint label and the
other does not.

This violates a direct translation-fiber uniformity. For any top
predecessor `u∈U_b∩P_i`, the four-element fiber `L_u^{-1}(b)`
contains exactly `j_b` sharp degree-five inputs and, among the
degree-eight inputs, precisely those internal successors `d` of `b`
whose `F`-fiber does not contain predecessor line `P_i`. There
are no central inputs. Both counts depend only on `i`, not on the
choice of `u` within `P_i`. Its remaining elements are exactly
the good top inputs. Therefore both first endpoints in `U_b∩P_i`
must have the same number of good top partners, contradicting the
counts one and two above.

This excludes every surviving incidence matrix and completes the
balanced single-coset exclusion, with the finite dependency confined
to the fully specified eight-vertex incidence check.
