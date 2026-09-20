# A restriction on the seven-plus-seven order-48 branch

Research note, 19 September 2026. This is an analytic necessary
condition, not a Lean theorem or a complete exclusion.

Assume the order-48, minimum-four, four-central configuration of
[the main note](1485_order_forty_eight_min_four.md), with fourteen
degree-six vertices `A` and fourteen degree-eight vertices `B`.
Consider its remaining sharp-count distribution

\[
(n_1,n_2,n_3)=(7,0,7).
\]

Write `L,H` for the seven members of `B` with sharp counts one
and three. Their internal ordinary in/out degrees are three and
one, respectively. The total number `ε` of bad ordinary
`B→B→B` paths is at most sixteen.

**Theorem.** At least four members of `H` have their internal
predecessor and successor in `L`. The remaining members of `H`
form isolated directed cycles in the internal `B` adjacency.
Their total number is zero, two, or three; in the latter two cases
they form a single directed cycle of that length.

If exactly four members are attached to `L`, each member of `L`
has at most two predecessors and at most two successors in `H`.
There are either two or three active members of `L`. In the
two-member case the four attached `H` vertices realize the four
ordered pairs of active `L` vertices exactly once.

Loops are initially allowed by the graph description but excluded
by the return-fiber argument in §5. This does not exclude the
displayed sharp-count distribution.

## 1. The internal graph and its sharp two-step relation

Let `K` indicate endpoint pairs in `B×B` with a sharp middle
in `A`. Its row and column sums are `2j_b` at a vertex `b`.
All its paths are good and unique. Let `E` indicate endpoint
pairs with a good middle in `B`, and let `D` be internal
ordinary adjacency. Thus `D²−E` counts bad internal paths.

The good-return inequality says that a top product `b*d` requires
`j_b+j_d≤4`. Consequently every `H×H` product has its good
middle in `A` or `B`, never in the top class.

If `h→h'` is an internal edge between two members of `H`,
there are at most `3·2+1=7` paths from `h` through `A∪B`
to `B`. All seven `H` endpoints need such a path. Hence every
product from `h` to `L` is top, and the successor of `h'`
must also lie in `H`. Finiteness and internal in/out degree one
show that every such edge lies in an isolated directed cycle of
`H` vertices. Write `c` for the number of vertices on these
cycles, and put `h=7−c`. Each of the other `h` vertices has
both its internal predecessor and successor in `L`.

For `l∈L`, put

\[
a_l=|Col(l)\cap H|,\qquad b_l=|Row(l)\cap H|.
\]

Both sums over `L` equal `h`. Moreover

\[
a_l>0\quad\Longleftrightarrow\quad b_l>0.                 \tag{1}
\]

For example, if `u→l` with `u∈H`, the six paths through
sharp `A` successors of `u` cannot cover all seven `H`
endpoints. Some ordinary path `u→l→v` therefore has `v∈H`.
The converse is the column-dual argument.

Let `x` count the entries of `K` in `H×L`. It also counts
those in `L×H`, since the row and column sums of `K` on
each class agree. Hence

\[
|K\cap(H\times H)|=42-x,\qquad
|K\cap(L\times L)|=14-x.                                  \tag{2}
\]

## 2. A quantitative lower bound for bad paths

Write `ε_HH,ε_LL` for the numbers of bad internal paths with
their two endpoints in the indicated classes. There are

\[
c+\sum_l a_lb_l
\]

ordinary internal two-step paths from `H` to `H`: the cycles
contribute `c`, and the paths with middle in `L` give the sum.
All 49 endpoint pairs have a good middle in `A` or `B`, so (2)
gives exactly `7+x` good internal paths. Therefore

\[
\varepsilon_{HH}=\sum_l a_lb_l-h-x.                         \tag{3}
\]

The number of ordinary internal paths from `L` to `L` is

\[
h+\sum_l(3-a_l)(3-b_l)
=63-5h+\sum_l a_lb_l.
\]

At most `49−(14−x)=35+x` of these can be good. Using (3),

\[
\varepsilon_{LL}\ge28-4h+\varepsilon_{HH},\qquad
\boxed{\varepsilon\ge28-4h+2\varepsilon_{HH}.}              \tag{4}
\]

Since `ε≤16`, we immediately have `h≥3`.

## 3. Equality at three attached vertices is impossible

Suppose `h=3`. Equation (4) forces

\[
\varepsilon=16,\qquad \varepsilon_{HH}=0,
\qquad \varepsilon_{LL}=16.
\]

Every `L×L` endpoint pair has a good middle in `A` or `B`,
and every bad internal path has both endpoints in `L`.

We first record an equality consequence of the top-packing argument
in [the main note, §§2–5](1485_order_forty_eight_min_four.md).
Across the four central parameters there are 64 auxiliary rows
starting at top vertices. Each contains one central output. A row
containing a top output has precisely the degree pattern
`{4,6,8,12}`. At `f=14`, the aggregate number of top outputs
in these rows is `24+ε`, while the aggregate number of degree-eight
outputs is `56−ε`. When `ε=16`, both numbers are forty.
Since every row containing a top output also contains exactly one
degree-eight output, all degree-eight occurrences lie in these rows.
Every remaining row therefore has pattern `{4,6,6,6}`.

The degree-eight output fiber in a `{4,6,8,12}` row contains
exactly one top input. Applying this on both sides proves that the
good ordered top pairs producing any fixed member of `B` form a
partial matching on its four top predecessors and four top successors.
There are at most four such good pairs.

For `l∈L`, let `ε_l` count bad internal paths starting at `l`.
If `c(l,v)` is the number of auxiliary relations containing the
ordinary internal edge `l→v`, the exact fiber count gives

\[
\varepsilon_l=\sum_{v\in Row(l)\cap B}(c(l,v)-2).
\]

The number of good ordered top pairs producing `l` is

\[
16-4-\sum_{v\in Row(l)\cap B}c(l,v)
=6-\varepsilon_l.
\]

The matching bound consequently gives `ε_l≥2`; dually, at least
two bad internal paths end at each member of `L`.

Put `x_l=|K(l)∩H|`. Since all `L×L` endpoint pairs are
covered by `K` or a good internal path, the number of good internal
paths from `l` to `L` is `5+x_l`. The ordinary count is

\[
9-2b_l-\sum_{v\in Row(l)\cap L}b_v.
\]

All bad paths starting at `l` end in `L`. Thus

\[
2\le\varepsilon_l
=4-2b_l-\sum_{v\in Row(l)\cap L}b_v-x_l.
\]

In particular `b_l≤1`. The dual argument gives `a_l≤1`.
Their sums are three and their supports agree by (1), so exactly
three members of `L` have `a_l=b_l=1`. Therefore
`Σa_lb_l=h=3`, and (3) gives `x=0`.

There are consequently no sharp two-step paths from `H` to `L`
or from `L` to `H`. Every member of `A` has two sharp
predecessors and two sharp successors in `B`. Its predecessors
cannot include both an `H` vertex and an `L` vertex, since
then either class of successor would create a forbidden cross path.
Thus each member of `A` has all four sharp neighbors in `H`,
or all four in `L`.

But the number of sharp edges from `H` to `A` is `7·3=21`,
whereas each member of the first sector receives exactly two such
edges. This is impossible. Hence `h≥4`, proving the theorem.

## 4. Four attached vertices have small attachment multiplicities

Suppose `h=4`. Let `G_LL` count `L×L` endpoint pairs with
top product, and let `ε_HL,ε_LH` count bad internal paths with
the indicated endpoints. The exact version of the count in §2 is

\[
\varepsilon_{LL}=12+\varepsilon_{HH}+G_{LL}.
\]

Consequently

\[
\boxed{2\varepsilon_{HH}+\varepsilon_{HL}
       +\varepsilon_{LH}+G_{LL}\le4.}                       \tag{5}
\]

For each `l∈L`, write `g_l` for the number of top products
from `l` to `L`, and `e_l` for the number of bad internal paths
from `l` to `H`. The exact row calculation, now allowing these
additional possibilities, gives

\[
\varepsilon_l
=4-2b_l-\sum_{v\in Row(l)\cap L}b_v-x_l+g_l+e_l.           \tag{6}
\]

If `b_l=3`, there are at most two active members of `L`,
since `Σb_v=4`. Each of the three `H` successors of `l`
returns to an active member of `L`. Two therefore have the same
return endpoint. Equal-degree ordinary middles cannot include a
good one when there are two different choices, so these give at
least two bad paths: `ε_l≥2`.

There is no internal `L` successor of this vertex. Equation (6)
therefore gives

\[
g_l+e_l=\varepsilon_l+2+x_l\ge4.
\]

By (5), equality holds throughout: `ε=16`, `ε_HH=ε_HL=0`,
`x_l=0`, and all of `G_LL+ε_LH=4` is concentrated at `l`.
But a bad path from `l` to `H` would have its sharp good
replacement counted by `x_l`; hence `e_l=0`. Thus there are
exactly four top-valued `L×L` pairs, all in a single row.

At `ε=16`, §3 gives at least two bad internal paths ending at
each member of `L`. The column-dual of (6), using `ε_HL=0`,
shows that a column at a vertex with `a_v≥2` must contain at
least two top-valued `L×L` pairs. Such a vertex exists: four
`H` attachments enter at most two active members of `L`.
But pairs confined to a single row contribute at most one to a
column. This contradiction excludes `b_l=3`. The dual argument
excludes `a_l=3`.

There cannot be four active vertices either. That would force
`a_l=b_l=1` on all four, so (3) would give
`ε_HH=−x`. Both quantities would be zero, contradicting the
odd sharp-sector count at the end of §3. There are therefore
two or three active vertices.

If there are two, both have `a_l=b_l=2`. The attachment matrix
whose entries count `L→H→L` paths on these two vertices has
every row and column sum two. It is either the all-ones matrix
or twice a permutation matrix.

The doubled-permutation alternative gives at least two bad internal
paths starting at each active vertex. In (6), their baseline terms
`4−2b_l−Σb_v−x_l` are nonpositive, so `g_l+e_l≥2` at each.
Equation (5) again forces `ε=16`, `ε_HH=ε_HL=0`, and all
four units of `G_LL+ε_LH` to be concentrated equally on these
two rows. Equality in (6) also gives `x_l=0` there. Thus their
bad-path counts into `H` vanish, and all four units are top-valued
`L×L` pairs, two in each active row.

The column-dual matching bound requires at least two of these pairs
in each active column. Since there are only two available rows,
all four pairs in the active two-by-two square must be top-valued.
This contradicts its ordinary paths through the attached `H`
vertices. The attachment matrix must consequently be all ones.

These refinements leave the three-active-vertex case, the all-ones
two-active-vertex case, and the cases with five, six, or seven
attached vertices. The next section excludes six attached vertices.

## 5. Good-return fibers exclude isolated high loops

Here is a useful form of the
[general return matching](1485_general_return_matching.md).
If `b,d∈B`
and `e=b*d`, there are exactly `n/d(e)` three-edge ordinary paths

\[
d\to x\to y\to b
\]

for which both adjacent two-edge paths are good. Indeed goodness
says `d*y=x` and `x*b=y`. E1485 and its dual then give

\[
e*x=(b*d)*(d*(x*b))=d,
\qquad y*e=((d*y)*b)*(b*d)=b.
\]

Thus these paths are exactly the matched pairs of the bijection
between `L_e^{-1}(d)` and `R_e^{-1}(b)`.

Exactly `j_d` of the first internal vertices `x` lie in `A`,
and exactly `j_b` of the second internal vertices `y` lie in
`A`: these are the sharp neighbors of the endpoints. The two
possibilities are disjoint because `A→A` edges do not exist.
Consequently

\[
\boxed{\#\{\text{good-good reverse triples wholly in }B\}
       \le n/d(e)-j_b-j_d.}                                \tag{7}
\]

For `b,d∈H` with `e∈B`, the right side is `6−3−3=0`.
In particular there cannot be an all-good ordinary five-cycle
entirely in `H`: two of its edges exhibit the product `e∈B`,
and the other three give a forbidden good-good reverse triple.

All two-edge paths in the isolated `H` cycles of §1 are good.
For a vertex on such a cycle, the six sharp-middle paths and the
single internal-middle path must cover the seven `H` endpoints
without overlap, as in the original path count. An isolated loop,
or a directed cycle of length five, therefore gives an all-good
five-cycle by traversal and is impossible.

Since there are at most three isolated vertices in total, none
can form a loop. They consequently form no cycle, one two-cycle,
or one three-cycle. Equivalently

\[
\boxed{h\in\{4,5,7\},\qquad c\in\{3,2,0\}.}
\]

The wholly-internal bound (7) applies to all sharp-count profiles
of the four-degree configuration, not only this seven-plus-seven
case. It is an additional necessary condition, not a construction
of any surviving case.
