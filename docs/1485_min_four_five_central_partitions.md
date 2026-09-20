# Minimum four with five central vertices: partition restrictions

Research note, 19 September 2026. These are analytic necessary
conditions for a finite E1485 magma. They do not prove that a surviving
incidence pattern is realizable by a magma, and they do not exclude
this central-cardinality case.

The degree-seven classification below is now used in the separate
[first-output degree-seven exclusion](1485_min_four_five_central_seven_exclusion.md).
Thus the degree-seven entries in the preliminary table are no longer
surviving cases; first-output degrees five and six remain.

Assume minimum degree `r=4` and central cardinality `m=5`. Write
`P_v,C_v` for a top vertex's central predecessor and successor sets.
Each central row or column partitions the five central vertices into
four nonempty blocks. Consequently

\[
1\le |P_v|,|C_v|\le2.                              \tag{1}
\]

Let `N_ij` count tops with `|P_v|=i, |C_v|=j`.

## 1. The global top-profile counts have one integer parameter

The central incidence moments give

\[
\sum iN_{ij}=\sum jN_{ij}=20,
\qquad \sum ijN_{ij}=25.
\]

Putting `d=N_22`, these equations imply

\[
\boxed{N_{11}=5+4d,\qquad
N_{12}=N_{21}=5-2d,\qquad N_{22}=d,\quad d\in\{0,1,2\}.}
                                                               \tag{2}
\]

In particular the top class has cardinality `15+d`. These three
possibilities are necessary moment solutions, not model constructions.

For a first noncentral top output of degree `p`, let `t` be its
equal number of top predecessors and successors. The first-output
fiber theorem gives `p−3≤t≤p−1`. Its top profiles partition five
central vertices into blocks of size one or two, so `3≤t≤5`.
The existing first-output gap gives `p≤7`. Thus the possibilities are

| First-output degree `p` | Top-profile size `t` | Non-top neighbors `p−t` |
| ---: | --- | --- |
| 5 | 3 or 4 | 2 or 1 |
| 6 | 3, 4, or 5 | 3, 2, or 1 |
| 7 | 4 or 5 | 3 or 2 |

The non-top neighbors need not all be sharp in this statement.

## 2. Degree seven with four top neighbors forces the middle moment solution

Suppose a degree-seven first top output `a` has `t=4`. Let
`U=TopPred(a)` and `V=TopSucc(a)`. Its central-middle matrix
has row and column sum `p−r=3`. After reindexing, it is

\[
K=J_4-I_4.                                           \tag{3}
\]

For each central `z`, its contribution to this matrix is the
rectangle

\[
\{u\in U:z\in C_u\}\times\{v\in V:z\in P_v\}.
\]

The nonempty rectangles partition the twelve entries of (3), by
uniqueness of the central middle. There are at most five rectangles.
Each row and each column belongs to at most two of them, by (1).

A rectangle with width three must have height one: in `J_4-I_4`,
only the row whose excluded position is the fourth column can have
all those three entries. Dually a height-three rectangle has width
one. Every other rectangle has both dimensions at most two.

Let `s` count `2×2` rectangles, `g` count the stars of shape
`1×3` or `3×1`, `h` count dominoes of shape `1×2` or `2×1`,
and `f` count singletons. A row lying in just one rectangle must
be a width-three star; every other row lies in exactly two
rectangles. The dual assertion holds for columns. Thus total
row-plus-column membership is `16−g`. Counting that same quantity
and counting the twelve entries gives

\[
4s+4g+3h+2f=16-g,
\qquad 4s+3g+2h+f=12.
\]

Equivalently,

\[
2g+h+f=4,\qquad 4s+g+h=8.
\]

Nonnegativity leaves only two possibilities:

* `s=1,g=0,h=4,f=0`;
* `s=2,g=0,h=0,f=4`.

The latter uses six rectangles, more than there are central vertices.
Therefore all five central vertices contribute, and the partition
has exactly **one square and four dominoes**. Each row and each
column has two memberships. Hence every `u∈U` has `|C_u|=2`,
and every `v∈V` has `|P_v|=2`.

Every central row contains exactly one top with central successor
count two. Thus the `P`-blocks of all such tops partition the central
set. The four tops in `U` already have their `P`-blocks partitioning
that set, so they exhaust the tops with central successor count two.
Consequently `N_12+N_22=4`. Formula (2) gives `d=1`, and therefore

\[
\boxed{(N_{11},N_{12},N_{21},N_{22})=(9,3,3,1),
\qquad |T|=16.}                                    \tag{4}
\]

Together with a row-local degree bound, this classification gives the
[degree-seven exclusion](1485_min_four_five_central_seven_exclusion.md).

## 3. What the same arithmetic says at other small central counts

For minimum four and `m=5,...,10`, every central block has size
at most `min(4,m−3)`. If a block of size four occurs, the
[full-column argument](1485_first_top_output_divisor_gap.md#1-a-large-first-output-excludes-full-central-incidence-counts)
forces every vertex to have exactly four top neighbors. Hence any
first output has `t=4` and `p−4` non-top neighbors.

In the complementary branch all central blocks have size at most
three, and a first-output profile has

\[
\max\!\left(\left\lceil m/3\right\rceil,p-3\right)
\le t\le\min(m,p-1).
\]

For fixed bounds `L≤|P_v|,|C_v|≤R`, each block also belongs
to an ordinary central partition into four blocks, giving the
refinement

\[
\max(L,m-3R)\le |P_v|,|C_v|\le\min(R,m-3L).
\]

These elementary refinements alone do not exclude the first-output
degrees five through seven at central counts six through ten.
