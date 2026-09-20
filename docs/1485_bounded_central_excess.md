# A quantitative first-output bound for bounded central excess

Research note, 19 September 2026. This is an analytic finite E1485
inequality, not yet formalized in Lean. It uses an elementary
permutation-counting extension of the set-pairs bound.

Let the minimum degree be `r`, let the central class have size
`m=r+c`, and suppose the central core is not full. Let `p` be
the least degree of a noncentral product of two top vertices. Put

\[
C_c=\binom{2c+2}{c+1}.
\]

**Theorem.**

\[
\boxed{p\le r+m-\left\lceil\frac{m}{C_c}\right\rceil.}       \tag{1}
\]

For fixed central excess `c`, this improves the first-output bound
at sufficiently large minimum degree. It is a necessary condition,
not a proof of full core.

## 1. Regular disjointness and permutation events

Let `A_1,...,A_t` and `B_1,...,B_t` be nonempty finite sets.
Suppose each `A_i` is disjoint from exactly `h>0` of the `B_j`,
and each `B_j` is disjoint from exactly `h` of the `A_i`.

The disjointness bipartite graph has a perfect matching. Indeed,
for a set of left vertices, its `h` times as many incident edges
all enter its neighbor set, which has at most `h` incident edges
per right vertex. Hall's condition follows. Reindex along a perfect
matching so that `A_i∩B_i=∅` for every `i`.

Take a uniformly random ordering of the finite union of all the
sets. Let `E_i` be the event that every element of `A_i` occurs
before every element of `B_i`. Its probability is

\[
\Pr(E_i)=\binom{|A_i|+|B_i|}{|A_i|}^{-1}.                     \tag{2}
\]

At most `h` of these events can occur simultaneously. To see this,
among the occurring events choose `E_i` for which the last element
of `A_i` occurs earliest. If another occurring `E_j` had
`A_i∩B_j≠∅`, then

\[
\max pos(A_j)<\min pos(B_j)\le\max pos(A_i),
\]

contradicting that choice. Thus `A_i` is disjoint from every
`B_j` whose event occurs, and there are exactly `h` available
indices.

Taking expectations proves the weighted bound

\[
\boxed{\sum_{i=1}^t
\binom{|A_i|+|B_i|}{|A_i|}^{-1}\le h.}                       \tag{3}
\]

In particular, if all set sizes are at most `k`, each summand is
at least `1/binom(2k,k)`, giving

\[
\boxed{t\le h\binom{2k}{k}.}                                \tag{4}
\]

Only disjointness is used here; nonempty cross-intersections need
not be singletons. Asymmetric size bounds `|A_i|≤a`, `|B_i|≤b`
give the analogous constant `binom(a+b,a)`.

## 2. Apply the bound to a first noncentral top output

Every central row and column partitions the `m` central vertices
into `r` nonempty central-neighbor blocks. Hence each such block
has size at most

\[
m-r+1=c+1.
\]

Choose a degree-`p` top output. The
[first-output fiber theorem](1485_first_top_output_fibers.md)
gives equally many top predecessors and successors, say `t`, and
a regular central-middle matrix with row and column sum `p−r`.
Its entries are intersections of the sets

\[
A_i=C_{u_i},\qquad B_j=P_{v_j},
\]

where `u_i` are the top predecessors and `v_j` the top successors.
Every intersection has size zero or one. The zero entries are the
good top pairs through the chosen output. Thus disjointness is
regular of positive degree

\[
h=t-(p-r)=r+t-p.
\]

All sets have size at most `c+1`, so (4) gives

\[
h\ge\left\lceil\frac{t}{C_c}\right\rceil,
\qquad
p\le r+t-\left\lceil\frac{t}{C_c}\right\rceil.
\]

The predecessor blocks partition the central class, so `t≤m`.
The integer-valued function `t↦t−ceil(t/C_c)` is nondecreasing.
Replacing `t` by `m` proves (1).

## 3. Examples and comparison with the sharper one-extra-vertex result

At `c=0`, formula (1) gives `p≤r+floor(r/2)`. The existing
minimal-central-class theorem gives the stronger description
`p=r+e`, where `e` is a proper divisor of `r`; the bound here
is consistent with it.

At `c=1`, the new formula is

\[
p\le2r+1-\left\lceil\frac{r+1}{6}\right\rceil.
\]

Here the additional fact that every nonempty cross-intersection has
size one improves the factor six to the sharp factor five, by the
[regular two-set theorem](1485_linear_two_set_regular_bound.md).
For `r≥4`, combining that theorem with the small-parameter
[one-extra-central-vertex theorem](1485_one_extra_central_first_output_gap.md)
gives

\[
p\le\min\!\left(2r-2,
2r+1-\left\lceil\frac{r+1}{5}\right\rceil\right).
\]

For example `r=15,m=16` gives `p≤27`, improving `p≤28`.
For `r=24,m=25`, it gives `p≤44`, improving `p≤46`.

At `c=2`, the constant is twenty. In particular `r≥59,m=r+2`
implies `p≤2r−2`, improving the ordinary row-local bound `2r−1`
throughout that range.

These inequalities do not by themselves exclude first-output
degrees five or six at minimum four with five central vertices.
