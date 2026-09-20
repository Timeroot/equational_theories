# Order forty: full central blocks force at most six central elements

Research note, 20 September 2026. These are analytic finite E1485
restrictions, not Lean declarations. No enumeration or SAT premise is
used. The filename preserves the original ten-central-element scope;
the main reduction below is stronger.

Assume a finite E1485 magma has order forty, minimum degree four, and
central class `Z` of size `m≥5`. Write `T` for the top class and `h=|T|`.
For `v∈T`, put

\[
P_v=Z\cap Col(v),\qquad C_v=Z\cap Row(v).
\]

Call a block **full** if it has size four. The
[order-forty reduction](1485_order_forty_four_central_exclusion.md#4-precisely-what-remains-at-order-forty)
gives degree classes `4,5,8,10`, with every degree-five vertex a first
noncentral top output and equally many top predecessors and successors.
In particular that class is nonempty. The central-defect reductions
give `m≤10`.

**Theorem.** If any full block occurs, then `h=16`, every vertex has
four top predecessors and four top successors, and

\[
|P_v|=4\iff |C_v|=4\qquad(v\in T).
\]

Consequently the
[uniform-top-count theorem](1485_order_forty_uniform_top_counts.md)
gives `m≤6`. Thus **no full block occurs when `7≤m≤10`**.
Only §1 is needed for this theorem. Sections 2–3 preserve independent
incidence restrictions at `m=10`; they are no longer needed to exclude
that full-block branch.

## 1. A full predecessor block forces a full successor block

Suppose `|P_u|=4`. The general full-column argument in
[the second central-defect gap, §2](1485_second_central_defect_gap.md#2-the-branch-with-a-full-central-degree)
gives `h=16` and

\[
|TopSucc(x)|=4\qquad(x\in M).                         \tag{1}
\]

This part of that argument does not require the small-defect numerical
hypothesis of the later theorem there.

We first show that every **non-top** vertex also has four top
predecessors. This is immediate for central vertices. At degree five,
the common top count in the two directions, together with (1), gives
the assertion.
Let `b` have degree eight. Write `j^-`, `k^-`, `t^-` for its
numbers of degree-five, degree-eight, and top predecessors, and use
plus signs for successors. These are all its possible neighbor
degrees. The degree-five neighbors are sharp, so sharp-neighbor
existence gives `j^-,j^+≥1`. Consequently

\[
j^\pm+k^\pm+t^\pm=8,\qquad t^+=4.
\]

The central shadow bounds `t^-≥⌈m/4⌉≥2`, and `j^-≥1`
bounds `t^-≤7`. The
[reciprocal-neighbor identity](1485_two_degree_research.md#a-weighted-balance-identity)
equates the sums of `40/d` on its two neighbor sets. Their values
are `40+3j^\pm-t^\pm`, whence

\[
3(j^+-j^-)=t^+-t^-=4-t^-.
\]

Thus `t^-` is four or seven. In the latter case `j^-=1`, so the
identity forces `j^+=0`, a contradiction. Therefore `t^-=4`.

Now suppose `a=u*v` is noncentral for some top `v`. The general
full-block row argument from the same cited §2 gives

\[
|TopPred(a)|\le3.                                      \tag{2}
\]

For completeness, the four central predecessors `c` of `u` give
distinct vertices `v*c` exhausting `TopSucc(v)`. E1485 therefore
gives `a*b=v` for every `b∈TopSucc(v)`. In particular
`a*(v*z)=v` for every central `z`; the two-sided auxiliary identity
gives `(z*a)*v=a`. Thus `Z*a=TopPred(a)` lies in the top-input
part of the size-four fiber `R_v^{-1}(a)`. That fiber also contains
a non-top sharp predecessor of `a`, proving (2).

Since all non-top vertices have four top predecessors, (2) forces
`a` to be top. But `Z` is independent, so the
[arbitrary-product return-matching bound](1485_general_return_matching.md#2-an-independent-set-bound-including-the-equality-case)
at `u*v=a` gives

\[
|P_u|+|C_v|\le40/d(a)=4.
\]

Its left side is at least five. This contradiction proves `u*T⊆Z`.
The number of central-valued top pairs with first entry `u` is
`4|C_u|`; it is now all `h=16` pairs. Hence `|C_u|=4`.

Applying the same argument to the opposite magma proves the converse.
The full-row counterpart of (1) now gives four top predecessors at
**every** vertex as well. The uniform-top-count theorem therefore
applies and gives `m≤6`, completing the main theorem.

## 2. A general incidence bound: at most two full-full tops

This section only needs the central incidence axioms at minimum four
with ten central labels; it does not need order forty or §1. Namely,
the rectangles `P_v×C_v` partition `Z×Z`, each central row and column
has four tops, and any `P` block meets any `C` block in at most one
point.

Let `f` count tops with both blocks full. For `z∈Z`, let `r_z`
and `c_z` count full-full predecessor and successor blocks containing
`z`. A partition of ten into four positive parts contains at most two
parts of size four, so

\[
0\le r_z,c_z\le2,\qquad \sum_zr_z=\sum_zc_z=4f.
\]

Every global `P` block meets a full `C` block exactly once, and
dually. Indeed the four opposite blocks in any central partition
cover the full four-set, and each meets it at most once. Thus every
full-full predecessor block meets every full-full successor block
exactly once. It follows that

\[
\sum_zr_zc_z=f^2,\qquad
\boxed{\sum_z(2-r_z)(2-c_z)=40-16f+f^2\ge0.}           \tag{3}
\]

The first moments give `f≤5`, and (3) excludes `f=4,5`.

Suppose `f=3`. The sum in (3) is one, so there is exactly one
exceptional point with `(r_z,c_z)=(1,1)`; every other point has
`r_z=2` or `c_z=2`. Label the three full-full tops by `1,2,3`.
For each `i`,

\[
\sum_{z\in P_i}c_z=3.
\]

Let `n_i` count the points of `P_i` with `r_z=2`. Every other
point of `P_i` has `c_z=2`, except for the possible exceptional
point, whose value is one. Consequently `n_i≥3` if `P_i` misses
the exceptional point, and `n_i≥2` if it contains it. Since the
exception belongs to exactly one `P_i`, these lower bounds are
`2,3,3`, in some order.

Make a loopless multigraph on the three tops: a point with `r_z=2`
is an edge joining the two predecessor blocks that contain it.
Its degrees are the `n_i`, all at most four. Its underlying graph
must be the triangle. Otherwise a vertex is isolated, contrary to
the positive lower bounds, or the graph is a two-edge path whose
center has degree at least `2+3=5`. Thus every two predecessor
blocks intersect. The dual argument says every two successor
blocks intersect. Two distinct full-full rectangles therefore
overlap, contradicting the partition of `Z×Z`.

We conclude

\[
\boxed{f\le2.}                                         \tag{4}
\]

## 3. Two full tops contradict a first-output permutation matrix

Return to order forty with `m=10`, and suppose `f=2`, keeping only
the uniform-top-count conclusion of §1. All
full blocks belong to these two full-full tops. Their rectangles
are disjoint, so at least one pair of their predecessor or successor
blocks is disjoint. By duality assume their successor blocks `B_1`
and `B_2` are disjoint. Put

\[
W=Z\setminus(B_1\cup B_2),\qquad |W|=2.
\]

Every global predecessor block meets each `B_i` exactly once.
The two full predecessor blocks therefore both contain `W`, while
every nonfull predecessor block has size two or three. There are
fourteen nonfull tops, and their predecessor sizes sum to
`40-8=32`; hence exactly four have predecessor size three and ten
have size two.

Let `S` be the sum of the successor sizes at those four size-three
predecessor blocks, and `Q` the sum at the other ten nonfull tops.
The central incidence moments give

\[
S+Q=40-8=32,\qquad 3S+2Q=100-32=68.
\]

Thus `S=4`, and each of those four tops has a singleton successor
block. Every size-three predecessor block contains one point of
`W`. The central row at that point contains both full tops, whose
successor blocks already cover `B_1∪B_2`; its other two blocks
must be the singleton parts of `W`. Therefore

\[
\begin{array}{ll}
|P_v|=3 &\Longrightarrow C_v\text{ is a singleton in }W,\\
|P_v|=2 &\Longrightarrow P_v\cap W=\varnothing
\end{array}
\qquad(v\text{ nonfull}).                              \tag{5}
\]

Choose any degree-five vertex `a`. Its top predecessor and successor
sets `U,V` have size four, their respective `P` and `C` blocks
partition `Z`, and

\[
K_{uv}=|C_u\cap P_v|\qquad(u\in U,v\in V)
\]

is a permutation matrix. Neither profile contains a full top: a full
successor block would give a row of four ones, and a full predecessor
block would give a column of four ones.

The four nonfull `P` blocks indexed by `U` partition ten using parts
of size two or three. Exactly two thus have size three. By (5) their
`K` rows are indexed by singleton `C` blocks in `W`.

On the other hand the four nonfull `C` blocks indexed by `V` have
sizes at most three, and partition ten. Their sizes are `3,3,3,1`
or `3,3,2,2`, so at most one is a singleton. In particular `V`
contains at most one size-three-`P` top. By (5), only such a top
can have its `P` block meet `W`.

The two specified rows of `K` can therefore have a one only in that
single possible column of `V`. Their positive row sums force two
ones into the same column, contradicting the column sum one. This
independently excludes `f=2` at `m=10`.

## 4. The remaining ten-central-element branch

Sections 2–3 alone would leave exactly one full-full top. The global
uniform-top-count theorem eliminates that case too, using §1 and
without any of the further incidence analysis.

Together with the
[small-block reduction](1485_order_forty_ten_central_small_blocks.md),
the ten-central-element branch is therefore reduced to `h∈{17,18}`
with all central blocks of size at most three. Both are now excluded
by the [unified ten-central-element proof](1485_order_forty_ten_central_exclusion.md).
