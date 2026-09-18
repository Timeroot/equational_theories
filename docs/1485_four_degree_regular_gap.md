# A four-degree gap under sharp regularity

Research note, 18 September 2026. Assume a finite E1485 magma has a full
central core, minimum degree `r`, and exactly four translation degrees

\[
r,\quad 2r,\quad b,\quad 2b,
\qquad n=2rb,\quad b>2r.
\]

The [neighbor-gap theorem](1485_min_two_neighbor_gap.md) excludes
`2r<b<3r`. This note proves the following additional conditional gap:

**If every degree-`b` vertex has `r` sharp neighbors in each direction,
then `b=3r` or `b≥4r`.**

The separate [scaled order-twenty-four argument](1485_six_times_square_full_core.md)
excludes `b=3r`.
The present count does not prove sharp regularity, an upper bound
`b≤4r`, or the full spectrum conjecture. No assertion here is a Lean
declaration.

## Four degree classes and a general cycle lemma

Write `Z,A,H,T` for the classes of degrees `r,2r,b,2b`. The full core
has `|Z|=|T|=r²`. Every vertex has `r` top neighbors in each direction,
and degree-`2r` vertices are sharp-regular. Their only non-top neighbors
are sharp neighbors in `H`.

Any two-edge path in `A∪H` which meets `A` is therefore good. A bad
two-edge path lying in `H` has its unique good replacement in `A`:
strict middle-degree decrease excludes both `H` and `T`, and its
endpoints cannot be adjacent to a central vertex.

Consider a five-cycle all of whose vertices lie in `H`, and record
whether each of its five two-edge paths is bad. The five-cycle law
prohibits an isolated bad position. Thus a mixed pattern has a single
block of two, three, or four bad positions.

In fact blocks of three or four are impossible, **without assuming
sharp regularity on `H`**. To see this, consider any mixed three-edge
path `a→b→c→d` in such a cycle and its unique good return middle
`e=d*a`.

* If `e∈A`, the three paths of the completed five-cycle that meet `A`
  are good. The other two statuses must then agree, contrary to the
  mixed hypothesis.
* If `e∈T`, strict middle-degree decrease says that there can be no
  other ordinary return middle at all, because no degree exceeds the
  top degree. This contradicts the existing return middle in `H`.
* Therefore `e∈H`. There can be no second ordinary return middle in
  `H`, since it would have the same degree as the good one. Hence the
  return path in the original high cycle is good.

Each block of three or four bad positions has a mixed adjacent pair
whose opposite return path is bad, contradicting this conclusion.
Consequently every high-only five-cycle has precisely

\[
\boxed{0,\ 2,\ \text{or }5\text{ bad positions}.} \tag{1}
\]

## Counts under sharp regularity

Now assume every vertex of `H` has sharp in-degree and out-degree `r`.
Counting sharp edges between `A` and `H` and then using the total order
gives

\[
|A|=|H|=h=r(b-r). \tag{2}
\]

Let `P,Q,D` be adjacency on `A→H`, `H→A`, and `H→H`.
The matrices `P,Q` have every row and column sum `r`, while `D` has
every row and column sum

\[
d=b-2r.
\]

The canonical auxiliary relation is now exactly the sharp relation.
An internal `H` edge has no good top extension. It has `2r` good
extensions in total, including all `r` sharp extensions into `A`.
It therefore has exactly `r` good high extensions and

\[
t=b-3r=d-r
\]

bad high extensions. The same counts hold for predecessors. In
particular `t≥0`.

Put `K=QP`. This zero-one matrix indicates the endpoint pairs in
`H×H` having a good middle in `A`; its row and column sums are `r²`.
Let `E` indicate the endpoint pairs having a good middle in `H`.
Good high-path counting gives row and column sums `dr` for `E`.
The supports of `K` and `E` are disjoint, and

\[
r^2+dr=r(b-r)=h.
\]

Consequently

\[
K+E=J_h. \tag{3}
\]

Every pair in `H×H` therefore has its product in `A∪H`; no such
pair has a top good middle. Define the nonnegative matrix

\[
F=D^2-E,
\]

whose entries count bad high two-edge paths.

## The two mixed-cycle counts

Let `N` count ordered high five-cycles whose two-edge paths at
positions zero and one are respectively bad and good. There are `hd`
choices of the shared edge, `t` bad high predecessors, and `r` good
high extensions. Such a mixed three-edge path cannot have its good
return middle in `A`, by the cycle argument above; by (3) its return
middle is therefore in `H`. It is the unique ordinary high return
middle. Hence

\[
N=h d t r. \tag{4}
\]

Let `B_0` count ordered high five-cycles whose paths at positions zero
and one are both bad and whose path at position three is good.
There are `hdt²` high three-edge paths with the first two paths bad.
If such a path has its return product in `H`, it contributes exactly
one cycle to `B_0`. If its return product lies in `A`, it contributes
none. The latter paths are counted by

\[
\operatorname{tr}(DFK).
\]

Indeed `DF` first selects the edge `a→b` and then a bad two-edge
path `b→c→d`, while `K_{da}=1` selects the good return through `A`.
That return forces the first two statuses to agree, so `a→b→c` is
also bad. This verifies both the count and its orientation. Therefore

\[
B_0=h d t^2-\operatorname{tr}(DFK). \tag{5}
\]

By (1), a mixed high five-cycle has exactly two consecutive bad
positions. Over its five rotations, it contributes once to `N` and
once to `B_0`. All-good and all-bad cycles contribute to neither.
Thus `B_0=N`. Equations (4)--(5) give

\[
\boxed{\operatorname{tr}(DFK)=h d t(t-r)\ge0.} \tag{6}
\]

If `t=0`, then `b=3r`. If `t>0`, nonnegativity and `h,d>0` force
`t≥r`, equivalently `b≥4r`. This proves the conditional gap.
