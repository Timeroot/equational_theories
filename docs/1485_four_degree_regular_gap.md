# Exact cardinality for sharp-regular full-core four-degree models

Research note, 18 September 2026. Assume a finite E1485 magma has a full
central core, minimum degree `r`, and exactly four translation degrees

\[
r,\quad 2r,\quad b,\quad 2b,
\qquad n=2rb,\quad b>2r.
\]

The [neighbor-gap theorem](1485_min_two_neighbor_gap.md) excludes
`2r<b<3r`. This note proves the following conditional classification:

**If every degree-`b` vertex has `r` sharp neighbors in each direction,
then `b=4r` and the order is `8r²=2(2r)²`.**

The proof first yields a gap and then an exact value; the filename
retains the earlier gap terminology. The separate
[six-times-square theorem](1485_six_times_square_full_core.md) excludes
the alternative `b=3r`. The present argument does not prove sharp
regularity or the full spectrum conjecture. No assertion here is a Lean
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

## Good closures force the remaining trace to vanish

The matrices `PD` and `DQ` are zero-one: they count two-edge paths
in `A∪H` containing a sharp edge, all of which are good. Their row
and column sums are `rd`.

Consider a three-edge path of class pattern `A,H,H,H` for which the
last two-edge path is good. Its first two-edge path is automatically
good. Close it by the unique good return. The five-cycle law makes all
five paths good. The return middle cannot be top: otherwise the path
through the last two high vertices and that top vertex would be good,
contrary to `H*T⊆A`, which follows from sharp regularity. It is
therefore high. This proves

\[
\operatorname{supp}(PE)\subseteq
\operatorname{supp}((DQ)^T).
\]

Each entry of `PE` is at most `r`, because `E` is zero-one and `P`
has row sum `r`. Its row sum is `r²d`, whereas the zero-one matrix
`(DQ)^T` has row sum `rd`. Equality therefore holds in every entry
bound on that support. The dual argument gives the other identity:

\[
\boxed{PE=r(DQ)^T,\qquad EQ=r(PD)^T.} \tag{7}
\]

Using `E=J-K` and `K=QP`, the first identity gives

\[
PQP=rJ-rQ^TD^T,
\qquad K^2=r^2J-rQQ^TD^T.
\]

Multiply by `D` and take traces. Since `DQ` is zero-one with `hdr`
entries equal to one,

\[
\begin{aligned}
\operatorname{tr}(DK^2)
 &=r^2hd-r\operatorname{tr}(QQ^TD^TD)\\
 &=r^2hd-r\lVert DQ\rVert_F^2=0.
\end{aligned} \tag{8}
\]

Every bad high path has an `A` replacement, so `F` is supported on
`K`. Each entry of `D²` is at most `d`; hence entrywise `0≤F≤dK`.
Nonnegativity of all matrices and (8) give

\[
0\le\operatorname{tr}(DFK)
\le d\operatorname{tr}(DK^2)=0.
\]

Equation (6) now forces `t(t-r)=0`, not merely `t≥r` when positive.
Thus `b=3r` or `b=4r`. The former has order `6r²` and is excluded by
the six-times-square theorem. Therefore

\[
\boxed{b=4r,\qquad n=8r^2=2(2r)^2.}
\]
