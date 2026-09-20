# Twenty internal edges with one failed rotation are impossible

Research finite graph lemma, 20 September 2026. The analytic reduction
below ends in a standard-Python check of 396 normalized cases and 676
search nodes, with no surviving graphs. No SAT solver or magma-table
enumeration is used. Its reduction, normalization, and search were
independently audited; this is not a Lean theorem.

The scope is the `K=20, τ=19` branch of the
[nine-central internal graph](1485_order_forty_nine_central_nonuniform_B.md).
The separate central-capacity and full-rotation arguments are needed to
deduce an exclusion of the whole nine-central case.

## 1. The graph statement and the unique boundary

**Lemma.** There is no binary matrix `D` on seven vertices, with equal
row and column degrees `2≤d_x≤4` and `Σd_x=20`, and permutation
matrix `Q_(x,σ(x))=1`, satisfying all three conditions:

- Entries of `D²` outside `Q` are at most one.
- Exactly nineteen internal two-edge paths have endpoint pair in `Q`.
- The one-`A` five-cycle identity holds:

  \[
  aDbDcDd,\quad Q_{da}=1
  \quad\Longrightarrow\quad Q_{ac}=Q_{bd}.              \tag{1}
  \]

In particular the lemma does not need a return-path capacity or the
all-`B` five-cycle condition.

Let `E` be the set of ordinary edges, and define the permutation of
ordered pairs

\[
 \phi(x,y)=(\sigma^{-1}(y),x),\qquad
 \phi^{-1}(x,y)=(y,\sigma(x)).
\]

For an edge `(x,y)`, its bad-successor indicator is
`β(x,y)=D_(y,σ(x))`. Thus it is one precisely when `(x,y)∈φ(E)`.
The hypothesis `K=20, τ=19` says that `E∩φ(E)` has nineteen
edges. Both edge sets have size twenty, so each of their differences
is a singleton.

The column degrees of `φ(E)` equal the row degrees of `E`,
hence equal the column degrees of `E`. The two differing edges
therefore share a column:

\[
 E\setminus\phi(E)=\{f\},\quad f=(r,c),\qquad
 \phi(E)\setminus E=\{(s,c)\},\quad r\ne s.              \tag{2}
\]

The row degree of `φ(E)` at `x` is `d_(σ(x))`. Consequently

\[
 d_x-d_{\sigma(x)}=
 \begin{cases}
 1,&x=r,\\-1,&x=s,\\0,&x\notin\{r,s\}.
 \end{cases}                                           \tag{3}
\]

Summing this difference around a permutation cycle shows that `r,s`
lie on the same cycle. Every other cycle has constant degree. On
the exceptional cycle there is one nonempty block of degree `d`
and one nonempty block of degree `d+1`, where `d=2` or `d=3`.
In particular `d_r≥3`.

The four possible degree multisets from `2≤d_x≤4` and `Σd_x=20`
are

\[
 (2,3^6),\quad(2^2,3^4,4),\quad(2^3,3^2,4^2),\quad(2^4,4^3).
\]

The last is already impossible by (3), since it contains no degrees
differing by one.

## 2. A forbidden shift at every vertex

The unique edge with `β=0` is `f`, whose first endpoint `r`
has degree at least three. Therefore every vertex has at least two
outgoing edges with `β=1`: at `r` there are `d_r−1≥2`,
and elsewhere there are `d_x≥2`.

Suppose `σ(u)Dσ⁻¹(u)`. For each of the at least two edges
`uDv` with `β(u,v)=1`, the latter equality supplies `vDσ(u)`.
Apply (1) to

\[
                    uDvD\sigma(u)D\sigma^{-1}(u).
\]

Its closing pair belongs to `Q`, and so does `(u,σ(u))`.
Thus `(v,σ⁻¹(u))` must belong to `Q`, forcing
`v=σ⁻²(u)`. This cannot hold for two distinct successors.
Relabeling `x=σ(u)` gives the global forbidden shift

\[
                       D_{x,\sigma^{-2}(x)}=0
                       \quad\text{for every }x.          \tag{4}
\]

This derivation does not assume that `σ` preserves degrees; indeed
(3) says that it does not preserve them on its exceptional cycle.

## 3. The only partially occupied orbit is prescribed

Let

\[
                    e=\phi^{-1}(s,c)=(c,\sigma(s)).
\]

On a cyclic orbit of `φ`, every proper occupied portion has an
entrance and an exit. Equation (2) therefore permits exactly one
partially occupied orbit. Its occupied segment is

\[
                         f,\phi(f),\ldots,e.             \tag{5}
\]

Thus `e` must occur on the orbit of `f`, and `φ(e)` must not
lie in the displayed segment. A one-edge segment is allowed. Every
other `φ` orbit is wholly occupied or wholly empty. The unoccupied
remainder of the exceptional orbit cannot be selected later.

## 4. Complete normalization

Relabel `r=0`. Let its permutation cycle have length `l≥2`,
and label this cycle successively `0,1,…,l−1`. Write `s=j`,
where `1≤j≤l−1`. Its degree list is exactly

\[
       (d+1,\underbrace{d,\ldots,d}_{j},
             \underbrace{d+1,\ldots,d+1}_{l-j-1}).
\]

For each of the remaining degree-two, degree-three, and degree-four
classes, choose a partition of its remaining number of vertices into
cycle lengths. List these homogeneous cycles in increasing degree,
then increasing length, and label each consecutively.

The remaining choice `c` in (2) can be normalized to:

- any position on the exceptional cycle;
- the first vertex of one representative homogeneous cycle for each
  distinct pair `(degree, cycle length)`.

Indeed homogeneous cycles may be rotated, and cycles of the same
degree and length may be interchanged, without disturbing any of the
fixed data. This gives all 396 cases; no fixed degree-preservation
assumption is imposed on the exceptional cycle.

As an independent control, the checker iterates every labeled
permutation and every degree list in `{2,3,4}^7` summing to twenty
whose unique degree descent is at zero. For each of the seven choices
of `c`, it explicitly relabels the cycles and verifies membership in
the normalized inventory. There are 141,120 such controls.

## 5. The exact orbit check

The [checker](../scripts/1485_m9_twenty_one_defect_check.py)
constructs (5), rejecting it if it does not terminate as required or
contains an edge forbidden by (4). It then lists all other `φ`
orbits, discarding any orbit containing an edge forbidden by (4).

It searches over the remaining whole orbits. It prunes only when:

- a row or column exceeds its prescribed degree;
- an entry of `D²` outside `Q` exceeds one.

Both failures are monotone under adding edges. At every recursion
node choose an unmet row, then branch on the first selected available
orbit meeting that row. The earlier such orbits are excluded in that
branch. Every completion has exactly such a first orbit, so the search
is exhaustive. Distinct orbits are disjoint, making the insertion and
removal operations exact.

The full inventory is:

| Degree multiset | Normalized cases | Recursion nodes | Complete graphs |
| --- | ---: | ---: | ---: |
| `(2,3⁶)` | 90 | 72 | 0 |
| `(2²,3⁴,4)` | 154 | 291 | 0 |
| `(2³,3²,4²)` | 152 | 313 | 0 |
| `(2⁴,4³)` | 0: excluded by (3) | 0 | 0 |
| Total | **396** | **676** | **0** |

All counts are asserted by the checker. Since no complete graph
survives even these necessary constraints, the lemma follows without
testing any additional five-walk patterns at the leaves.

## 6. Controls and reproduction

The orbit engine is also run on the known
[fifteen-edge intermediate fixture](1485_order_forty_nine_central_fifteen_edges.md):

\[
 \sigma(x)=x+1\pmod7,\qquad
 E=\{(x,x-1),(x,x+2):x\in\mathbf Z/7\}\cup\{(0,0)\}.
\]

With degrees `(3,2,2,2,2,2,2)`, exceptional segment `{(0,0)}`,
and its seven-cycle permutation, the same search must retain this
exact graph. This is a positive control for the partial-orbit engine,
not an example satisfying the twenty-edge hypotheses and not a magma.
An independent set-based evaluator verifies its margins, unique
rotation defect, repeated-middle bound, and forbidden shift. Deleting
its loop must fail both the margins and the unique-defect condition.

Run:

```sh
python3 scripts/1485_m9_twenty_one_defect_check.py
```

Add `--verbose` for per-case output. The initial complete run, including
the 141,120 normalization controls, took 7.60 seconds. Python's `-O`
mode is refused so that assertions cannot be silently disabled. The
script uses only the Python standard library and has no imports from
other project checkers.
