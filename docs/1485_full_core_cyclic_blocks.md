# Full-core canonical components have cyclic blocks of size r squared

Research note, 18 September 2026. Assume a finite E1485 magma of order
`n` has minimum translation degree `r` and a full central core
`|Z|=r²`. The [full-core sharp-regularity theorem](1485_full_core_sharp_regularity.md)
identifies the canonical relation `C` with sharp adjacency. Thus `C`
is zero-one and `r`-regular in both directions. Let `A` denote
ordinary adjacency and `d(a)` the translation degree.

This note proves that every periodic class of every communicating
component of `C` has exactly `r²` elements. In particular `r²`
divides the size of each canonical component, and divides `n`.
It does not assume or prove that multiplication descends to these
blocks. This is a pen-and-paper theorem, not a Lean declaration.

## Exact top-return counts force identical rows

Let `Γ_T(a,b)=1` when `a*b` has maximum degree, and zero otherwise.
The [ordinary-edge rectangle theorem](1485_canonical_triples.md)
says that every `C-A-C` three-edge path has a top good return.
Conversely, if `d*a=t∈T`, the good-return fiber matching

\[
x\longmapsto x*d:
L_t^{-1}(a)=C(a)\longrightarrow R_t^{-1}(d)=C^-(d)
\]

parametrizes exactly `r` good-good three-edge paths from `a` to
`d`. Each has canonical boundary edges. Every `C-A-C` path is
good-good, because its boundary edges are sharp. Hence

\[
\boxed{CAC=r\Gamma_T^T.} \tag{1}
\]

The matrix `AC` is zero-one, since its two-edge paths contain a
sharp edge. Fix a vertex `a`. Its row in `CAC` is the sum of the
`r` rows of `AC` indexed by `C(a)`. By (1) each entry of this
sum is zero or `r`. It follows that all these selected rows are
identical:

\[
\boxed{b,c\in C(a)\quad\Longrightarrow\quad
(AC)_{b*}=(AC)_{c*}.} \tag{2}
\]

Dually, the columns of `CA` indexed by `C^-(a)` are identical.

## Extracting the same-degree part

Every sharp edge joins complementary degrees. Thus all vertices of
`C(a)` have degree `n/d(a)`. Also, if a path `b→x C y` has
`d(b)=d(y)`, its first edge is sharp as well: the sharp second
edge gives `d(x)=n/d(y)=n/d(b)`, so the first edge attains
equality in the ordinary edge-degree bound.

Consequently the equal-endpoint-degree part of `AC` is precisely
`C²`. Every other entry of `C²` is zero. The equalities in (2)
therefore imply

\[
\boxed{b,c\in C(a)\quad\Longrightarrow\quad
(C^2)_{b*}=(C^2)_{c*}.} \tag{3}
\]

There is no averaging across different degree classes in this step.
The two rows have the same endpoint degree, so the same set of
columns is retained in both.

## All normalized powers are uniform on r-squared points

Set `B=C/r`. This is doubly stochastic. Since `C²` is zero-one
and has row sum `r²`, every row of `B²` is uniform on exactly
`r²` vertices.

Equation (3) persists after right multiplication by any matrix.
In particular, for every `k≥2`, the rows of `B^k` indexed by one
set `C(a)` are identical. Therefore

\[
(B^{k+1})_{a*}
=\frac1r\sum_{b\in C(a)}(B^k)_{b*}
=(B^k)_{b*}\quad\text{for any }b\in C(a).
\]

Induction starting at `k=2` proves

\[
\boxed{\text{For every }k\ge2,\ B^k\text{ has only entries }
0\text{ and }1/r^2,
\text{ with exactly }r^2\text{ nonzero entries per row}.} \tag{4}
\]

The corresponding column statement follows either by duality or
from the column sums of these doubly stochastic matrices.

## The periodic classes all have size r squared

Because `C` has equal in-degree and out-degree at each vertex,
its communicating components are closed. Fix one such component,
and let its period be `p`. The standard finite directed-graph
period decomposition partitions it into classes

\[
X_0,X_1,\ldots,X_{p-1},
\]

with every edge going from `X_i` to `X_{i+1}` modulo `p`.
The row and column degree `r` shows that consecutive classes have
the same cardinality.

For completeness, the eventual-path property used here is the usual
finite irreducibility fact: for fixed vertices `x∈X_i` and
`y∈X_j`, all sufficiently large lengths congruent to `j-i`
modulo `p` occur as directed path lengths from `x` to `y`.
Equivalently, the restriction of `B^p` to each `X_i` is a finite
irreducible aperiodic stochastic matrix, whose sufficiently large
powers have all entries positive.

Choose a sufficiently large `k≥2` divisible by `p`. A row of
`B^k` indexed by `X_i` then has support exactly `X_i`. Equation
(4) says that its support has size `r²`. Thus

\[
\boxed{|X_i|=r^2\quad\text{for every periodic class}.} \tag{5}
\]

Since every two-step `C` path from `x∈X_i` ends in `X_{i+2}`,
and its `C²` row has exactly `r²` ones, (5) gives the stronger
exact description

\[
\boxed{(C^2)_{xy}=1
\quad\Longleftrightarrow\quad
x\in X_i,\ y\in X_{i+2}
\text{ within the same communicating component}.} \tag{6}
\]

In particular, two rows of `C²` are equal or disjoint, and the
equivalence classes of equal rows are exactly the periodic classes.
This is a canonical, choice-free partition into `r²`-element blocks.
On the blocks, `C` acts by a permutation `σ`, and `C²` is the
complete relation from each block to `σ²` of that block.

## Divisibility and degree restrictions

A component of period `p` has size `pr²`. Therefore

\[
\boxed{r^2\mid |X|\text{ for every canonical component }X,
\qquad r^2\mid n.} \tag{7}
\]

Each periodic block has constant translation degree: it is the
support of a row of `C²`, and a sharp two-edge path preserves
endpoint degree. Successive blocks have complementary degrees.
Hence an odd-period component can occur only in the self-complementary
degree `\sqrt n`; in particular, its existence implies that `n` is
a square. In the nonconstant-degree case, the no-canonical-five-cycle
theorem also excludes component periods one and five.

For a top parameter `t`, the maps `x↦x*t` and `x↦t*x` move
each periodic block respectively to `σ` and `σ^{-1}` of that
block, since their values are canonical successors and predecessors.
Their restrictions have fibers of size `r`, so each restricted
image has size `r`. This is compatible with, but does not yet prove,
a quotient multiplication on the blocks.

The subsequent [period-ten theorem](1485_full_core_period_ten.md) proves
`σ¹⁰=id` without assuming quotient compatibility. In the nonconstant
case each communicating component therefore consists of either two or
ten blocks, and `2r²` divides `n`.
