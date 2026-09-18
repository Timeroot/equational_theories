# Full central core gives a Boolean quotient and square-or-double-square order

Research note, 18 September 2026. **Theorem:** let a finite E1485 magma
have order `n`, minimum translation degree `r`, and exactly `r²`
central vertices. Then

\[
\boxed{n=r^2 2^m\quad\text{for some integer }m\ge0.} \tag{1}
\]

More precisely, the canonical `r²`-element blocks form a magma
congruence. Their quotient has a constant row and column and is
therefore a Boolean NAND algebra twisted by an automorphism of order
dividing five. The quotient map reflects goodness of two-edge paths.

Consequently a full-core model has square or twice-square order.
This applies unconditionally at minimum degree two, where
[full central core is proved](1485_two_central_exclusion.md), and
also at minimum degree one. **Full central core is not proved for
arbitrary minimum degree**, so this is not yet a proof of the entire
spectrum conjecture. These are pen-and-paper results, not new Lean
declarations.

## Established ingredients and notation

Let `A` be ordinary adjacency and `C` canonical adjacency. The
[full-core sharp-regularity theorem](1485_full_core_sharp_regularity.md)
proves that `C` is precisely sharp adjacency and is `r`-regular in
both directions. Thus `AC` and `CA` are zero-one matrices: every
path they count contains a sharp edge and has its unique good middle.

The [cyclic-block theorem](1485_full_core_cyclic_blocks.md) partitions
the carrier into blocks of size `r²`, with a permutation `σ` of the
blocks. Canonical edges go from `I` to `σI`, and every canonical
path of length at least two reaches the entire appropriate target
block. In particular, `C²` is the complete relation from `I` to
`σ²I`. Translation degree is constant on each block; denote it
by `d(I)`.

Let `T` and `Z` be the top and central classes. Each has size `r²`
and is a single canonical block: two sharp steps from a central
vertex reach `r²` central vertices, hence all of `Z`, and similarly
for `T`. In the constant-degree case these blocks coincide.

We need two established top-return facts. First,

\[
\boxed{\sigma^3I*I\subseteq T\quad\text{for every block }I.} \tag{2}
\]

Indeed a canonical three-edge path between the endpoints has top
good return. This is a statement about all actual products of
representatives, not an already assumed quotient operation.

Second, if `a*b` is top, the weak central law, its dual, and the
top-fiber descriptions give, for every `y`,

\[
\boxed{b*(y*a)\in C(b),\qquad (b*y)*a\in C^-(a).} \tag{3}
\]

For example `(a*b)*(b*(y*a))=b`; since `a*b` is a top predecessor
of `b`, its fiber at `b` is exactly `C(b)`. The other statement
is dual. Finally the exact good-return count is

\[
\boxed{CAC=r\Gamma_T^T,}                          \tag{4}
\]

where `Γ_T(a,b)=1` exactly when `a*b∈T`. Every entry of `CAC`
is therefore zero or `r`.

None of the arguments below assumes block congruence. They do not
need the separately proved bound on the order of `σ`.

## Top rectangles force zero-or-r neighbor counts

Fix a vertex `w` and a block `J`. Suppose `w` has an ordinary
successor `q∈J`. By the equivalent column definition of adjacency,
there is `y` with `y*q=w`.

For every `l∈σ⁻³J`, equation (2) gives `q*l∈T`. Apply the first
part of (3), with `(a,b)=(q,l)`. It gives

\[
l*w=l*(y*q)\in C(l).
\]

Thus `l→l*w→w` has its first edge canonical, and
`(CA)_{lw}=1` for **every** `l` in the `r²`-element block `σ⁻³J`.
Summing these entries counts each ordinary predecessor of `w` in
`σ⁻²J` exactly `r` times, once for each of its canonical
predecessors. Consequently

\[
\operatorname{Row}(w)\cap J\ne\varnothing
\quad\Longrightarrow\quad
|\operatorname{Col}(w)\cap\sigma^{-2}J|=r.         \tag{5}
\]

Here is the dual argument explicitly. If `q∈K` is an ordinary
predecessor of `w`, choose `y` with `q*y=w`. For every
`l∈σ³K`, equation (2) gives `l*q∈T`. The second part of (3)
then gives `w*l=(q*y)*l∈C⁻(l)`, so `(AC)_{wl}=1` for all such
`l`. Summing over their block proves

\[
\operatorname{Col}(w)\cap K\ne\varnothing
\quad\Longrightarrow\quad
|\operatorname{Row}(w)\cap\sigma^2K|=r.            \tag{6}
\]

Apply (6) to the nonempty predecessor set supplied by (5), and
conversely apply (5) to the successor set supplied by (6). We obtain
the exact transport relation

\[
\boxed{
|\operatorname{Row}(w)\cap J|
=|\operatorname{Col}(w)\cap\sigma^{-2}J|
\in\{0,r\}.}                                    \tag{7}
\]

In particular, every row and every column of every ordinary
adjacency block has sum zero or `r`.

## Every nonempty ordinary adjacency block is r-regular

Let `X=A_{I,J}` be an ordinary adjacency block. Let `L` be the
canonical block from `σ⁻¹I` to `I`, and `R` the canonical block
from `J` to `σJ`. Both are `r`-regular square matrices of size
`r²`.

The matrices `XR` and `LX` are zero-one, as restrictions of `AC`
and `CA`. A row of `XR` has sum `r` times the corresponding row
sum of `X`, hence zero or `r²` by (7). Therefore each active row
of `XR` consists entirely of ones. Dually every active column of
`LX` consists entirely of ones. If `u` indicates the active rows
of `X` and `v` its active columns, this says

\[
XR=u\mathbf1^T,\qquad LX=\mathbf1v^T.
\]

Consequently

\[
LXR=(Lu)\mathbf1^T=\mathbf1(v^TR)
\]

is constant along every row and every column, hence is a constant
matrix `λJ`. It is a block of `CAC`, so (4) gives `λ=0` or `r`.
If `X` is nonzero, regularity of `L,R` makes `LXR` nonzero, and
therefore `λ=r`.

Now `Lu=r1` forces every row of `X` active. Otherwise choose a
canonical predecessor of an inactive row index; the corresponding
row of `Lu` would have at most `r−1` contributing ones. The dual
argument forces every column active. Hence

\[
\boxed{A_{I,J}\text{ is either zero or r-regular}.} \tag{8}
\]

This is the additional conclusion that the earlier matrix-only
constraints did not yield: the top-rectangle transport (7) is
essential before applying saturation.

## The unique minimum-degree middle makes the partition a congruence

Define a directed edge between blocks `I→J` when `A_{I,J}` is
nonzero. For any two blocks `I,J`, at least one common intermediate
block exists: choose actual representatives `a∈I,b∈J`; their
product supplies the path `a→a*b→b`.

Among all blocks `K` with `I→K→J`, choose one of minimum
translation degree. Every actual path from `I` through `K` to
`J` is good. Otherwise the strict minimum-degree-middle theorem
would replace its middle by a vertex in a smaller-degree block
`K'`, still with `I→K'→J`, contradicting minimality.

Thus the matrix

\[
A_{I,K}A_{K,J}
\]

has every entry at most one: two middles would both be good,
contradicting uniqueness of the product. Both factors are
`r`-regular by (8), so every row of their product has sum `r²`.
There are exactly `r²` columns, and consequently

\[
\boxed{A_{I,K}A_{K,J}=J.}                        \tag{9}
\]

Every pair of representatives `a∈I,b∈J` therefore has its
product in `K`. A second minimum-degree intermediate block would
give a second good middle for every pair, which is impossible.
In particular the product block is unique and depends only on
`I,J`, not on the representatives.

Define `I⋆J=K`. The projection onto blocks is now a surjective
magma homomorphism, and the quotient satisfies E1485. This proves
congruence rather than assuming it in the minimum-degree argument.
Moreover (9) proves goodness reflection: whenever `I→K→J` is
a good quotient path, **every** actual path with its middle in
`K` is good.

## Constant row in the quotient and the spectrum conclusion

Every product with a central factor is top. Hence the quotient has

\[
Z\star I=I\star Z=T\qquad\text{for every block }I.
\]

It has a constant row and column. The proved
[constant-row classification](1485_spectrum_research.md#4-classification-of-the-constant-rowcolumn-case)
identifies any such E1485 magma with Boolean NAND twisted by an
automorphism whose fifth power is the identity. In particular a
finite quotient has `2^m` elements for some `m≥0`.

Each fiber of the quotient has `r²` elements, so

\[
n=r^2 2^m.
\]

If `m=2k`, this is `(r2^k)²`; if `m=2k+1`, it is
`2(r2^k)²`. This proves the stated square-or-double-square order
theorem under full central core.

## Exact degree spectrum and multiplicities

The ordinary graph of the quotient is exactly the nonzero-block
graph used above. Indeed an actual product supplies an ordinary
edge, and conversely every ordinary edge comes from some product.
Since each nonzero adjacency block contributes exactly `r`
successors to each of its source vertices, a vertex in block `I`
has degree

\[
d(a)=r\,d_Q(I),                                  \tag{10}
\]

where `d_Q` is the translation degree in the quotient.

In a Boolean algebra with `m` atoms, twisted NAND
`x⋆y=¬(τx∧τ⁻¹y)` has row degree `2^j` when `x` contains `j`
atoms. The automorphism `τ` only permutes atoms. Exactly
`binom(m,j)` Boolean elements contain `j` atoms, and each quotient
element has `r²` lifts. Thus the full degree distribution is

\[
\boxed{
\{d(a):a\in M\}=\{r2^j:0\le j\le m\},\qquad
\#\{a:d(a)=r2^j\}=r^2\binom mj
\quad(0\le j\le m).}                             \tag{11}
\]

In particular **no full-core model has a vertex of degree `3r`**,
answering the local extraction question without assuming that any
ordinary row is a submagma. The quotient construction, not a row
restriction, supplies the needed smaller E1485 algebra.

The outstanding general hypothesis is still `|Z|=r²`. None of the
arguments above supplies it for arbitrary finite E1485 magmas.
