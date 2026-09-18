# Canonical-boundary three-edge paths have a unique top return

Research note, 18 September 2026. Assume a finite E1485 magma has
minimum degree `r` and a full central core `|Z|=r²`. Let `T` be
its top-degree class, also of size `r²`, and use the canonical
`r`-regular relation from the [full-core note](1485_full_central_core.md):

\[
C(x)=x*T,\qquad C^-(x)=T*x.
\]

This note does not assume that the sharp degrees are constant,
that there are only four translation degrees, or that arbitrary
products preserve a canonical component.

## Any ordinary edge supplies a top coordinate rectangle

Suppose `y→x` is an ordinary edge. By the ordinary predecessor
description, choose `v∈M` with `v*x=y`. There is no requirement
that `v` be top. For every `u∈T`, E1485 says

\[
(x*u)*(u*(v*x))=u,
\quad\text{so}\quad (x*u)*(u*y)=u. \tag{1}
\]

Thus

\[
u\longmapsto(x*u,u*y)
\]

is an injection from `T` into `C(x)×C^-(y)`, with left inverse
given by multiplication. Both finite sets have size `r²`, so it is
a bijection. In particular,

\[
\boxed{C(x)\times C^-(y)\longrightarrow T,
\qquad(a,b)\longmapsto a*b
\quad\text{is a bijection whenever }y\to x.} \tag{2}
\]

The inverse is exactly `(x*u,u*y)`, not merely an unspecified
coordinate parametrization.

Now consider a three-edge path with canonical boundary edges

\[
a_0\mathrel C a_1\to a_2\mathrel C a_3.
\]

Apply (2) with `y=a₁`, `x=a₂`: the pair `(a₃,a₀)` belongs to
`C(a₂)×C^-(a₁)`. Therefore

\[
\boxed{a_3*a_0\in T.} \tag{3}
\]

In particular this applies to every canonical three-edge path. The
middle edge need only be ordinary.

## The ordinary two-edge return is unique

Let `t=a₃*a₀∈T`. If `a₃→w→a₀` is any ordinary return
path, the strict degree-decrease theorem says either `w=t`, or
`d(w)>d(t)`. The latter is impossible because `t` has maximum
degree. Consequently the three-edge path has precisely
one ordinary two-edge return middle, namely `t`.

Writing `A` for ordinary adjacency, the exact entrywise statement is

\[
\boxed{(CAC)_{ab}>0\quad\Longrightarrow\quad
(A^2)_{ba}=1,
\text{ with its unique middle in }T.} \tag{4}
\]

Here `C` also denotes the zero-one adjacency matrix of the
canonical relation. Counting all `C-A-C` paths, using the row and
column sums `r` of `C`, gives the global trace identity

\[
\boxed{\operatorname{tr}(CACA^2)=r^2\sum_{a\in M}d(a).} \tag{5}
\]

The value one in (4) counts ordinary return middles, not canonical
three-edge paths; the entries of `CAC` need not be zero or one.
The useful all-canonical specialization is

\[
\operatorname{tr}(C^3A^2)=|M|r^3. \tag{5a}
\]

The strengthened ordinary-edge hypothesis is essential to the
[full-core sharp-regularity proof](1485_full_core_sharp_regularity.md):
the two interior path statuses in a `C-A-C` path agree, and one
can force either to be good by adjoining a sharp boundary edge.

## There are no canonical five-cycles

For this section assume additionally that the translation degree is
nonconstant, so `r<s` and the central and top classes are disjoint.

The canonical relation on `Z∪T` is bipartite: every central
canonical neighbor is top, and every top canonical neighbor is
central. The latter follows because a top vertex has `r` sharp
central neighbors, already exhausting its canonical neighbors.
There are no canonical edges between `Z∪T` and its complement.

Any canonical five-cycle in a noncore component would supply a
canonical three-edge path and a canonical two-edge return with a
non-top middle. This contradicts (4). The core component has no
odd cycle by bipartiteness. Hence

\[
\boxed{r<s\quad\Longrightarrow\quad\operatorname{tr}(C^5)=0.} \tag{6}
\]

The term “cycle” here includes closed directed walks with repeated
vertices, as required by the matrix trace.

The extra hypothesis is necessary. In the constant-degree case,
`n=r²` and `Z=T=M`; then `C=A`, `A²=J`, and
`tr(C⁵)=nr³`, not zero. The rectangle and unique-return statements
(1)--(5) remain valid in that case.

## Consequences in the four-degree setup

For the noncentral classes `A,H` of degrees `2r,b`, the canonical
matrix is

\[
C_0=\begin{pmatrix}0&P\\Q&R\end{pmatrix}.
\]

Its all-canonical cube has high-high block `KR+RK+R³`, where
`K=QP`. More generally the high-high block of `C₀A₀C₀`, for
ordinary noncentral adjacency `A₀=[[0,P],[Q,D]]`, is
`KR+RK+RDR`. Equation (3) therefore gives

\[
\boxed{\operatorname{supp}(RDR)\subseteq
\operatorname{supp}(G^T),} \tag{7}
\]

In particular this includes `supp(R³)⊆supp(G^T)`, in addition to
the already proved exact formulas
`RK=G^T diag(k)` and `KR=diag(k)G^T`.

The separate sharp-regularity proof now establishes `R=0` in this
four-degree setup. Neither argument asserts that canonical components
are closed under arbitrary products. Their divisibility by `r²` is
now proved separately by the [cyclic-block theorem](1485_full_core_cyclic_blocks.md),
which builds on the exact top-return counts above.
