# Ordinary adjacency on the canonical blocks: proved bounds and remaining gap

**Update:** the gap discussed here is now closed in the
[full-core quotient theorem](1485_full_core_quotient.md). The new
ingredient is top-rectangle transport, which forces zero-or-`r`
neighbor counts before the saturation argument is applied. The
matrix-only counterexamples below remain valid and explain why
that extra ingredient was necessary.

Research note, 18 September 2026. Assume a finite E1485 magma has a
full central core of size `r²`. Let `A` be ordinary adjacency and `C`
canonical adjacency, now known to be sharp adjacency. The
[cyclic-block theorem](1485_full_core_cyclic_blocks.md) partitions the
carrier into `r²`-element blocks, with `C` carrying each block `I`
to `σI` and `C²` the complete relation from `I` to `σ²I`.

The results below are pen-and-paper necessary conditions. They do
**not** establish block congruence or the proposed matrix identity
`AC²=C²A`.

## Each ordinary block has row and column sums at most r

Fix a vertex `a` and a target block `J`. If `b` is an ordinary
successor of `a`, every path `a→b C c` is good. Consequently the
sets `C(b)`, as `b` ranges over `Row(a)`, are pairwise disjoint.
For `b∈J` they are `r`-element subsets of the same `r²`-element
block `σJ`. Hence

\[
|\operatorname{Row}(a)\cap J|\le r.                 \tag{1}
\]

The dual argument gives `|Col(a)∩J|≤r`. Thus every rectangular
block of `A` has each row and each column sum at most `r`.

The desired strengthening to sums **zero or `r`** has not been
proved. Constant total degree on each canonical block does not
automatically make the contributions from individual target blocks
constant.

## Multiplication by C makes degree-triangular matrices

Both `AC` and `CA` are zero-one matrices: every path they count
contains a sharp edge and therefore has its unique good middle.
Moreover

\[
(AC)_{ab}=1\Longrightarrow d(b)\le d(a),\qquad
(CA)_{ab}=1\Longrightarrow d(b)\ge d(a).           \tag{2}
\]

For example, a path `a→u C b` has `d(u)d(b)=n`, whereas the
ordinary edge bound gives `d(a)d(u)≥n`. Equality of endpoint
degrees forces the first edge sharp as well. The dual argument
handles `CA`. Thus the equal-degree part of **either** matrix is
exactly `C²`; the other entries strictly lower or raise degree.

This gives a potential finite degree-induction strategy, but no
induction step establishing block congruence is presently claimed.

## Saturation gives exact quadratic matrix identities

The good-return theorem gives `CAC=rΓ_T^T`, with `Γ_T` zero-one.
For fixed `a`, the `r` rows of `AC` indexed by `C(a)` are
therefore identical: their sum has only entries zero and `r`.
Put `X=AC`. For each vertex `b`,

\[
\begin{aligned}
(C^TCX)_{b*}
&=\sum_{a:b\in C(a)}\ \sum_{c\in C(a)}X_{c*}\\
&=\sum_{a:b\in C(a)}rX_{b*}=r^2X_{b*}.
\end{aligned}
\]

The column-dual calculation yields

\[
\boxed{C^TCAC=r^2AC,\qquad CAC C^T=r^2CA.}        \tag{3}
\]

These can also be read as equality cases of the Euclidean norm
contraction by the doubly stochastic matrix `C/r`.

Let `E` be the orthogonal averaging projection onto vectors constant
on each canonical block, and put `B=C/r`. The block description gives
an orthogonal decomposition into that constant subspace and its
orthogonal complement. On the first, `B` is the block permutation;
on the second its restriction `N` satisfies `N²=0`. It is a
contraction, but need not be zero and may have singular value one.
Thus (3) alone need not eliminate coupling between block-constant
vectors and those square-zero directions.

## The disconnected canonical blocks have exact component geometry

Write `C_i` for the `r²`-by-`r²` canonical adjacency block from
`X_i` to `X_{i+1}`. Then `C_iC_{i+1}=J`. In the bipartite graph
of `C_i`, a connected component has equally many left and right
vertices, since all degrees are `r`. If its vertex sets are `L,R`,
sum `C_iC_{i+1}=J` over the rows indexed by `L`, at any one target
vertex `z`. Every vertex of `R` has all its `r` predecessors in
`L`, giving

\[
|L|=r\,|C_{i+1}^{-}(z)\cap R|.
\]

Hence there is an integer `m` with

\[
|L|=|R|=rm,\qquad 1\le m\le r,                  \tag{4}
\]

and every next-block vertex has exactly `m` predecessors in `R`.
The component parameters `m` form a partition of `r`. A dual
statement describes predecessors of the left-side components.

On any one block, let `R_α` be the right vertex set of an incoming
canonical component, of size `rm_α`, and let `L_β` be the left
vertex set of an outgoing canonical component, of size `rn_β`.
These two partitions have the exact intersections

\[
\boxed{|R_\alpha\cap L_\beta|=m_\alpha n_\beta.} \tag{5}
\]

Indeed sum `C_{i-1}C_i=J` over the corresponding outer component
sets. There are `r²m_αn_β` outer pairs, each with one middle.
Every possible middle belongs to `R_α∩L_β` and contributes
exactly `r²` paths.

For `r=2`, a disconnected canonical bipartite block must therefore
be two copies of `K_{2,2}`. If both incoming and outgoing blocks
are disconnected, their two partitions meet in singletons: they
form a two-by-two coordinate grid. This describes the possible
isometric directions in the preceding section without assuming
that ordinary adjacency respects those coordinates.

For clarity, (3) also identifies exactly where block-row counts
can vary. Multiplying its first identity on the right by `C` and
using that `C²` maps the block-constant subspace onto itself gives
`CᵀC A E=r² A E`. Thus, for a fixed target block, the ordinary
row count is constant on every incoming canonical component of
the source block. This follows either from equality in averaging,
or from the elementary maximum principle on the connected
bipartite component. Dually, ordinary column counts are constant
on outgoing canonical components. The possible variation between
different components is the remaining issue.

## A small exact counterexample to a matrix-only shortcut

The following matrices concern only local incidence constraints;
they are **not** an E1485 magma or a counterexample to block
congruence. At `r=2`, take

\[
C_0=\begin{pmatrix}
1&1&0&0\\0&0&1&1\\1&1&0&0\\0&0&1&1
\end{pmatrix},\qquad
X=\begin{pmatrix}
0&0&0&0\\0&0&0&0\\0&0&0&1\\0&1&0&0
\end{pmatrix}.
\]

Then `C₀` is two-regular and `C₀²=J₄`. Direct multiplication gives

\[
C_0X=\begin{pmatrix}
0&0&0&0\\0&1&0&1\\0&0&0&0\\0&1&0&1
\end{pmatrix},\quad
XC_0=\begin{pmatrix}
0&0&0&0\\0&0&0&0\\0&0&1&1\\0&0&1&1
\end{pmatrix},
\]

\[
C_0XC_0=\begin{pmatrix}
0&0&0&0\\0&0&2&2\\0&0&0&0\\0&0&2&2
\end{pmatrix}.
\]

Thus both mixed products are zero-one and the three-factor product
has only entries zero and `r`. Nevertheless `X` has row sums
`0,0,1,1` and column sums `0,1,0,1`, rather than zero or `r`.
Also `X C₀²≠C₀² X`. The local zero-one and saturation conditions
therefore do not by themselves prove the desired block regularity
or commutation.

There is a second limitation even if commutation with block
averaging is supplied. For the same `C₀`, let `Y` be the
permutation matrix interchanging indices `1` and `2` and fixing
`0,3` (indices start at zero). Then

\[
YJ_4=J_4Y=J_4,\qquad C_0YC_0=2C_0,
\]

and `C₀Y,YC₀` are zero-one. Yet every row and column of `Y`
has sum one, strictly between zero and `r=2`. Thus even constant
row and column sums on an ordinary block, together with the local
mixed-product conditions, do not force sums zero or `r`. This
second example again describes only matrices, not an E1485 model.

An experimental check found `AC²=C²A` in all 390 archived order-eight,
order-sixteen and order-eighteen tables. That is evidence only; the
general identity remains a proof target.
