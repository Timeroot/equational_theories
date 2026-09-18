# The canonical block permutation has period dividing ten

Research note, 18 September 2026. Assume a finite E1485 magma has
minimum translation degree `r` and a full central core of size `r²`.
Let `T` be its maximum-degree class. The
[sharp-regularity theorem](1485_full_core_sharp_regularity.md) identifies
sharp adjacency with the canonical relation `C`. The
[cyclic-block theorem](1485_full_core_cyclic_blocks.md) partitions the
carrier into blocks of size `r²`, on which `C` acts by a permutation
`σ`. Write `[x]` for the block containing `x`.

**Theorem.** The block permutation satisfies `σ¹⁰=id`. If the
translation degree is nonconstant, each canonical communicating
component has either `2r²` or `10r²` vertices. In particular,
`2r²` divides the order of a nonconstant-degree full-core model.

This proof does **not** assume that multiplication respects the blocks.
Expressions such as `I*J⊆T` mean that every actual product of an
element of `I` and an element of `J` belongs to `T`; they do not
refer to an already constructed quotient multiplication. The proof is
a pen-and-paper result, not a Lean declaration.

## Two established facts in block notation

Canonical successors and predecessors have the block labels

\[
 y\in C(x)\Longrightarrow[y]=\sigma[x],\qquad
 y\in C^-(x)\Longrightarrow[y]=\sigma^{-1}[x].       \tag{1}
\]

Every canonical path of length at least two reaches the entire
appropriate target block. In particular, if `[y]=σ³[x]`, there is
a canonical three-edge path from `x` to `y`. The
[top-return theorem](1485_canonical_triples.md) therefore gives

\[
 \boxed{[y]=\sigma^3[x]\quad\Longrightarrow\quad y*x\in T.} \tag{2}
\]

Equivalently, `σ³I*I⊆T` for every block `I`.

We also use the canonical top-fiber descriptions: for a top
predecessor `t` of `b`, `L_t^{-1}(b)=C(b)`; for a top successor
`t` of `a`, `R_t^{-1}(a)=C^-(a)`.

## Top-valued products give two controlled block identities

Suppose `a*b=t∈T`. E1485 and its dual say, for every `z`,

\[
 t*(b*(z*a))=b,\qquad ((b*z)*a)*t=a.               \tag{3}
\]

The product path `a→t→b` shows that `t` is a top predecessor
of `b` and a top successor of `a`. Applying the top-fiber
descriptions to (3) gives

\[
 \boxed{a*b\in T\quad\Longrightarrow\quad
 b*(z*a)\in C(b),\qquad (b*z)*a\in C^-(a).}         \tag{4}
\]

In particular their blocks are `σ[b]` and `σ⁻¹[a]`, respectively.
No compatibility of general products with block labels is used here.

Finally, if `u→v` is any ordinary edge, choose `z` with `u*z=v`.
The dual identity gives, for every `w`,

\[
 \boxed{(v*w)*(w*u)=w.}                            \tag{5}
\]

We will use this only when the displayed edge is sharp.

## A second family of top rectangles

Fix a block `I`, an arbitrary `x₀∈I`, and an arbitrary
`x₇∈σ⁷I`. Choose `x₃∈σ³I` and a sharp successor
`x₄∈C(x₃)`, so `[x₄]=σ⁴I`. Set

\[
 w=x_0*x_7,\qquad p=w*x_3,\qquad q=x_4*w.
\]

By (2), both `x₃*x₀` and `x₇*x₄` are top-valued. Apply the
second conclusion of (4) to `(a,b,z)=(x₃,x₀,x₇)` and the
first conclusion to `(a,b,z)=(x₇,x₄,x₀)`. They give

\[
 p\in C^-(x_3),\quad [p]=\sigma^2I,
 \qquad
 q\in C(x_4),\quad [q]=\sigma^5I.
\]

Thus `[q]=σ³[p]`, and (2) gives `q*p∈T`. But (5), applied
to `x₃→x₄` with the parameter `w`, says `q*p=w`.
Since `x₀,x₇` were arbitrary, we have proved

\[
 \boxed{I*\sigma^7I\subseteq T\quad\text{for every block }I.} \tag{6}
\]

## Comparing two labels of one product

Keep `x₀∈I` and `x₇∈σ⁷I`, and choose sharp successors
`x₈∈C(x₇)` and `x₁∈C(x₀)`. Thus their blocks are `σ⁸I`
and `σI`. Put `v=x₈*x₀`.

Equation (5) for `x₇→x₈` gives

\[
 v*(x_0*x_7)=x_0.
\]

By (6), its second factor is top and is a successor of `x₀`.
The right top-fiber description therefore gives

\[
 v\in C^-(x_0),\qquad [v]=\sigma^{-1}I.            \tag{7}
\]

On the other hand, (5) for `x₀→x₁`, with parameter `x₈`,
gives

\[
 (x_1*x_8)*v=x_8.
\]

The first factor is top by (6), now applied to the block `σI`,
because `[x₈]=σ⁷[x₁]`. It is a predecessor of `x₈`, so
the left top-fiber description gives

\[
 v\in C(x_8),\qquad [v]=\sigma^9I.                 \tag{8}
\]

Equating (7) and (8) yields `σ⁻¹I=σ⁹I`. Since `I` was
arbitrary and `σ` is a permutation,

\[
 \boxed{\sigma^{10}=\mathrm{id}.}                  \tag{9}
\]

## Component sizes and the remaining quotient question

A canonical component with period `p` consists of a cycle of `p`
blocks. Equation (9) forces `p∣10`. In the nonconstant-degree
case there are no closed canonical walks of length five, by the
[canonical-path theorem](1485_canonical_triples.md). Therefore
`p=1` and `p=5` are impossible, leaving precisely `p=2` or
`p=10`. Each block has size `r²`, proving the component-size
and divisibility claims.

At the level of the block set, `σ⁵` is consequently an involution
and `σ²` has order dividing five. These are available candidates
for a Boolean complement and an order-five twist. This note does not
assert that either interacts with multiplication as those names would
require. Neither block congruence nor a constant-row quotient follows
from the period-ten argument alone. They have subsequently been proved
by the [separate quotient argument](1485_full_core_quotient.md), which
does not need the period-ten result.
