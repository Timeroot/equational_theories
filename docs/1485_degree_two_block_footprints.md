# Exact block footprints at degree twice the minimum

Research note, 18 September 2026. Assume a finite E1485 magma has a
full central core, minimum degree `r`, maximum degree `s`, and order
`n=rs`. Use the [sharp-regular canonical relation](1485_full_core_sharp_regularity.md)
`C`, ordinary adjacency `A`, and the
[canonical blocks](1485_full_core_cyclic_blocks.md), each of size `r²`.
The induced block permutation is `σ`. The central set `Z` and top set
`T` are individual blocks. These are pen-and-paper statements; no
quotient congruence is assumed.

The subsequent [full-core quotient theorem](1485_full_core_quotient.md)
proves block congruence in general and excludes degree `3r`. The local
identities below remain valid; the final projection obstruction records
the earlier state of this approach, not a remaining spectrum gap under
full core.

Put `H=AC`, `K=CA`, and let `Γ(x,y)=1` exactly when `x*y∈T`.
All entries of `H,K` are zero or one, because a two-edge path
containing a sharp edge is good. The established saturation identities are

\[
 CAC=r\Gamma^T,\qquad C^T\Gamma^T=rH,
 \qquad\Gamma^TC^T=rK.                            \tag{1}
\]

## Degree-2r footprints are two complete blocks

If `d(a)=2r`, its only ordinary neighbors are its `r` top neighbors
and its `r` sharp neighbors. Indeed complementary neighbor degrees
are occurring degrees at most `2r`, and the first degree gap leaves
only `r,2r`.

The canonical successor sets of different members of `Row(a)` are
disjoint, since every path counted by `AC` is good. The top neighbors
contribute all of `Z`, while the sharp neighbors contribute exactly
`C²(a)=σ²[a]`. Thus

\[
 \boxed{H_{ax}=1\iff x\in Z\cup\sigma^2[a]
 \qquad(d(a)=2r).}                               \tag{2}
\]

The column-dual statement is

\[
 \boxed{K_{xa}=1\iff x\in Z\cup\sigma^{-2}[a]
 \qquad(d(a)=2r).}                               \tag{3}
\]

These unions are disjoint. Also every product `a*x` is either top
or a sharp successor of `a`, and every `x*a` is either top or a
sharp predecessor. Therefore

\[
 \Gamma(a,x)+K_{ax}=1,\qquad
 \Gamma(x,a)+H_{xa}=1\quad(d(a)=2r).              \tag{4}
\]

For two degree-`2r` inputs, a non-top common middle necessarily
makes both edges sharp. Hence

\[
 \boxed{d(a)=d(b)=2r\quad\Longrightarrow\quad
 \begin{cases}
 a*b\in\sigma[a],&[b]=\sigma^2[a],\\
 a*b\in T,&[b]\ne\sigma^2[a].
 \end{cases}}                                    \tag{5}
\]

In the first case the product has degree `s/2`. Equation (5) is
block-determinacy for this restricted pair of degree classes, not a
claim about arbitrary products.

## Exact top-output rectangles for the complementary class

Let `d(u)=s/2`. Its sharp successors have degree `2r` and all
lie in `σ[u]`. Summing their identical rows (2) and using (1)
gives

\[
 \boxed{x*u\in T\iff[x]=Z\text{ or }[x]=\sigma^3[u].} \tag{6}
\]

More explicitly, the row of `CAC` at `u` is `r` times the
indicator of `Z∪σ³[u]`, and is also `r` times the column of
`Γ` at `u`.

Dually, summing (3) over the sharp predecessors of `u` gives

\[
 \boxed{u*x\in T\iff[x]=Z\text{ or }[x]=\sigma^{-3}[u].} \tag{7}
\]

Consequently the columns of `Γ` at degree `s/2`, and its rows
at that degree, are constant on every canonical block. No unproved
ordinary block equitability is used to obtain this.

## The degree-2r images in a fixed top projection family

Fix `t∈T` and write

\[
 P_a(x)=t*(x*a).
\]

Each `P_a` is an idempotent whose image has size `d(a)`, by sharp
regularity and the mixed-projection rank formula. There is the useful
exact description

\[
 \boxed{\operatorname{im}P_a
 =\operatorname{Row}(t)\cap\{x:K_{xa}=1\}.}        \tag{8}
\]

To check it, an image point `x` belongs to `Row(t)` and satisfies
`t*(x*a)=x`. The top-fiber description then says `x*a∈C(x)`,
which gives the path `x C (x*a)→a`. Conversely such a path is
good; since `t→x`, sharpness gives `t*(x*a)=x`, and idempotence
places `x` in the image.

Every top row meets every canonical block in exactly `r` vertices:
`L_t` maps the appropriate source block onto that intersection, and
its restricted fibers have size `r`. Combining this fact with (3)
and (8), for `d(a)=2r` we obtain

\[
 \boxed{\operatorname{im}P_a
 =(\operatorname{Row}(t)\cap Z)
 \sqcup(\operatorname{Row}(t)\cap\sigma^{-2}[a]).}  \tag{9}
\]

Both displayed pieces have size `r`. Thus these images really do
depend only on `[a]`, and distinct degree-`2r` blocks give distinct
images. This proves that special case of the general image-invariance
target.

For any parameters `a,b`, the fixed-left right regular band identity
also implies

\[
 \operatorname{im}(P_aP_b)
 =\operatorname{im}P_a\cap\operatorname{im}P_b.    \tag{10}
\]

Indeed `P_b` preserves `im P_a`; consequently the product image is
contained in both images. Every point in their intersection is fixed
by both factors and hence belongs to the product image.

## The former local obstruction at degree 3r

For `d(v)=3r`, the [local layer theorem](1485_degree_three_local_projections.md)
and global sharp regularity give

\[
 H_{v*}=1_Z+1_{\sigma^2[v]}+1_D,\qquad |D|=r^2,   \tag{11}
\]

where all elements of `D` have degree `2r`. Dually the support of
the column `K_{*v}` is `Z⊔σ⁻²[v]⊔D⁻`, with `|D⁻|=r²`
and all elements of `D⁻` of degree `2r`.

Equation (8) now shows, for every top `t`, that `im P_v` consists
of the `r` central points of `Row(t)`, its `r` points in
`σ⁻²[v]`, and exactly `r` points in `D⁻`. This does not yet
show that `D⁻`, or `D`, is one whole canonical block.

The specific missing step is to show that intersections of
`im P_v` with the degree-`2r` images (9) cannot contain just a
proper nonempty portion of the second `r`-point slice. Equation
(10) realizes such an intersection as the image of a product of
projections, but no theorem presently identifies that product image
with a single-parameter image. Degree gaps for translation ranks
therefore cannot simply be applied to it.

Nor may one assume that the projections have uniform fibers after
restriction to `Row(t)`: that assertion is false already in the
known order-eight tables. The note records the exact two-block
structure. The global quotient theorem resolves the degree-`3r` question
without needing this local projection-image argument.
