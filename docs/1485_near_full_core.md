# A finite central core cannot be missing exactly one vertex

Research note, 18 September 2026. This is a pen-and-paper proof, not a
Lean declaration.

**Theorem.** Let `M` be a nonempty finite E1485 magma and let `r`
be its minimum translation degree. Its central set `Z` cannot have
cardinality `r²−1`.

The full-core conjecture `|Z|=r²` remains open in general: this
theorem excludes the nearest smaller possibility, not all smaller
cores. It uses the established finite degree, uniform-fiber,
sharp-neighbor, and good-path theorems. The proof does not assume full
core, a Boolean quotient, or equal sharp degrees at arbitrary vertices.

## 1. The missing central products form one rectangle

Suppose for contradiction that `m=|Z|=r²−1`. Central vertices exist,
so `r≥2`. Put `n=rs`, where `s` is the maximum translation degree,
and write `T` for the top class. The degrees are nonconstant, so
`Z∩T=∅`.

Let `B` be ordinary adjacency from `Z` to `T` and `C` adjacency
from `T` to `Z`. The [unrestricted incidence identities](1485_unrestricted_central_incidence.md)
give

\[
BC=J_m,\qquad K=CB\le J_T.
\]

The entry `K_xy` detects whether the product of the top vertices
`x,y` is central. Let `k⁺=C1`, `k⁻=Bᵀ1` be their central
out-degrees and in-degrees. Every entry lies in `[1,r]`.

For each central vertex, the sum of `k⁺` over its `r` top
successors is `m=r²−1`. Thus each of those entries is at least
`r−1`. Every top vertex has a central predecessor, so this holds
throughout `T`. Dually, every `k⁻` is at least `r−1`. Write

\[
k^+=r\mathbf1-u,\qquad k^-=r\mathbf1-v,
\]

where `u,v` are zero-one vectors. Set `h=|T|`, `E=Σu=Σv`, and
`I=Σuv`. Counting incidence and using `Σk⁺k⁻=m²` gives

\[
E=r(h-m),\qquad I=r^2(h-r^2)+1.
\]

If `a=h−r²`, then `I≥0` gives `a≥0` by integrality, whereas
`I≤E` gives `r(r−1)a≤r−1` and hence `a≤1/r`. Therefore

\[
|T|=r^2,\qquad |\operatorname{supp}u|
=|\operatorname{supp}v|=r,\qquad u^Tv=1.
\]

Put `U=supp u`, `V=supp v`, and `U∩V={w}`. The row and column
sums of `K` are `rk⁺` and `rk⁻`. Thus zeros can occur only in
`U×V`, and every row indexed by `U` has exactly `r` zeros. Hence

\[
\boxed{K=J_{r^2}-uv^T.}                         \tag{1}
\]

Precisely the pairs in `U×V` have noncentral products.

## 2. Every vertex has exactly `r` top neighbors in each direction

For `x∈M`, let `p` indicate its top predecessors. The unique good
path from each central vertex to `x` gives `Bp=1`. Multiplying
by `C` and using (1) yields

\[
|\operatorname{TopPred}(x)|\mathbf1
-|V\cap\operatorname{TopPred}(x)|u=r\mathbf1-u.
\]

Since `T\U` is nonempty, compare coordinates outside and then
inside `U`. The dual argument treats successors. Together they give

\[
\boxed{
\begin{aligned}
|\operatorname{TopPred}(x)|&=r,&
|V\cap\operatorname{TopPred}(x)|&=1,\\
|\operatorname{TopSucc}(x)|&=r,&
|U\cap\operatorname{TopSucc}(x)|&=1.
\end{aligned}}                                 \tag{2}
\]

In particular top adjacency `D` is `r`-regular, `Du=1`, and
`vᵀD=1ᵀ`. Thus the `r` sets `TopSucc(x)`, `x∈V`, partition
`T`, as do the `r` sets `TopPred(x)`, `x∈U`.

## 3. A top translation has exactly one noncentral exceptional input

Fix `b∈T`. For each top output `x∈TopPred(b)` of `R_b`,
its size-`r` fiber contains exactly the `k⁻_x` central predecessors
of `x`: all paths with a central endpoint are good. The number of
noncentral inputs in these fibers is therefore

\[
\sum_{x\in\operatorname{TopPred}(b)}(r-k^-_x)
=|V\cap\operatorname{TopPred}(b)|=1.
\]

Consequently there is exactly one **noncentral** input `e_b` such
that `e_b*b` is top. This counts inputs, not outputs or fibers.
The exceptional input is allowed to be top; no exclusion of
top-valued top products is needed.

## 4. Every column of the missing rectangle is constant

Fix `v∈V`, and first take `u∈U\{w}`. Since `u∉V`,
the set `Z∩Col(u)` of central predecessors of `u` has exactly
`r` elements. Each such `c` can be written `c=z*u` with
`z∈T`: choose a top predecessor of the central vertex `c`,
and use the good path `z→c→u`.

Put `b=v*c`, which is top because `c` is central. The central
path `b→c→u` gives `b*u=c`, so the map `c↦v*c` is
injective. Its `r` values belong to `TopSucc(v)`, which has
size `r` by (2); hence they exhaust that set.

The original E1485 identity now gives

\[
(u*v)*b
=(u*v)*(v*(z*u))
=v
\qquad(b\in\operatorname{TopSucc}(v)).           \tag{3}
\]

By (1), `u*v` is noncentral. For each fixed `b` in this
nonempty top-successor set, the unique noncentral exceptional input
of `R_b` therefore identifies `u*v` with `e_b`. In particular,
all `u∈U\{w}` have the same product with `v`, say `a`, and

\[
a*b=v\qquad(b\in\operatorname{TopSucc}(v)).     \tag{4}
\]

To include `u=w`, choose any `c∈Z∩Col(w)`. Such a `c`
exists because that set has size `r−1>0`. Again write `c=z*w`
with `z∈T`, and put `b=v*c∈TopSucc(v)`. E1485 gives
`(w*v)*b=v`. Both `w*v` and `a` are noncentral, and (4)
gives `a*b=v`. Uniqueness of the exceptional input of `R_b`
forces `w*v=a`.

We have proved the full-column identity

\[
\boxed{u*v=a\quad\text{for every }u\in U,}
\qquad a\notin Z.                              \tag{5}
\]

## 5. The constant column overfills a top fiber

The fiber `R_v^{-1}(a)` has size `r`, since `v` is top.
Equation (5) already puts all `r` top vertices of `U` in it.

Choose a sharp predecessor `f⇒a`, which exists by the finite
sharp-neighbor theorem. As `a=u*v`, there is an ordinary edge
`a→v`. The path `f⇒a→v` is good, so `f*v=a` as well.

This `f` is not top. Indeed sharpness gives `d(f)d(a)=n`;
if `d(f)=s`, then `d(a)=r`, contradicting `a\notin Z`.
Thus the fiber contains `U∪{f}`, with `r+1` distinct elements.
This contradicts uniform fiber size `r` and proves the theorem.

## Appendix: the incidence completion alone is consistent

The contradiction genuinely uses multiplication and finite fibers,
not just the central incidence equations. To see what those equations
permit, adjoin a formal central point `★` and put

\[
\widehat B=\begin{bmatrix}B\\v^T\end{bmatrix},
\qquad\widehat C=\begin{bmatrix}C&u\end{bmatrix}.
\]

Both square matrices are `r`-regular. The incidence identities give

\[
\widehat B\widehat C=\widehat C\widehat B
=\widehat B D=D\widehat C=J_{r^2}.
\]

These matrices define a genuine full-core E1485 magma on
`(Z∪{★})⊔T`: use adjacency `[[0,B̂],[Ĉ,D]]` and declare a
two-edge path good unless all three vertices are top. The four
matrix identities give unique good middles for the four endpoint
types. A bad path cannot be isolated on a five-cycle: its two
neighboring good paths would force the remaining two vertices to
be adjacent central vertices, which is forbidden. Every edge is
supported by a good path because top vertices have central neighbors.
Thus the good-path graph construction applies.

This completion agrees with the given operations involving original
central vertices and on central-valued top pairs; it sends the
missing rectangle to `★`. It is not a quotient or submagma of
the hypothesized original model. The proof above excludes replacing
that single central value by actual noncentral outputs while retaining
the required finite structure.
