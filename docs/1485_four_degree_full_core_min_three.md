# Four degrees and a full central core at minimum degree three

Research note, 18 September 2026. This proves a conditional extension
of the [minimum-degree-two four-degree theorem](1485_four_degree_min_two.md):

**Theorem.** A finite E1485 magma with minimum translation degree three,
exactly nine central vertices, and exactly four translation degrees is
sharp-regular and has order `72=2·6²`.

The nine-central-vertex hypothesis is essential to the scope of this
note: it is not established here for every minimum-degree-three model.
The proof uses the [full central core](1485_full_central_core.md), the
[neighbor-gap theorem](1485_min_two_neighbor_gap.md), and the
[sharp-regular four-degree cardinality theorem](1485_four_degree_regular_gap.md).
No assertion here is a Lean declaration.

## General four-degree notation

First allow any minimum degree `r` and assume `r²` central vertices.
The smallest larger degree is `2r`. If there are exactly four degrees,
reciprocity gives

\[
r,\quad 2r,\quad b,\quad 2b,
\qquad n=2rb,\quad b>2r.
\]

Write `A,H` for degrees `2r,b`, with cardinalities `m,h`. The central
and top classes have cardinality `r²`, so

\[
m+h=2r(b-r). \tag{1}
\]

Each vertex has `r` top neighbors in both directions. Vertices of `A`
have exactly `r` non-top neighbors, all sharp and in `H`. At a high
vertex `a`, reciprocal neighbor balance equates the sharp in-degree
and out-degree: after the identical top contributions are canceled,
their difference is multiplied by `1/(2r)-1/b`, which is nonzero.
Write the common sharp degree as `k_a`, where `1≤k_a≤r`.

Let `P,Q,D` denote adjacency on `A→H`, `H→A`, and `H→H`.
The first two relations are sharp, and

\[
\sum_{a\in H}k_a=mr,\qquad
D\mathbf1=D^T\mathbf1=(b-r-k_a)_{a\in H}. \tag{2}
\]

Use `C` for the canonical `r`-regular relation. Its internal part
`R=C∩(H×H)` has in-degree and out-degree `r-k_a`.

## A bound on endpoints with top product

Suppose `d*a=t` is top, with `a,d∈H`. The canonical-fiber identities
give two sets of size `r`:

\[
X=L_t^{-1}(a)=C(a),\qquad
Y=R_t^{-1}(d)=C^-(d).
\]

For `x∈X`, the weak central law gives

\[
(x*d)*(d*(t*x))=d.
\]

Since `t*x=a` and `d*a=t`, this says `(x*d)*t=d`, so `x*d∈Y`.
The dual law gives

\[
((d*a)*x)*(x*d)=x,
\quad\text{hence}\quad a*(x*d)=x.
\]

Consequently `x↦x*d` is injective from `X` to `Y`, with left inverse
`y↦a*y`. Equal finite cardinalities make it a bijection. Each matched
pair `x,y=x*d` is an ordinary edge `x→y`, and gives two good paths
`a→x→y` and `x→y→d`.

The sets `X,Y` contain respectively `k_a,k_d` vertices of `A`; their
other vertices lie in `H`. There is no ordinary edge `A→A`, because
`(2r)²<n=2rb`. Thus the `k_a` low members of `X` must match high
members of `Y`, and the `k_d` low members of `Y` must receive high
members of `X`. These are disjoint sets of matched edges, proving

\[
\boxed{d*a\text{ top}\quad\Longrightarrow\quad k_a+k_d\le r.}
\tag{3}
\]

In fact exactly `r-k_a-k_d` matched edges have both ends high.
Conversely, any high good-good three-edge path from `a` to `d`, closed
by its good top return, is an all-good five-cycle. It therefore belongs
to this matching. Hence `r-k_a-k_d` is the exact number of those
high good-good paths, not only a nonnegative bound.

## A moment identity when top returns are absent

Let `K=QP` indicate high endpoint pairs with a good middle in `A`;
let `E` indicate good high middles; and let `G` indicate top good
middles. All three matrices are zero-one, with disjoint supports, and

\[
K+E+G=J_h. \tag{4}
\]

Put `F=D²-E`, the matrix of bad high two-edge paths, and
`t=b-3r`. An internal edge outside `R` has `t` bad high extensions;
an edge in `R` has `t+r`. Indeed the total good-extension count is
`2r`; its top contribution is zero or `r`, respectively, and all
`k_a` sharp extensions into `A` are good. Therefore

\[
F\mathbf1=tD\mathbf1+r(r\mathbf1-k).
\]

Also `K1=rk`, while
`D²1=(b-r)D1-Dk`. Substituting in (4) gives the exact row formula

\[
\boxed{G\mathbf1=(r^2-m)\mathbf1+Dk.} \tag{5}
\]

Suppose now `G=0`. Sum (5), use (2), and expand:

\[
(m-r^2)h
=\mathbf1^TDk
=\sum_a(b-r-k_a)k_a
=(b-r)mr-\sum_a k_a^2. \tag{6}
\]

Define `x=h-m≥0` and `ℓ_a=r-k_a`. Equation (2) gives
`Σℓ_a=rx`. Combining (1) and (6) yields

\[
\sum_a k_a^2=r^2h-\frac{mx}{2}.
\]

On the other hand, expanding `(r-ℓ_a)²` gives
`Σk_a²=r²h-2r²x+Σℓ_a²`. Hence

\[
\boxed{G=0\quad\Longrightarrow\quad
\sum_a\ell_a^2=\frac{4r^2-m}{2}\,x,
\qquad \sum_a\ell_a=rx.} \tag{7}
\]

## Minimum degree three forces regularity

Now take `r=3` and suppose some high vertex is irregular. It has a
successor under `R`. Every bad high extension from a fixed high source
`a` ends in the set of endpoints of sharp paths `a⇒α⇒c` through
`A`. This set has exactly `r k_a` elements. An `R` edge has `b-2r`
bad high extensions, so

\[
b-6\le3k_a\le6.
\]

Thus `b≤12`. The degree gaps give `b≥9`, and degree-nine vertices
are sharp-regular. The irregular case consequently requires

\[
9<b\le12. \tag{8}
\]

No high vertex can have sharp degree one: it would have an `R` edge
and the same bound would give `b≤9`. Hence every `k_a` is two or
three. Equation (3) now excludes every top-return pair, since
`k_a+k_d≥4>3`. Thus `G=0`.

The quantities `ℓ_a=3-k_a` are zero or one. Therefore `Σℓ_a²=Σℓ_a=3x`.
If any high vertex is irregular, `x>0`; equation (7) then gives

\[
3=\frac{36-m}{2},\qquad m=30.
\]

But (1), together with `m≤h` and (8), gives

\[
m\le3(b-3)\le27,
\]

a contradiction. All high vertices are therefore sharp-regular.
The sharp-regular four-degree theorem forces `b=4r=12`, and the
order is `n=2rb=72`, completing the proof.
