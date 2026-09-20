# Nine central elements: bounds on the remaining nonuniform seven-vertex graph

Research lemmas, 20 September 2026. These are analytic necessary conditions,
not an exclusion of the remaining nine-central case and not Lean theorems.
No graph enumeration or SAT result is used.

The [nine-central reduction](1485_order_forty_nine_central_reduction.md)
leaves seventeen tops, seven degree-five vertices `A`, and seven
degree-eight vertices `B`. Every member of `A` has top-profile size four.
Every member of `B` has sharp degree one and balanced top count `t_x`.
Let `D` be the ordinary adjacency matrix on `B`, and put

\[
 d_x=7-t_x,\qquad K=\sum_xd_x.
\]

The row and column degrees of `D` both equal `d_x`. Let `Q` be the
sharp two-step endpoint permutation, with `Q_(x,σ(x))=1`. An entry of
`D²` outside `Q` is at most one. For an ordinary edge `x→y`, write

\[
 \eta(x,y)=D_{\sigma^{-1}(y),x},\qquad
 \beta(x,y)=D_{y,\sigma(x)}.
\]

These are the two bad-extension indicators. Their sums over the edges
agree; write that common sum as `τ`. Thus `0≤τ≤K`. If `N` counts
top-valued products of two tops, the exact top-pair budget is

\[
                  N=-86+7K-\sum_xd_x^2+\tau\ge0.       \tag{1}
\]

Initially `0≤d_x≤4`. The reduction already proves `K≥15`.

**Theorem.** Every remaining candidate has

\[
                 15\le K\le20,\qquad 1\le d_x\le4,
                 \qquad 3\le t_x\le6.                 \tag{2}
\]

If `K=15`, its degree multiset is `(3,2,2,2,2,2,2)`, `N=0`,
and `τ=14`. Sections 3–4 supply the analytic reduction used by the
[subsequent ninety-case graph lemma](1485_order_forty_nine_central_fifteen_edges.md),
which now excludes that boundary case. Thus the combined bound is
`16≤K≤20`.

## 1. At most twenty internal edges

Each row of `D²` has six positions outside `Q`, of value at most
one, and its `Q` position has value at most `d_x`. Summing gives

\[
 \sum_xd_x^2=\sum_{x,y}(D^2)_{xy}\le42+K.
\]

Cauchy's inequality gives `K²/7≤42+K`, hence `K≤21`. Equality
at `K=21` forces all degrees to be three. That uniform case is
[already excluded analytically](1485_order_forty_nine_central_uniform_exclusion.md).
Therefore `K≤20`.

## 2. No isolated internal vertex: seven top neighbors are impossible

Suppose only `v≤6` vertices have positive internal degree. Every
internal two-step path has both endpoints in this active set. At an
active vertex `x`, if `σ(x)` is active, the row sum of `D²` is
at most `v−1+d_x`. If `σ(x)` is inactive, it is at most `v`,
which is also at most `v−1+d_x`, since `d_x≥1`. Consequently

\[
 \sum_xd_x^2\le v(v-1)+K\le30+K,
 \qquad K^2/6\le\sum_xd_x^2.
\]

Thus `K≤16`. Equation (1) now gives

\[
 N\le-86+8K-K^2/6\le-86+128-256/6=-2/3.
\]

The second inequality holds because `8K−K²/6` increases on
`0≤K≤16`. This contradicts `N≥0` and proves `d_x≥1`.

## 3. The fifteen-edge boundary has exactly one failed edge rotation

Suppose `K=15`. The least possible square sum is 33, attained only
by degrees `(3,2^6)`. Equation (1) gives `N≤34−Σd_x²≤1`.
The square sum is odd because `Σd_x²≡Σd_x=15 (mod 2)`, so
nonnegativity forces that minimum square sum. The
[one-top-product gap](1485_top_product_count_gap.md) rules out `N=1`.
Thus

\[
                    N=0,\qquad\tau=14.                 \tag{3}
\]

Let `h` be the unique vertex of degree three, and let `E` be the
set of edges of `D`. Define a permutation of ordered pairs by

\[
 \phi(x,y)=(\sigma^{-1}(y),x),\qquad
 \phi^{-1}(x,y)=(y,\sigma(x)).
\]

Exactly one edge `e` has `η(e)=0`, and exactly one edge `f` has
`β(f)=0`. Equivalently

\[
                  E\setminus\phi(E)=\{f\},\qquad
                  \phi(E)\setminus E=\{\phi(e)\}.
\]

The column degrees of `E` and `φ(E)` agree. Their row degrees
are respectively `d_x` and `d_(σ(x))`. If `σ(h)=h`, all
margins would agree, forcing the two distinct differing edges to have
both endpoints equal, impossible. Hence `σ(h)≠h`. Comparing
the two exceptional rows and their common column shows that, for some
vertex `a`,

\[
                 e=(a,h),\qquad f=(h,a).                 \tag{4}
\]

Thus the only failed predecessor rotation enters the degree-three
vertex; the only failed successor rotation leaves it. The possibility
`a=h` is not ruled out here.

## 4. The forbidden permutation shift also holds at fifteen edges

The [one-`A` five-cycle identity](1485_order_forty_nine_central_uniform_exclusion.md#1-the-general-finite-graph-lemma)
is valid without uniformity:

\[
 xDyDzDw,\quad Q_{wx}=1
 \quad\Longrightarrow\quad Q_{xz}=Q_{yw}.               \tag{5}
\]

At `K=15`, every vertex has at least two outgoing edges with
`β=1`: vertices other than `h` have two outgoing edges and no
exception, and `h` has three with exactly one exception. If
`D_(σ(x),σ⁻¹(x))=1`, choose any such outgoing edge `x→y`.
Its `β=1` supplies `y→σ(x)`. Apply (5) to

\[
                     x\to y\to\sigma(x)\to\sigma^{-1}(x).
\]

The closing `Q` entry and the first tested `Q` entry both equal
one. Therefore `Q_(y,σ⁻¹(x))=1`, forcing `y=σ⁻²(x)`.
This is impossible for two distinct choices of `y`. Relabeling
`u=σ(x)` yields

\[
                       D_{u,\sigma^{-2}(u)}=0
                       \quad\text{for every }u.         \tag{6}
\]

Unlike the uniform case, there is no established formula
`D²=J+2Q` here, so the uniform trace contradiction does not follow.
The uniform trace proof therefore cannot be reused directly. The
[separate tiny orbit classification](1485_order_forty_nine_central_fifteen_edges.md)
now excludes the fifteen-edge boundary; the other nonuniform cases are
not settled by the present note.
