# Minimum degree three cannot have five central vertices

Research note, 18 September 2026. This is a pen-and-paper finite
exclusion, not a Lean declaration. It uses the earlier analytic
[nine-top reduction](1485_five_central_nine_top.md), but does **not**
depend on the [bounded incidence scan](1485_five_central_residual_scan.md).
That scan suggested the binary matrix structure proved below directly.

**Theorem.** A finite E1485 magma with minimum translation degree three
cannot have exactly five central vertices.

The nine-top reduction gives nine top vertices, with central in/out
profile `1(1,1), 2(1,2), 2(2,1), 4(2,2)`. We prove directly that
its central-product matrix compares two binary types. Its least
noncentral translation degree must then be six. Next its first
noncentral top-top output must have degree nine and at least four
good top endpoint pairs. Equality in the general product-degree bound
forces those pairs to form a matching, so there can be at most three.

## 1. The central-product matrix has only two binary types

Let `P_t,C_t` be the central predecessor and successor sets of a top
vertex `t`. Let

\[
A=\{t:|P_t|=1\},\qquad E=\{t:|C_t|=1\}.
\]

Both sets have size three and their intersection is a single vertex
`o`. Write `P_o={p}`, `C_o={q}`. For a central label `z`, put

\[
\alpha_z=\#\{a\in A:P_a=\{z\}\},\qquad
\beta_z=\#\{b\in E:C_b=\{z\}\}.
\]

### 1.1. Ordinary top adjacency is three-regular

Write `B:Z→T`, `C:T→Z`, and let `D:T→T` be ordinary adjacency.
Set `K=CB` and `F=J−K`. The standard identities give
`BC=J`, `BD=DC=J`, and `K≤J`.

The [packing bound](1485_boundary_central_defect.md) gives at least
three top successors at every top vertex, because all central
in-degrees are below three and `5≤2|TopSucc(t)|`. Summing `BD=J`
over all its entries gives

\[
45=\sum_{t\in T}|P_t|\,|TopSucc(t)|
\ge3\sum_{t\in T}|P_t|=45.
\]

Every top vertex therefore has exactly three top successors. The
dual proof gives exactly three top predecessors. Since the central
sets on each such neighborhood partition the five central labels,
every row of `D` has exactly one successor in `E`, and every
column of `D` has exactly one predecessor in `A`.

### 1.2. Missing products transmit the singleton labels

Fix a top target `v∉A`, so `|P_v|=2`. Its missing column in `F`
has three entries, and their predecessor sets partition `Z`: this is
the column of `BF=1(3\mathbf1-|P|)^T` corresponding to `v`.
They are two disjoint pairs and one singleton `{z}`, belonging to
a unique missing input `a∈A`.

For a missing input `u`, its E1485 witness set is

\[
S_{u,v}=\{v*c:c\in P_u\}
=\{b\in TopSucc(v): C_b\cap P_u\ne\varnothing\}.
\]

It has size `|P_u|`, and `(u*v)*b=v` throughout it. The two
size-two witness sets intersect inside the three-element set
`TopSucc(v)`. At an intersection witness, the size-three fiber of
`R_b` at `v` already has two central inputs, forcing the two
noncentral products to agree. Their common product has at most two
top inputs under `R_v`, because its fiber also contains a non-top
sharp predecessor. Thus the remaining singleton witness cannot
meet either size-two witness set. The two size-two sets must coincide.

Let `b` be the remaining top successor of `v`. Its nonempty central
successor set avoids the two predecessor pairs, so it is exactly
`{z}`. In particular `b∈E`, and it is the unique `E` successor
of `v`. We have proved:

> For every `v∉A`, the label of its unique missing input in `A`
> equals the label of its unique ordinary top successor in `E`.

The reversed statement holds by duality.

### 1.3. All singleton labels coincide

Each `b∈E` has precisely two ordinary top predecessors outside
`A`, by §1.1. The preceding label rule therefore gives

\[
\#\{(a,v):a\in A,\ P_a=\{z\},\ v\notin A,\ F_{av}=1\}
=2\beta_z.
\]

On the other hand, a row `a∈A` of `F` has size six when `a=o`
and size three otherwise. Subtracting its entries in the three
columns `A` yields

\[
\boxed{
2\beta_z=3\mathbf1_{z=p}
 +\sum_{a\in A:P_a=\{z\}}\ \sum_{c\in C_a}\alpha_c.
}                                                     \tag{2}
\]

Indeed `K_{at}=1` for `t∈A` exactly when its singleton label
belongs to `C_a`. Duality gives

\[
\boxed{
2\alpha_z=3\mathbf1_{z=q}
 +\sum_{b\in E:C_b=\{z\}}\ \sum_{c\in P_b}\beta_c.
}                                                     \tag{3}
\]

Nonnegativity shows `β_p≥2` and `α_q≥2`. If `p≠q`, the
three available singleton labels, including those of `o`, force
`α_p=1`, `α_q=2`, `β_p=2`, and `β_q=1`. In (2) at `z=p`,
only `a=o` contributes, giving the contradiction `4=3+2`.

Thus `p=q`. Equations (2) and (3), retaining just the contribution
of `o`, give

\[
2\beta_p\ge3+\alpha_p,\qquad
2\alpha_p\ge3+\beta_p.
\]

Their sum gives `α_p+β_p≥6`. Each is at most three, so both
are three. Every singleton predecessor set and every singleton
successor set is therefore the same set `{p}`.

### 1.4. Every predecessor pair crosses every successor pair

The three tops in `A` exhaust the central row at `p`, and the
three in `E` exhaust its central column. Hence all other `P_t`
and `C_t` are pairs in the four-element set `Z\{p}`.

Every occurring successor pair occurs together with its complement
in that four-element set. To see this, choose a top carrying the
pair and any one of its central predecessors. Its central row has
three tops whose successor sets partition `Z`; besides the chosen
pair they must be `{p}` and its complementary pair.

An occurring predecessor pair cannot equal any successor pair,
because `K≤J`. Nor can it be disjoint from a successor pair:
it would equal the latter's occurring complement. It therefore
meets every successor pair exactly once. Consequently

\[
\boxed{K_{uv}=1
\iff (u\in E\text{ and }v\in A)
\text{ or }(u\notin E\text{ and }v\notin A).}
\]

This is the required binary-type matrix, obtained without classifying
the individual pair lists or the compatible matrices `D`.

## 2. Every vertex has three top neighbors in each direction

For every vertex `a`, the predecessor sets `P_t`, as `t` runs through
the top predecessors of `a`, partition the five central points. This
is the usual central-endpoint uniqueness identity `B p_a=1`.
All singleton sets are `{p}`, and all other sets are pairs avoiding
`p`. A partition must therefore use one singleton and two pairs.
Hence `a` has exactly three top predecessors.

Dually, the sets `C_t` over its top successors partition the five
central points. Here the only singleton set is `{p}`, and all other
sets have size two and avoid `p`. A partition therefore consists of
one singleton and two pairs. Thus `a` has exactly three top successors
as well. This statement concerns every vertex of the magma, not only
the nine top vertices.

## 3. An odd square binary-type matrix has no intermediate regularity

Consider any `3×3` submatrix of `K` with equal row sums and equal
column sums, all equal to `e`. If its selected rows include both
binary types and `b` selected columns have type zero, then its two
possible row sums are `b` and `3−b`. Equality would require
`b=3/2`, which is impossible.

Thus all selected rows have the same type. Every selected column is
then either entirely zero or entirely one. Equal column sums force
all columns to agree. Therefore

\[
\boxed{e\in\{0,3\}.}
\]

The same argument works with any odd square size in place of three.

## 4. Apply this to a least-degree noncentral vertex

Let `a` have the least noncentral degree `d>3`. Its non-top neighbors
are all sharp. The [least-degree balance argument](1485_unrestricted_central_incidence.md)
shows that its sharp in-degree and out-degree agree, say `k`.
Section 2 gives

\[
d=3+k,\qquad 1\le k\le3.
\]

Let `U=TopPred(a)` and `V=TopSucc(a)`, both of size three. For
each `u∈U`, the size-three fiber `L_u^{-1}(a)` contains all `k`
sharp successors of `a`. Its other `3−k` inputs are top vertices.
Thus precisely `3−k` members `v∈V` satisfy `u*v=a`.
Every other path `u→a→v` is bad. Its good replacement has degree
strictly below `d`, so minimality of `d` makes that replacement
central. Therefore every row of `K[U,V]` has sum `k=d−3`.
The dual fiber count gives the same column sum.

Section 3 now yields `k∈{0,3}`. Since `k≥1`, we get `k=3`
and `d=6`, as claimed. The same fiber count shows that `3−k=0`:
no top-input pair has product `a`.

## 5. The first noncentral top output has sharp degrees one

Let `p` be the least degree among noncentral products of two top
vertices, and fix such a product `a` of degree `p`. Existence follows
from the non-full central core. Section 4 excludes `p=6`, while
the three-degree product bound gives `p≤9`. Thus `p∈{7,8,9}`.

Put `U=TopPred(a)` and `V=TopSucc(a)`. A bad path from `U`
through `a` to `V` has a strictly lower-degree good replacement.
That replacement is itself a top-top product, so minimality of `p`
makes it central. The bad-path matrix on `U×V` is therefore
exactly `K[U,V]`; its complementary entries are precisely the
ordered top pairs whose product is `a`.

Write `k+` and `k-` for the sharp out-degree and in-degree of `a`.
Every top translation fiber has size three and contains all sharp
neighbors on the opposite side. Hence every row of `K[U,V]` has
sum at least `k+≥1`, and every column sum is at least `k-≥1`.

Both binary types must occur in each selected list. If only one type
occurred in `U`, positive column sums would force the same sole type
in `V`, giving `K[U,V]=J`, contrary to `a` being a top product.
The same argument applies with the lists reversed.
If `k+≥2`, both column types would have multiplicity at least two
among three columns, which is impossible. Dually `k-≥2` is
impossible. Thus

\[
\boxed{k+=k-=1.}
\]

Each list has its two binary types in multiplicities one and two.
The number of matching-type pairs, namely the number of ones in
`K[U,V]`, is consequently four or five. Writing `g` for the number
of good top endpoint pairs with middle `a`, we obtain

\[
\boxed{g\in\{4,5\}.}                           \tag{1}
\]

## 6. The top-fiber slot bound forces degree nine

The [general top-fiber slot bound](1485_three_central_minimum_top_output.md#a-general-top-fiber-slot-bound)
states that, when every vertex has `r` top neighbors in each direction
and every noncentral degree is at least `q`, a degree-`p` vertex of
sharp out-degree `k` has

\[
g\le r(r-k)-(p-r-k)\max(0,q-p+r).
\]

Here `r=3`, `q=6`, and `k=1`. For `p=7` the upper bound is zero,
and for `p=8` it is two. Both contradict (1). Hence `p=9`.

As an intermediate necessary condition, degrees six and nine divide
the order `n`, so `18|n`. The occurring complementary degree `n/9`
cannot lie strictly between three and six. Equality to three would
give `n=27`, inconsistent with divisibility by six. Therefore
`n/9≥6`, and `n≥54`. The contradiction below does not require an
order-by-order search, including at these larger orders.

## 7. Equality in the product-degree bound forces a matching

The following fact holds in any finite E1485 magma of minimum degree
`r`, maximum degree `s`, and order `n=rs`:

> If `a` is a product of top vertices and `d(a)=r²`, its good
> ordered top endpoint pairs form a matching: no two distinct pairs
> have the same first coordinate or the same second coordinate.

To prove the first assertion, suppose `a=u*v=u*w`, where `u,v,w`
are top. Recall the [fixed-parameter set](1485_image_research.md)

\[
F_u(a)=\{b:u*(a*b)=a\},\qquad
|F_u(a)|=\frac{n^2}{d(u)d(a)}.
\]

The absorption identity proving the product-degree bound gives
`Row(v)⊆F_u(a)` and `Row(w)⊆F_u(a)`. At degree `r²`,

\[
|F_u(a)|=\frac{n^2}{s r^2}=s
=|Row(v)|=|Row(w)|.
\]

Thus `Row(v)=Row(w)`. Every top vertex has a central successor;
choose one, say `z`, of `v`. It is then also a successor of `w`.
The two paths `a→v→z` and `a→w→z` both have central endpoint
`z`, so both are good. Their good middle is unique, forcing `v=w`.
Applying this argument to the dual magma proves the second assertion.

In particular, if `a` has exactly `r` top predecessors, it has at
most `r` good ordered top endpoint pairs.

## 8. Contradiction

Our first noncentral top output has degree nine, and exactly three top
predecessors. Section 7 therefore gives `g≤3`, contradicting the
lower bound `g≥4` in (1). This excludes the five-central, nine-top
profile. The earlier analytic nine-top reduction handles every
minimum-degree-three model with five central vertices, completing the
theorem without a computational classification premise.
