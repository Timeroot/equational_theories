# A full central core makes the regular auxiliary relation canonical

Research note, 18 September 2026. The results below are pen-and-paper
theorems, not Lean declarations. Assume the established finite E1485
structure theorems, and write `n=|M|`, `r=min d`, `s=max d`, so `n=rs`.
Let `Z` and `T` be the minimum- and maximum-degree classes.

The extra hypothesis in this note is

\[
|Z|=r^2. \tag{H}
\]

It holds for **every finite model with `r=2`**, by the
[central-cardinality theorem](1485_two_central_exclusion.md). It is not
proved here for arbitrary `r`. Under (H), the subsequent
[Boolean-quotient theorem](1485_full_core_quotient.md) now proves
square-or-double-square order.

The subsequent [full-core sharp-regularity theorem](1485_full_core_sharp_regularity.md)
now proves that the canonical relation constructed here is exactly
sharp adjacency, without any restriction on the number of degrees.
This resolves the matching obstruction described at the end of this note.

The [cyclic-block theorem](1485_full_core_cyclic_blocks.md) then partitions
the carrier into blocks of size `r²`; the
[period-ten theorem](1485_full_core_period_ten.md) shows that their
canonical permutation has order dividing ten. In the nonconstant case
this proves `2r²∣n`. Compatibility of multiplication with these blocks
is now proved by the linked quotient theorem, giving the stronger
conclusion `n=r²·2^m`. The general full-core hypothesis remains open.

## Maximum-degree translations are mutual inverses on their images

For `t∈T`, let `k_t^-` and `k_t^+` count its central predecessors and
successors. These are sharp-neighbor counts, between one and `r`.
Unique goodness of central-endpoint paths gives

\[
\sum_t k_t^- = \sum_t k_t^+ = r|Z|=r^3,
\qquad \sum_t k_t^-k_t^+=|Z|^2=r^4.
\]

Equality in `Σ k_t^-k_t^+≤r Σ k_t^-` forces every `k_t^+=r`.
Dually every `k_t^-=r`, and therefore `|T|=r²`.

For any vertex `a`, each central row meets its top predecessor set
exactly once. Summing over the central rows counts each top predecessor
`r` times. Hence `a` has exactly `r` top predecessors, and dually
exactly `r` top successors.

Each central vertex is the good middle of `r²` top-endpoint pairs.
These disjoint sets cover all `r⁴` pairs, so

\[
T*T\subseteq Z. \tag{1}
\]

For `t,u∈T`, both `L_tR_u` and `R_uL_t` are idempotent mixed
projections. Both have rank `n/d(u*t)`, hence rank `s` by (1).
Their images are therefore the full
images of `L_t` and `R_u`. Idempotence gives

\[
\boxed{L_tR_uL_t=L_t,\qquad R_uL_tR_u=R_u.} \tag{2}
\]

Equivalently, `L_t:Col(u)→Row(t)` and
`R_u:Row(t)→Col(u)` are inverse bijections.

## The central choice disappears

For central `h`, the [regular-relation construction](1485_sharp_degree_defect.md)
defines

\[
B_h(a)=\{a*c:c\in Col(h)\},\qquad |B_h(a)|=r.
\]

Choose a top predecessor `t` of `a`. For every `u∈T`, equation (2)
applied to `a∈Row(t)` gives `t*(a*u)=a`. Thus `a*T` is contained
in the `r`-element fiber `L_t^{-1}(a)`. It contains `B_h(a)` because
`Col(h)⊆T`. Consequently

\[
\boxed{B_h(a)=a*T=L_t^{-1}(a)
\quad(h\in Z,\ t\in T\cap Col(a)).} \tag{3}
\]

In particular the relation is independent of `h`; call it `B`.
It is `r`-regular in both directions and satisfies `S⊆B⊆A`, where
`S` and `A` denote sharp and ordinary adjacency. The dual statement is

\[
B^{-}(a)=T*a=R_u^{-1}(a)
\quad(u\in T\cap Row(a)). \tag{4}
\]

For clarity, these really are opposite relations: if `b=a*u` with
`u∈T`, choose a top predecessor `t` of `a`. Then (2) gives `t*b=a`,
so `a∈T*b`. The converse is dual.

For each fixed `a`, its `r` successors under `B` have top successor
sets that partition `T`. Indeed (2) says that each fiber in (3) meets
`Col(u)` exactly once for every `u∈T`. Each part has size `r`.
In particular `u↦a*u` maps `T` onto `B(a)` with all fibers of size
`r`; the fiber at `b` is `T∩Row(b)`. There is a dual statement for
`t↦t*a` and top predecessor sets.

## An exact overlap formula when `r=2`

Now take `r=2`, so (H) is available unconditionally. Write
`B(a)={b,c}` with `d(b)≤d(c)`. Since `B(a)` contains a sharp
successor,

\[
d(b)=n/d(a). \tag{5}
\]

The set `B(a)` is invariant under every projection
`P_z(v)=a*(v*z)`. To check this, fix a central parameter `h` and
write `E=P_h`, whose image is `B(a)`. The band identity
`EP_zE=P_zE` proves the invariance. It follows that

\[
Row(b)\cup Row(c)=L_a^{-1}(\{b,c\}). \tag{6}
\]

Indeed, if `w=v*z` with `v∈B(a)`, then `a*w=P_z(v)∈B(a)`.
Conversely, `a*w=v∈B(a)` gives the good path `a→v→w`, hence
`w∈Row(v)`. The two fibers on the right of (6) each have size
`n/d(a)=d(b)`. Therefore

\[
\boxed{|Row(b)\cup Row(c)|=2d(b),\qquad
|Row(b)\cap Row(c)|=d(c)-d(b).} \tag{7}
\]

In particular `d(c)≤2d(b)`. Both edges from `a` are sharp exactly
when the two ordinary rows in (7) are disjoint. Otherwise `b` is the
unique sharp successor, and every bad path `a→c→w` is replaced by
the good path through `b`. All these statements have column-dual
versions for `B^{-}(a)`.

## The former matching obstruction

The bipartite graph of `B` has degree two at every vertex. It is thus
a disjoint union of even cycles (left and right copies of `M` are
distinct). Sharp edges cover every vertex, but this alone does not
say that they contain a perfect matching.

**A perfect matching consisting of sharp edges would suffice.** Its
degree products multiply to `n^n`, so
`(Π_a d(a))²=n^n`. The product of degree products over all `2n`
edges of `B` is then `n^{2n}`. Each factor is at least `n`; hence
each is exactly `n`, and every edge of `B` is sharp.

This was the remaining obstruction when the canonical relation was first
constructed. It is now resolved by the linked sharp-regularity proof:
all edges of `B` are sharp, so the regular bipartite graph supplies the
matching, the overlaps in (7) vanish, and `Δ=Σ d−Σ n/d=0`.
The new proof uses ordinary edges in the top-coordinate rectangle,
not just the mutual-inverse identities by themselves.
