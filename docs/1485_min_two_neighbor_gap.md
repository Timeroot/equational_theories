# Neighbor gaps from a full central core

Research note, 18 September 2026. Assume a finite E1485 magma has order
`n`, minimum translation degree `r`, and exactly `r²` central vertices.
This note proves:

* No translation degree lies strictly between `r` and `2r`, or strictly
  between `2r` and `3r`.
* Every vertex of degree `2r` or `3r` has exactly `r` sharp neighbors
  in each direction.
* If a degree greater than `r` occurs, degree `2r` occurs and `2r|n`.

The full-central-core hypothesis is proved for **every finite model
with minimum degree two**, by the
[central-cardinality theorem](1485_two_central_exclusion.md). Thus,
unconditionally at minimum degree two, degrees three and five are
absent, degrees two, four, and six are sharp-regular, and the order is
divisible by four. A nonregular vertex must have degree at least seven.

The hypothesis is not established for arbitrary `r`. Even under that
hypothesis this note does not settle regularity at larger degrees or
the complete spectrum conjecture. These are pen-and-paper results, not
Lean declarations.

## Setup

Use the finite degree and uniform-fiber theorems and the
[canonical auxiliary relation](1485_full_central_core.md). Write `Z`
for the central set and `T` for the maximum-degree set. Under
`|Z|=r²`, both sets have `r²` elements, every vertex has `r` top
predecessors and successors, and the relation

\[
B(a)=a*T,\qquad B^-(a)=T*a
\]

is `r`-regular in both directions. It contains all sharp edges.
Every vertex has at least one and at most `r` sharp neighbors in each
direction. Its ordinary in-degree and out-degree agree, denoted `d(a)`;
degrees divide `n`, and the complementary degree `n/d(a)` also occurs.

Every top vertex has `r` central sharp neighbors in each direction.
Those exhaust its `B` neighbors. Therefore, if `a` is not central,
neither `B(a)` nor `B^-(a)` contains a top vertex. This remains true
when `a` itself is top.

## Good extensions distinguish the auxiliary edges

For an ordinary edge `a→b`, a successor `c` of `b` gives a good path
`a→b→c` precisely when `a*c=b`. These good extensions form the
nonempty fiber `L_a^{-1}(b)`, of cardinality `n/d(a)`.

If `a B b`, all `r` top successors of `b` give good extensions: the
top-input fiber of `u↦a*u` at `b` is exactly `T∩Row(b)`. If the
ordinary edge does not belong to `B`, none of its top extensions is
good, since `a*T=B(a)` does not contain `b`. Thus

\[
\#\{\text{good non-top extensions of }a\to b\}
=\frac{n}{d(a)}-r\mathbf1_{aBb}. \tag{1}
\]

The dual statement counts good non-top predecessors of the edge.
In particular every ordinary edge outside `B` satisfies both gap
inequalities

\[
\boxed{a\to b,\ a\not B b
\quad\Longrightarrow\quad
\frac n{d(a)}\le d(b)-r,
\qquad \frac n{d(b)}\le d(a)-r.} \tag{2}
\]

For later counts, the number of bad non-top extensions is exactly

\[
d(b)-\frac n{d(a)}-r+r\mathbf1_{aBb}. \tag{3}
\]

These extensions cannot end at a sharp successor of `b`, because a
path containing a sharp edge is good. There is a column-dual formula.

## The smallest noncentral degree is exactly twice the minimum

Suppose some degree greater than `r` occurs, and let `q` be the
smallest one. If `q>2r`, a vertex `v` of degree `q` has a predecessor
`a` which is neither top nor a `B` predecessor: those two sets cover
at most `2r` of its predecessors.

The complementary degree `j=n/d(a)` occurs. Since `a` is not top,
`j>r`; since its edge to `v` is outside `B`, (2) gives `j≤q−r<q`.
This contradicts the choice of `q`. Thus `q≤2r`.

Every ordinary neighbor of a degree-`q` vertex has complementary degree
at most `q`. A non-top neighbor has complementary degree greater than
`r`, and hence exactly `q`, by minimality. All its non-top neighbors
are consequently sharp.

There are `q−r` non-top neighbors in either direction. They include
all `r` neighbors under `B`, because a noncentral vertex has no top
`B` neighbor. Hence `q−r≥r`. Combining this with `q≤2r` proves

\[
\boxed{q=2r.} \tag{4}
\]

There are exactly `r` non-top neighbors at every degree-`2r` vertex,
and all are sharp. This proves sharp regularity at degree `2r` and
excludes every degree in `(r,2r)`.

Degree divisibility also gives `2r|n` whenever the degree spectrum is
nonconstant. If every degree is `r`, then `n=r²`. In the unconditional
case `r=2`, both alternatives give `4|n`.

## The second open interval is empty

Suppose an occurring degree `q` satisfies `2r<q<3r`. A degree-`q`
vertex again has a predecessor `a` that is neither top nor a `B`
predecessor, because `q>2r`. Its complementary degree satisfies

\[
r<\frac n{d(a)}\le q-r<2r,
\]

contradicting the first gap. Thus no degree lies in `(2r,3r)`.
For `r=2`, this excludes degree five without any assumption about
sharp regularity at that degree.

## Degree three times the minimum is sharp-regular

Let `d(v)=3r`. The two gaps show that the complementary degrees of
its neighbors can only be `r`, `2r`, or `3r`. The `r` top neighbors
have complementary degree `r`; its sharp neighbors have complementary
degree `3r`; every other neighbor has degree `n/(2r)`.

Let `k^-` and `k^+` count its sharp predecessors and successors.
There are `2r−k^-` and `2r−k^+` neighbors of degree `n/(2r)`.
Reciprocal neighbor balance gives

\[
\frac{r^2+3rk^-+2r(2r-k^-)}n
=\frac{r^2+3rk^++2r(2r-k^+)}n,
\]

so `k^-=k^+`; denote this common value by `k`.

Suppose `k<r`. Since the `r` elements of `B^-(v)` are non-top,
one of them, say `a`, is not sharp and has degree `n/(2r)`.
The edge `a B v` has `2r` good extensions. Its `r` top extensions
and its `k` sharp extensions are good. Among the `2r−k` non-top,
nonsharp successors of `v`, exactly `r−k` give good paths and
therefore exactly `r` give bad paths.

On the other hand, let `c` be any successor of degree `n/(2r)`
outside `B(v)`. The edge `v→c` has `2r` good predecessors, and
none is top by the dual of (1). There are exactly `2r` non-top
predecessors of `v`, so all of them give good paths to `c`. In
particular `a→v→c` is good.

Every bad extension from `a` must therefore end at a nonsharp element
of `B(v)`. There are only `r−k` such elements, fewer than the `r`
bad extensions just counted. This contradiction proves

\[
\boxed{k^-=k^+=r\quad\text{when }d(v)=3r.} \tag{5}
\]

## Scope of the bad-path count

At a vertex of degree `q`, label a non-top neighbor by its
complementary degree `j=n/d(a)`. A non-`B` predecessor of label `j`
has `q-j-r` bad non-top extensions, whereas a `B` predecessor has
`q-j`. These are row sums of the zero-one matrix of bad paths through
the vertex; its column sums are given by the dual rule. Sharp rows
and columns are zero.

For `r=2,q=6`, a nonregular vertex would require a bad row and a bad
column each having two entries, while all others vanish, so their
single intersection cannot support the prescribed margins. At degree
seven the elementary row and column bounds no longer exclude every
possibility; further structure is needed.
