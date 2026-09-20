# Ordered degrees in every central-parameter row

Research note, 19 September 2026. These unconditional finite E1485
lemmas extend the row-local argument in
[the first-output note](1485_first_top_output_fibers.md) from top
vertices to arbitrary vertices. They are not Lean declarations.

Write `n=rs`, with minimum degree `r`, fix a central vertex `h`,
and use the canonical central-parameter relation

\[
B_h(a)=a*Col(h)=L_{h*a}^{-1}(a).
\]

Its in- and out-degrees are `r`, it lies in ordinary adjacency,
and it contains every sharp edge. No independence from `h` or
full-core hypothesis is assumed.

## 1. An ordered bound in an arbitrary row

Fix `a`, put `c=n/d(a)`, and let `S=B_h(a)`. For a member
`b∈S`, let `j` be the number of members of `S` having degree
strictly smaller than `d(b)`. Then

\[
\boxed{d(b)\le c+(c-1)j.}                                  \tag{1}
\]

Indeed, set `t=h*a`, which is top. The map `v↦a*v` is
injective on `Col(h)`: if two inputs give the same value `b`,
the two ordinary paths `b→v→h` are good by their central
endpoint, so the inputs coincide. Its image `S` has size `r`
and equals the size-`r` fiber `L_t^{-1}(a)`.

For `b∈S`, we have `t*b=a`. Absorption gives

\[
Row(b)\subseteq F_t(a)
=\{x:t*(a*x)=a\}=L_a^{-1}(S).
\]

For `x∈Row(b)`, the path `a→b→x` says either `a*x=b`
or `d(a*x)<d(b)`. Thus `Row(b)` is contained in the union
of the fiber of `L_a` at `b` and the fibers at the `j`
strictly smaller members of `S`. These fibers are disjoint and
have size `c`. Each meets `Col(h)` in exactly one point, whereas
`Row(b)` meets that central column in exactly one point. At
least `j` of the union's points are therefore excluded. This proves
`d(b)≤(j+1)c−j`, which is (1).

In particular every central-parameter edge satisfies

\[
a\mathrel{B_h}b
\quad\Longrightarrow\quad
d(b)\le rc-r+1.
\]

For `r>1`, this gives the strict product inequality

\[
\boxed{a\mathrel{B_h}b\quad\Longrightarrow\quad
d(a)d(b)<nr.}                                               \tag{2}
\]

## 2. Prime-power orders force all sharp counts above the prime

Suppose `n=ℓ^e`, where `ℓ` is prime, and `r≥ℓ`.
Then every vertex has at least `ℓ` sharp predecessors and at
least `ℓ` sharp successors:

\[
\boxed{k^-_{\mathrm{sharp}}(a),\ k^+_{\mathrm{sharp}}(a)
\ge\ell.}                                                  \tag{3}
\]

Fix `a`, again putting `c=n/d(a)`, and let `k` be its sharp
out-degree. All `k` sharp successors lie in `S=B_h(a)` and
have degree `c`. Every other member of `S` has larger degree,
by the ordinary edge bound and the definition of sharpness.

If `k=r`, the conclusion is immediate. Otherwise choose a
least-degree nonsharp member `b∈S`. Exactly the `k` sharp
members have strictly smaller degree. All degrees divide `n`,
so they are powers of `ℓ`; consequently `d(b)≥ℓc`.
Applying (1) gives

\[
\ell c\le c+(c-1)k,
\qquad
k\ge\left\lceil\frac{(\ell-1)c}{c-1}\right\rceil
\ge\ell.
\]

Here `c≥r≥ℓ>1`. The dual proof gives the in-degree bound.
The same proof works whenever consecutive occurring translation
degrees differ by a factor of at least an integer `ℓ≥2` and
`r≥ℓ`; primality is only a convenient source of that gap.

The assumption `r≥ℓ` matters: minimum-one models at powers of
two have sharp degree one. At odd prime-power order, minimum one
is already excluded by the known minimum-one classification.

More generally, if `b∈B_h(a)` has `d(b)≥ℓ^v c`, then
(1) implies that at least `ℓ^v` members of `B_h(a)` have
strictly smaller degree than `b`, for every integer `v≥1`.
In particular `ℓ^v≤r−1`. This is an ordered-prefix constraint
on each individual auxiliary row, not merely a global average.

## 3. Sparse degrees make a first top output sharp off the top class

Let `p` be the first noncentral top-output degree and let `a`
be such an output. Write its top-neighbor count as `t=p-l`,
where the first-output theorem gives `1≤l≤r−1`.

If `x` is a non-top successor of `a`, put `c=n/d(x)`.
The ordinary edge bound gives `c≤p`. On the other hand the
fiber `R_x^{-1}(a)` contains all `t` top predecessors of `a`,
by the first-output fiber theorem. It also contains any sharp
predecessor of `a`, since a path containing that sharp edge is
good. Such a predecessor is non-top. Therefore

\[
\boxed{p-r<c\le p.}                                        \tag{4}
\]

If there is no occurring degree strictly between `p−r` and `p`,
equation (4) forces `c=p`: every non-top successor is sharp.
Duality gives the predecessor assertion.

In particular, at prime-power order, whenever `p≥ℓr`, the
next smaller possible degree is `p/ℓ≤p−r`. Thus every
non-top neighbor of `a` is sharp, and (3) improves its count to

\[
\ell\le l\le r-1.
\]

These facts do not yet prove sharp regularity, which would require
`l=r` and therefore exclude a noncentral top output altogether.

## 4. Consequences for the next odd prime-power frontier

At the remaining order `n=ℓ^9`, with `ℓ` an odd prime,
the [divisor-gap theorem](1485_first_top_output_divisor_gap.md)
leaves only the minimum `r=ℓ³` and the four occurring degrees

\[
r=\ell^3,\quad q=\ell^4,\quad b=\ell^5,\quad s=\ell^6.
\]

The first noncentral top-output degree is `q`. Indeed if it were
at least `b=ℓ²r`, the divisor-gap calculation with multiplier
`ℓ²` would require `r>ℓ⁴`, contrary to `r=ℓ³`.
Here that calculation only needs `p≥ℓ²r`, not a corresponding
bound on the least noncentral degree of the whole magma.

For a degree-`q` vertex, its auxiliary row consists of its sharp
degree-`b` successors and some top successors; if any top member
occurs, it has at least `ℓ` sharp members below it.

For a degree-`b` vertex, an auxiliary top successor forces at
least `ℓ²` strictly lower-degree members in the same row.
For a top vertex, an auxiliary degree-`b` successor similarly
forces at least `ℓ²` lower-degree members. Finally there are
no auxiliary top-to-top edges, since `s²=nr` violates (2).

These are genuine additional restrictions on the ninth-power
frontier, not an exclusion of that frontier.
