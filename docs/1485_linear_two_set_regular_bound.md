# Regular linear intersections of two-element sets: the sharp factor five

Research note, 19 September 2026. This elementary finite-set theorem
sharpens the factor six from permutation counting to the sharp factor
five when all cross-intersections have size at most one. No enumeration
is used.

Let `A_1,...,A_t` and `B_1,...,B_t` be nonempty sets of size at
most two. Repetitions are allowed. Suppose every cross-intersection
has size zero or one, and the disjointness matrix has every row and
column sum equal to `h>0`.

**Theorem.**

\[
\boxed{t\le5h.}                                             \tag{1}
\]

The factor five is sharp, attained by repeating the pentagon
[crown construction](1485_two_set_crown_bound.md#3-equality-five-is-the-pentagon).

## 1. Normalize the two families

Choose uniformly from each indexed family, retaining multiplicities.
Put

\[
\delta=h/t,\qquad \gamma=1-\delta,
\qquad \alpha_v=\Pr(v\in A),\quad \beta_v=\Pr(v\in B).
\]

Every fixed occurring `A` intersects a random `B` with probability
`γ`, and every occurring `B` intersects a random `A` with the
same probability. We prove a contradiction from `δ<1/5`.

Every fixed two-element set occurs in either family with probability
at most `δ`. For example, take a `B_j` disjoint from an occurring
`A_i`; this is possible because `h>0`. All copies of `A_i` are
among the `h` sets disjoint from this `B_j`, giving the bound.
The dual argument applies to repeated `B` sets.

## 2. Every vertex has mass at most three times the disjointness density

Fix a vertex `v` occurring in the `A` family. Choose an `A_i`
containing it and then a `B_j` disjoint from `A_i`. In particular
`B_j` avoids `v`.

An `A` containing `v` can intersect this `B_j` only if it is
one of the at most two sets `{v,x}`, for `x∈B_j`. Their total
probability is at most `2δ` by §1. All other intersecting `A`
sets have total probability at most `1−α_v`. Since the total
intersection probability is `γ`,

\[
\gamma\le1-\alpha_v+2\delta,
\qquad \alpha_v\le3\delta.
\]

The dual argument gives

\[
\boxed{\alpha_v,\beta_v\le3\delta.}                          \tag{2}
\]

No singleton can occur. If `{v}` occurred in the `A` family,
its intersection probability would say `β_v=γ>3δ`, contrary
to (2); similarly for `B` singletons. Thus every set has size two.

There are no vertices appearing on only one side. If `v` occurred
only in the `A` family, an edge `{v,u}` in that family would give
`β_u=γ`, again contradicting (2). The dual argument is identical.
Consequently all vertices under consideration have positive `α,β`,
and

\[
\sum_v\alpha_v=\sum_v\beta_v=2.                            \tag{3}
\]

## 3. The two support graphs have no leaves

Let `G` be the simple support graph of the `A` two-sets, and
`H` the simple support graph of the `B` two-sets. Both have the
same vertex set by §2. They have no common edge, because that
would give a cross-intersection of size two.

If `v` were a leaf of `G`, all `A` sets containing it would be
copies of its unique incident edge. Thus `α_v≤δ`. Choose any
incident `H` edge `{v,u}`, possible because `β_v>0`. Its fixed
intersection probability, together with the cross-intersection bound,
gives

\[
\alpha_v+\alpha_u=\gamma.
\]

Therefore `α_u≥γ−δ=1−2δ>3δ`, contradicting (2).
There are no isolated vertices by construction. Both `G` and `H`
have minimum degree at least two, by the dual argument.

## 4. The first support graph must be bipartite

For every edge `{u,v}` of `G`,

\[
\beta_u+\beta_v=\gamma.                                    \tag{4}
\]

On an odd cycle, this makes all its vertex masses equal to `γ/2`.
For an odd cycle of length at least five, (3) gives
`5γ/2≤2`, or `γ≤4/5`, contradicting `δ<1/5`.

A triangle is also impossible. No `B` edge can join two triangle
vertices, since all three such edges belong to `G`. Thus every
`B` set meets the triangle in at most one vertex. Its total
`β` mass is at most one, whereas (4) makes it `3γ/2>1`.
Hence `G` has no odd cycle and is bipartite.

## 5. Bipartite components give the final contradiction

In a connected component of `G`, equation (4) makes `β` constant
on each bipartition class, with values `b` and `γ−b`. Both
classes have at least two vertices, since the minimum degree is
at least two. Thus every component has total `β` mass at least
`2γ`. Two components would have mass at least `4γ>2`,
contrary to (3). Therefore `G` is connected.

If both bipartition classes had at least three vertices, their mass
would be at least `3γ>2`, again impossible. One class has exactly
two vertices. Every vertex in the other class has at least two
neighbors, so `G` is a complete bipartite graph `K_{2,k}`.

The graph `H` shares no edge with `G`. Its vertices in the
two-element class can therefore be adjacent only to each other,
giving degree at most one. This contradicts §3 and completes the
proof of (1).

## Sharpness and the E1485 consequence

For any positive integer `h`, take `h` copies of each set in

\[
A_i=\{i,i+1\},\qquad B_i=\{i+2,i+4\},
\qquad i\in\mathbb Z/5\mathbb Z.
\]

There are `t=5h` sets in each family. Every row and column has
exactly `h` disjoint partners, and all other intersections have
size one. Thus the coefficient five cannot be improved for this
abstract class.

If an E1485 magma has `m=r+1` central vertices, its top central
blocks have size at most two. Applying (1) to a first-output
central matrix gives `t≤5(r+t−p)`. Since `t≤m`,

\[
\boxed{p\le r+m-\left\lceil\frac m5\right\rceil.}           \tag{5}
\]

This bound is combined with the stronger small-parameter gap in
the [bounded-central-excess note](1485_bounded_central_excess.md).
