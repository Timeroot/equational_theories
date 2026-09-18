# The exact local projection chain at degree three times the minimum

Research note, 18 September 2026. Assume a finite E1485 magma of order
`n=rs` has minimum degree `r`, maximum degree `s`, and a full central
core of size `r²`. This note proves a necessary local structure for a
vertex of degree `3r`. **It does not exclude such a vertex.** In
particular, the known exclusion of order `6r²` cannot presently be
applied to an extracted submagma merely from this local structure.
These are pen-and-paper statements, not Lean declarations.

Use the [neighbor gaps](1485_min_two_neighbor_gap.md),
[full-core theorem](1485_full_central_core.md), and the mixed-projection
rank and fixed-point counts from the
[projection note](1485_image_research.md).

## Three equally sized layers in each neighborhood

Fix `v` with `d(v)=3r`. Its row is a disjoint union

\[
\operatorname{Row}(v)=S^+\sqcup U^+\sqcup T^+,
\qquad |S^+|=|U^+|=|T^+|=r,                       \tag{1}
\]

whose degrees are respectively `s/3`, `s/2`, and `s`.
Here `S⁺` is its sharp-successor set and `T⁺` its top-successor set.
The column has corresponding layers `S⁻,U⁻,T⁻` with the same sizes
and degrees.

Indeed, a neighbor `a` satisfies `n/d(a)≤3r`, and `n/d(a)` is itself
an occurring degree. The two forbidden open intervals below `3r`
therefore leave only `r,2r,3r` as complementary degrees. There are
exactly `r` top neighbors and, by degree-`3r` sharp regularity, exactly
`r` sharp neighbors. The other `r` form the middle layer. This
argument applies even if many other degrees occur elsewhere in the
magma.

## Every mixed projection has one of three nested images

For each parameter `y∈M`, put

\[
P_y(x)=v*(x*y).
\]

The mixed projections are idempotent, take values in `Row(v)`, and
satisfy the fixed-left band identity `P_yP_zP_y=P_zP_y`. Their images
and ranks obey

\[
\operatorname{im}(P_y)=\{u:(y*v)*u=v\},\qquad
\operatorname{rank}(P_y)=\frac n{d(y*v)}.          \tag{2}
\]

Consequently:

| Position of `y*v` | Rank of `P_y` | Image of `P_y` |
|---|---:|---|
| `T⁻` | `r` | `S⁺` |
| `U⁻` | `2r` | `S⁺∪U⁺` |
| `S⁻` | `3r` | `Row(v)` |

Each of the three rows of the table applies to exactly `n/3`
parameters `y`.

Here is the point requiring proof: the image in the middle row is
independent of `y`, not just of cardinality `2r`. Every projection
fixes the `r` sharp successors, so rank `r` forces image `S⁺`.
A rank-`3r` projection is the identity on the whole row. For
`u∈U⁺`, the exact fixed-parameter count is

\[
\#\{y:P_y(u)=u\}
=\frac{n^2}{d(v)d(u)}
=\frac{2n}{3}.                                  \tag{3}
\]

Uniform fibers of `R_v` and the `r` elements of each column layer
show that each rank occurs for `n/3` parameters. The rank-`r`
parameters never fix `u`, and all rank-`3r` parameters fix it.
Equation (3) therefore forces **every** rank-`2r` parameter to fix
**every** element of `U⁺`. Its image is exactly `S⁺∪U⁺`, as asserted.
For completeness, the corresponding fixed-parameter counts on
`S⁺,U⁺,T⁺` are `n,2n/3,n/3` respectively.

In particular the fixed-left generated semigroup has no further
images or ranks. The three possible images form the chain

\[
S^+\subset S^+\cup U^+\subset\operatorname{Row}(v). \tag{4}
\]

To check the semigroup assertion, each generator preserves the image
of every other generator by the band identity. Thus it preserves
every set in (4). In a product of generators, choose a factor of
smallest image. All factors with larger image fix this smallest
image pointwise, and factors with the same image do too. The product
therefore has precisely that smallest image.

## Exact goodness through the vertex

The good two-edge paths `a→v→b`, with `a` in a column layer and `b`
in a row layer, are described by

| | `S⁺` | `U⁺` | `T⁺` |
|---|---|---|---|
| `S⁻` | good | good | good |
| `U⁻` | good | good | bad |
| `T⁻` | good | bad | bad |

This follows directly from (2) and the image table: `a*b=v` exactly
when `b` belongs to the corresponding displayed image. In particular
the entire rectangle `U⁻×U⁺` has constant product `v`.

The good replacement of a path in either off-diagonal bad rectangle
`T⁻×U⁺` or `U⁻×T⁺` has degree exactly `2r`. Its degree is less
than `3r`, so it is `r` or `2r`; it cannot be central, because a
central neighbor can only be adjacent to top vertices and the other
endpoint has degree `s/2`. On `T⁻×T⁺` the good replacement is
central, by `T*T⊆Z`.

## A canonical local rectangle of size `3r²`

There is a further useful general observation. If all canonical
predecessors of a vertex `a` are sharp, then every path
`a→u B w` is good, where `B(x)=x*T` is the canonical relation.
Indeed `t*a∈B⁻(a)` is then sharp for every top parameter `t`, so

\[
\operatorname{rank}(L_aR_t)=n/d(t*a)=d(a).
\]

This idempotent projection therefore fixes `Row(a)` pointwise.
Writing `w=u*t` proves `a*w=u`.

It follows that the sets `B(u)`, for `u∈Row(a)`, are pairwise
disjoint: a common element would give two good middles from `a`.
For our degree-`3r` vertex, define

\[
I(v)=\bigcup_{u\in\operatorname{Row}(v)}B(u).
\]

Then

\[
|I(v)|=3r^2,\qquad
I(v)=B(S^+)\sqcup B(U^+)\sqcup Z,                 \tag{5}
\]

with each displayed block of size `r²`; here `B(X)` denotes the
union over `x∈X`. The last block is `B(T⁺)=Z`, because it consists
of `r` disjoint `r`-element central sets. A column-dual construction
has the same cardinality.

For any central parameter `h`, multiplication gives inverse
bijections

\[
\operatorname{Row}(v)\times\operatorname{Col}(h)
\longleftrightarrow I(v),\qquad
(u,c)\longmapsto u*c,\qquad
x\longmapsto(v*x,x*h).                            \tag{6}
\]

The first coordinate is recovered by the preceding goodness result;
the second is recovered by centrality, `(u*c)*h=c` for
`c∈Col(h)`. Its image is all of `I(v)` because
`u*Col(h)=B(u)`. Consequently

\[
E_{v,h}(x)=(v*x)*(x*h)                            \tag{7}
\]

is a retraction of `M` onto `I(v)`.

This makes a specific extraction candidate available, but not an
E1485 submagma. In particular, the blocks `B(S⁺)` and `B(U⁺)` need
not yet be confined to degrees `3r` and `2r`: that would require
sharp regularity at degrees `s/3` and `s/2`. Nor is the retraction
asserted to have uniform fibers or to preserve multiplication.

## Why this does not yet give a smaller E1485 magma

First, the row is **not** closed under the operation. A degree-`3r`
vertex cannot be top: otherwise `n=3r²`, while the guaranteed
degree `2r` would have occurring complementary degree `3r/2`, in
the first forbidden gap. Thus `Row(v)` contains no central vertex.
But it contains top vertices, and the square of each top vertex is
central. This disproves row closure under the hypotheses, rather
than merely leaving it unproved.

The larger set `I(v)` in (5) is also not closed. No element of
`Row(v)` is central, so none of its canonical successors is top.
Thus `I(v)` has no top elements. It contains all of `Z`, however,
and every product with a central factor is top. A retraction onto
`I(v)` cannot be a magma homomorphism: the image of a homomorphism
would be a submagma.

Second, the local projection information by itself is consistent as
an action on the row. On three layers `{s_i},{u_i},{t_i}`, each of
size `r`, take

* `E`: send all three points of index `i` to `s_i`;
* `F`: fix `s_i,u_i`, and send `t_i` to `u_i`;
* `I`: the identity.

These are commuting idempotents with ranks `r,2r,3r` and the nested
images (4). Repeat each projection `n/3` times in the parameter
list. The exact fixed-parameter counts are `n,2n/3,n/3`, and every
nontrivial move decreases the assigned degrees `s/3,s/2,s`.
Thus even the exact local rank distribution, fixed-point counts,
band identities, and strict degree decrease do not yield a
contradiction. This example is an abstract projection system, **not**
an E1485 magma or a counterexample to the conjecture.

The missing step must use relations between different fixed-left
families, the five-cycle law beyond this local goodness table, or a
newly justified quotient or derived operation. No such extraction is
claimed here.
