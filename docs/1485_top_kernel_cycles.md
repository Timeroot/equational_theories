# Top kernel mates and the cycles of the canonical relation

Research note, 18 September 2026. This gives a cycle description of the
kernel-mate involutions of maximum-degree translations in a finite E1485
magma of minimum degree two. The canonical bipartite cycles all have
length four or eight. All maximum left and right kernel mates commute
pairwise, including across the two sides. Any fixed left mate and right
mate generate a Klein four group whose orbits are precisely the canonical
four-element blocks. The initial cycle equivalence and local goodness
criterion are retained below to distinguish the original reductions from
their subsequent resolution.

We use the finite structure theorems in
[the graph note](1485_graph_research.md), the
[four-central-vertex theorem](1485_two_central_exclusion.md), and the
[full-central-core results](1485_full_central_core.md), together with
[full-core sharp regularity](1485_full_core_sharp_regularity.md) and the
[cyclic-block theorem](1485_full_core_cyclic_blocks.md). These are
pen-and-paper results, not new Lean declarations.

## The canonical relation and top profiles

Write `n=|M|`, let `Z` be the central set, and let `T` be the set of
maximum-degree vertices. Both have cardinality four, and the maximum
degree is `n/2`. The canonical relation

\[
 a\mathrel B b\quad\Longleftrightarrow\quad b\in a*T
\]

has two predecessors and two successors at every vertex. Define the top
profiles

\[
 P(a)=T\cap\operatorname{Col}(a),\qquad
 Q(a)=T\cap\operatorname{Row}(a).
\]

Both have size two. The full-core theorem supplies the following facts:

* If `B(a)={b,b'}`, then `Q(b),Q(b')` partition `T`. The fiber of
  `t↦a*t`, restricted to `T`, at `b` is exactly `Q(b)`.
* If `B^-(b)={a,a'}`, then `P(a),P(a')` partition `T`. The fiber of
  `t↦t*b`, restricted to `T`, at `a` is exactly `P(a)`.
* If `t∈P(a)`, then `L_t^{-1}(a)=B(a)`. Dually, if `t∈Q(b)`, then
  `R_t^{-1}(b)=B^-(b)`.

In particular, an edge of `B` has every possible top extension good:

\[
aBb\quad\Longrightarrow\quad
a*t=b\ (t\in Q(b)),\qquad t*b=a\ (t\in P(a)). \tag{1}
\]

The sharp-regularity theorem now proves the stronger statement that
`B` is exactly sharp adjacency. In particular, every ordinary two-edge
path containing a `B` edge is good, and `B²` is zero-one.

## Bipartite cycles have length divisible by four

Make the bipartite graph with a left and a right copy of `M`, joining
left `a` to right `b` precisely when `aBb`. It is a finite simple
graph of degree two, so each connected component is a cycle of length
at least four.

Write a component in cyclic order as

\[
 a_0-b_0-a_1-b_1-\cdots-a_{k-1}-b_{k-1}-a_0,
\]

where the `a_i` are left vertices and the `b_i` right vertices. The
two predecessors of `b_i` are `a_i,a_{i+1}`, with subscripts modulo
`k`. Therefore

\[
 P(a_{i+1})=T\setminus P(a_i). \tag{2}
\]

Likewise the profiles `Q(b_i)` alternate between a two-element set
and its complement. No subset equals its own complement, so `k` is
even. Thus every bipartite cycle has length `2k` divisible by four.
Left and right copies are distinct here, even when they carry the same
underlying element of `M`.

## Kernel mates are the two alternating matchings

For `t∈T`, every nonempty fiber of `L_t` has size two. Let `λ_t(x)`
be the other point in the fiber containing `x`. This is a fixed-point-free
involution on `M`. Similarly, let `ρ_t(x)` be the other point in the
`R_t`-fiber containing `x`.

On the right side of a bipartite component, `λ_t` exchanges the two
neighbors of each left vertex `a_i` for which `t∈P(a_i)`. Equation
(2) selects exactly every other left vertex. Thus `λ_t` restricts to
one of the two alternating perfect matchings on the cyclically arranged
right vertices. Different top parameters can select either matching,
but there are only these two restrictions on any one component.
The dual statement describes the restrictions of `ρ_t` to the left
vertices.

Fix one central vertex `h`, and write `Row(h)={s,t}`. For every `a`,
the set `P(a)` meets `Row(h)` in exactly one point: all paths from
`h` to `a` are good, and their middle is unique. Consequently `λ_s`
and `λ_t` select opposite alternating matchings on **every** bipartite
component. This holds whether or not the central incidence multigraph
is connected.

If there are `k=2m` right vertices in the component, the product of
the two alternating matchings has order `m`. For `k=2` both matchings
exchange the same two vertices, so their product has order one. For
`k≥4`, their product moves by two cyclic positions, in opposite
directions on the two parity classes; it consists of two cycles of
length `k/2`.

Two involutions commute precisely when their product has order at most
two. We have proved the following equivalences:

1. Every bipartite component of `B` has at most four vertices on each
   side, hence has length four or eight.
2. All the involutions `λ_t`, for `t∈T`, commute pairwise.
3. All the involutions `ρ_t`, for `t∈T`, commute pairwise.
4. For one fixed central `h` with `Row(h)={s,t}`, the two involutions
   `λ_s,λ_t` commute.
5. For one fixed central `h` with `Col(h)={r_0,r_1}`, the two involutions
   `ρ_{r_0},ρ_{r_1}` commute.

Statements 4 and 5 may equivalently be required for every central
choice. This cycle argument alone only establishes the equivalences.
The next section proves all five statements, as well as the cross-side
commutation that the equivalences do not address.

## Four-element blocks prove all mate commutation

The cyclic-block theorem partitions `M` canonically into four-element
blocks. There is a permutation `σ` of the blocks such that every
`B` edge goes from a block `X` to `σ(X)`.

A connected component of the bipartite graph therefore lies between
one left block `X` and one right block `σ(X)`. It has at most four
vertices on each side. Its length is divisible by four, so its length
is four or eight. This proves statement 1 and hence all five equivalent
statements above.

There is also a direct argument that includes the cross-side mates.
Every nonempty fiber of `L_t` is a set `B(a)` and thus lies in one
four-element block. Every nonempty fiber of `R_u` is a set `B^-(b)`
and has the same property. Hence every `λ_t` and `ρ_u` preserves
each block and restricts there to a fixed-point-free involution.

On a four-element set, the three fixed-point-free involutions are
the three double transpositions. Together with the identity they form
a Klein four group. They commute pairwise. Applying this observation
on every block proves

\[
\boxed{\lambda_t\lambda_v=\lambda_v\lambda_t,\qquad
\rho_u\rho_w=\rho_w\rho_u,\qquad
\lambda_t\rho_u=\rho_u\lambda_t
\quad(t,u,v,w\in T).} \tag{3}
\]

The left and right restrictions are always distinct. For any top
parameters `t,u` and any `x`, the path

\[
t*x\mathrel B x\mathrel B x*u
\]

is good, so

\[
\boxed{(t*x)*(x*u)=x.} \tag{4}
\]

Consequently no distinct points have both the same `L_t` output
and the same `R_u` output. In particular, `λ_t(x)≠ρ_u(x)`.
On each block these are therefore two distinct double transpositions,
and they generate the transitive Klein four action. Thus, for any
fixed `t,u∈T`,

\[
\boxed{\{x,\lambda_t(x),\rho_u(x),\lambda_t\rho_u(x)\}
=\text{the canonical four-element block containing }x.} \tag{5}
\]

No ordinary adjacency assumption on `u,t` is needed in (4): it uses
the now-proved goodness of every canonical two-edge path.

## Eliminating the mate functions from the commutator

Fix central `h` and enumerate

\[
 \operatorname{Row}(h)=\{s,t\},\qquad
 \operatorname{Col}(h)=\{r_0,r_1\}.
\]

For `v∈Row(h)`, the sharp edge `h⇒v` gives the rectangular
factorization

\[
 x=(v*x)*(x*h).
\]

More precisely, the inverse bijections are

\[
 x\longmapsto(v*x,x*h),\qquad
 (a,r)\longmapsto a*r
 \quad\text{between }M\text{ and }Row(v)\times Col(h).
\]

Therefore, if `x*h=r_0`, then

\[
 \lambda_v(x)=(v*x)*r_1,
 \qquad \lambda_v(x)*h=r_1. \tag{6}
\]

This is the other point of the fiber, not just another point with the
same output: the two values of the second coordinate exhaust `Col(h)`.
After one mate operation the next operation must use `r_0` instead.
Thus commutation of `λ_s,λ_t`, on inputs with `x*h=r_0`, is exactly
the conditional identity

\[
 \boxed{
 x*h=r_0\quad\Longrightarrow\quad
 \bigl(t*((s*x)*r_1)\bigr)*r_0
 =\bigl(s*((t*x)*r_1)\bigr)*r_0.
 } \tag{7}
\]

The analogous identity with `r_0,r_1` exchanged handles the other
inputs. These identities were originally targets equivalent to the
cycle bound. They now follow from the proved mate commutation in (3).

## A criterion for goodness of canonical two-edge paths

This local criterion predates full-core sharp regularity. The latter
now proves goodness for both top adjacency types, with no extra
hypothesis. The criterion remains a direct proof in one of the types.

Let `D` be ordinary adjacency restricted to `T`. Every row and column
of this four-by-four zero-one matrix has sum two.

Consider a path `aBbBc`. Suppose there are `t∈Q(b)` and `u∈Q(c)`
with an ordinary top edge `t→u`. Write `u=t*z`. Equation (1) gives
`a*t=b` and `b*u=c`. The universal absorption identity

\[
 a*((a*t)*(t*z))=a*t
\]

then gives `a*c=b`. Thus this `B`-path is good.

If there is no edge from `Q(b)` to `Q(c)`, both top rows indexed by
`Q(b)` must equal `T\Q(c)`: they each have two members, all outside
the two-element set `Q(c)`. In particular, they are equal.

Consequently, **if the four rows of `D` are distinct, every two-edge
path in `B` is good**. Unique goodness then implies that `B²` is a
zero-one matrix: there is at most one `B`-middle between any ordered
pair of vertices.

There are only two possible row-multiplicity types for `D`. If two
rows are equal, they exhaust the column sums in their two columns;
the remaining two rows must both be the complementary pair. Hence
`D` either has four distinct rows or has two repeated row pairs.
In the second case a bad `B`-path necessarily has `Q(b)` equal to
one repeated-row pair and `Q(c)` equal to the complement of its
common row. This is a necessary condition, not a sufficient condition
for badness.

There is also an unconditional extension bound. The two vertices
`c_0,c_1∈B(b)` have complementary profiles `Q(c_0),Q(c_1)`. A
nonempty top row cannot avoid both of these sets. Thus, for any fixed
edge `aBb`, at least one of its two `B`-extensions is good by the
criterion above. Every `B`-edge has at most one bad `B`-extension.
The column-dual argument gives at most one bad `B`-predecessor.

## Central coordinates on each bipartite side

Fix a central `h`. The map

\[
\boxed{x\longmapsto(h*x,x*h)
\text{ is injective on each side of every bipartite }B
\text{ component}.} \tag{8}
\]

This does not assert injectivity on all of `M`, or even on every
four-element block. A block may split into two sides of size two.

Here is the proof for a right side `U`. Write `Row(h)={s,t}`.
The sharp rectangles used in (6) show that both `λ_s` and `λ_t`
swap the two possible values of `x*h`. If `|U|=2`, either mate
exchanges its two elements, whose second coordinates therefore differ.

Suppose `|U|=4`. Then `U` is one entire canonical block, and the
opposite alternating matchings `λ_s,λ_t` are distinct on it.
Their product `η` is the third nonidentity element of its Klein
four group. Since both factors swap the second coordinate, `η`
preserves that coordinate. The second coordinate is nonconstant on
`U`, so its two fibers are precisely the two pairs exchanged by `η`.

Choose `u∈Col(h)`. The mate `ρ_u` is distinct from both left
mates on `U`, and hence equals `η` there. The sharp edge `u⇒h`
gives the rectangular recovery

\[
x=(h*x)*(x*u).
\]

Thus `h*x` differs on the two points in any `ρ_u`-pair, since
their `x*u` outputs agree. This distinguishes the two points in
each second-coordinate fiber and proves (8). The argument for a left
side is dual. In particular, on any side of size four, the coordinate
map is a bijection onto `Row(h)×Col(h)`.

## Historical experiments

Direct checks on the nine minimum-degree-two order-eight tables and
the 180 archived order-sixteen tables found:

* All maximum left kernel mates commute, all maximum right kernel
  mates commute, and every maximum left mate commutes with every
  maximum right mate.
* For every central `h`, the coordinate map
  `x↦(h*x,x*h)` is injective on each side of each bipartite
  `B`-component.

These observations are now theorems (3) and (8). The second also
implies the cycle bound, since there are only `2·2=4` possible
coordinates. Historically it was unproved: central rectangle closure
alone does not establish it, and the coordinate map is not injective
on all of `M` in general. Its proof above uses the additional
four-element-block and cross-mate conclusions.

These 189 tables are experimental evidence, not an exhaustive search
at order sixteen. A short proof search using one complete order-eight
central core, its exact central rows and columns, and the two-element
top-fiber bounds did not establish mate commutation. That failed search
is historical: the cycle bound, global commutation, and general
`B²`-goodness now follow from the pen-and-paper full-core theorems,
not from the finite bank or the search.
