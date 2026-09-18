# Top kernel mates and the cycles of the canonical relation

Research note, 18 September 2026. This gives a cycle description of the
kernel-mate involutions of maximum-degree translations in a finite E1485
magma of minimum degree two. It proves an equivalence between their
same-side commutation and a bound on the canonical bipartite cycles.
**Neither that cycle bound nor commutation is proved here.** A separate
criterion below proves goodness of all canonical two-edge paths for one
of the two possible top adjacency types.

We use the finite structure theorems in
[the graph note](1485_graph_research.md), the
[four-central-vertex theorem](1485_two_central_exclusion.md), and the
[full-central-core results](1485_full_central_core.md). These are
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
choice. These equivalences do not prove any of the five statements.
They also do not assert commutation between a left kernel mate `λ_t`
and a right kernel mate `ρ_u`.

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
 \qquad \lambda_v(x)*h=r_1. \tag{3}
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
 } \tag{4}
\]

The analogous identity with `r_0,r_1` exchanged handles the other
inputs. Proving these identities under the full finite central-core
hypotheses would prove the cycle bound above. Formula (3) and the
equivalence with (4) are proved; identity (4) itself remains a target.

## A criterion for goodness of canonical two-edge paths

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

## Experimental targets and limits

Direct checks on the nine minimum-degree-two order-eight tables and
the 180 archived order-sixteen tables found:

* All maximum left kernel mates commute, all maximum right kernel
  mates commute, and every maximum left mate commutes with every
  maximum right mate.
* For every central `h`, the coordinate map
  `x↦(h*x,x*h)` is injective on each side of each bipartite
  `B`-component.

The second observation would imply the cycle bound, since there are
only `2·2=4` possible coordinates. It is **not proved** by central
rectangle closure: the coordinate map is not asserted to be injective
on all of `M`.

These 189 tables are experimental evidence, not an exhaustive search
at order sixteen. A short proof search using one complete order-eight
central core, its exact central rows and columns, and the two-element
top-fiber bounds did not establish mate commutation. No cycle bound,
global commutation theorem, or general `B²`-goodness assertion is being
claimed on that basis.
