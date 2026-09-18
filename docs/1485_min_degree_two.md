# Finite E1485 magmas of minimum degree two

Research note, 18 September 2026. Assume the finite degree, centrality,
uniform-fiber, and sharp-edge theorems in
[the graph note](1485_graph_research.md). This note proves two global
consequences when the minimum translation degree is two:

* Exactly four vertices have maximum degree.
* Every vertex has exactly two maximum-degree predecessors and exactly
  two maximum-degree successors.

It also narrows the four-degree case of order twelve and excludes its
possibilities with three or four central vertices. The subsequent
[order-twelve proof](1485_order_twelve.md) excludes the other two
possibilities. No assertion here has been added to Lean.

## The central incidence counts

Let the order be `n`, let `Z` be the central set, of size `m`, and let
`T` be the set of vertices of maximum degree `s=n/2`, of size `h`.
Every edge incident with a central vertex joins it to `T` and is sharp.
Every vertex of `T` has a sharp predecessor and successor, necessarily
central. Sharp degrees are at most the minimum ordinary degree, two.

Write `B` for adjacency from `Z` to `T` and `C` for adjacency from
`T` to `Z`. Every row of `B` and every column of `C` sums to two.
Centrality and unique goodness give

\[
 BC=J_{m,m}.
\]

For `v∈T`, let `k_v^-` and `k_v^+` be its numbers of central
predecessors and successors. Both are in `{1,2}`. Counting edges and
then all entries of `BC` gives

\[
 \sum_{v\in T}k_v^-=\sum_{v\in T}k_v^+=2m,
 \qquad \sum_{v\in T}k_v^-k_v^+=m^2. \tag{1}
\]

The central rectangle injection gives `m≤2²=4`. Since each `k_v^+≥1`,
(1) also gives `m²≥2m`, so `m≥2`.

Let `p,q,q',u` count the vertices of `T` of respective types
`(k^-,k^+)=(1,1),(1,2),(2,1),(2,2)`. Equality of the first two sums
in (1) gives `q=q'`, and the remaining equations are

\[
 2m=p+3q+2u,\qquad m^2=p+4q+4u.
\]

For `m=2,3,4`, their nonnegative integer solutions are respectively

| `m` | `p` | `q=q'` | `u` | `h=p+2q+u` |
|---|---|---|---|---|
| 2 | 4 | 0 | 0 | 4 |
| 3 | 1 | 1 | 1 | 4 |
| 4 | 0 | 0 | 4 | 4 |

For example, subtraction gives `q+2u=m²−2m`; substitution in the
first equation leaves the displayed possibilities immediately.
Thus exactly four vertices have maximum degree.

## Exactly two top neighbors at every vertex

Fix an arbitrary vertex `x`, and let `X⊆T` be its set of top
predecessors. For each central `z`, every path `z→v→x` is good.
Its unique middle `z*x` has maximum degree because it is adjacent
to `z`. Therefore

\[
 |\operatorname{Row}(z)\cap X|=1 \qquad(z\in Z). \tag{2}
\]

Form a loopless multigraph on the four vertices of `T`, with one
undirected edge `Row(z)` for each `z∈Z`; repeated edges are allowed.
Its vertex degrees are the numbers `k_v^-`. Equation (2) says that
the indicator of `X` takes opposite values at the ends of every edge.

If `m=2`, all four multigraph degrees are one, so it is a perfect
matching and `|X|=2`.

If `m=3`, the degree multiset is `{1,1,2,2}`. A loopless multigraph
with these degrees is either a path on four vertices or a double edge
and a disjoint single edge. In a four-vertex path the two bipartition
classes have size two, so (2) gives `|X|=2`. In the other case (2)
chooses one endpoint from each of the two disjoint pairs, again giving
`|X|=2`.

If `m=4`, all four degrees are two. Sum (2) over the four central
vertices: each element of `X` is counted twice, so `2|X|=4`.

This proves that every vertex has two top predecessors. Apply the
same argument to `Col(z)` and the numbers `k_v^+` to obtain exactly
two top successors. The proof permits `s=2`, in which case every
vertex is central and top and the result gives `n=4`.

## A bound on the number of degree-three vertices

Let `A` now denote the degree-three class in an arbitrary minimum-degree-two
model, and put `f=|A|`. A vertex `a∈A` has two top successors and
one other successor. Since it has a sharp successor, and a sharp
successor has degree `n/3<s`, that other successor is its unique sharp
successor. The analogous statement holds for predecessors.

Fix a top vertex `t`, with `ℓ_t` central successors, and let `α_t`
count its successors in `A`. Every nonempty `L_t`-fiber has size two.
Each central output uses two top inputs: its fiber is its ordinary row,
by sharpness. For an output `a∈A`, its unique sharp successor is one
input, because a path containing that sharp edge is good. Its other
input must be one of its two top successors. Thus these outputs use
`2ℓ_t+α_t` distinct top inputs. There are four available, giving

\[
 \alpha_t\le4-2\ell_t.
\]

Each `a∈A` has two top predecessors, while `Σ_t ℓ_t=2m`.
Summing the inequality proves

\[
 \boxed{|\{x:d(x)=3\}|\le8-2m.} \tag{2a}
\]

In particular, three central vertices allow at most two degree-three
vertices, and four central vertices allow none.

## Four central vertices are equivalent to absence of degree three

Conversely, suppose degree three does not occur. By degree reciprocity,
degree `n/3` does not occur either. If a degree-four vertex `u` exists,
it has two top successors. Its other two successors have degree at
least `n/4`, by the ordinary-edge degree bound, and strictly less than
`n/2`. Since their degrees divide `n`, the only possibilities are
`n/4` and `n/3`: take the integer complementary degrees, which are
strictly greater than two and at most four. The latter possibility is
absent, so both other successors have degree `n/4` and are sharp.

Consequently, no product `t*v` of two top vertices can have degree four.
If its output were such a vertex `u`, the two-element fiber of `L_t`
at `u` would already contain both sharp successors of `u`, neither
top. There would be no room for the top input `v`.

The three-degree product bound gives `d(t*v)≤4` for top `t,v`.
Degree three is absent, and degree four has just been excluded for
these products. Therefore every top-top product is central. Each central
middle accounts for exactly four ordered top endpoint pairs, and these
pairs are disjoint by unique goodness. They exhaust all sixteen pairs,
so `4m=16` and `m=4`.

Together with (2a), this proves the global equivalence

\[
 \boxed{m=4\quad\Longleftrightarrow\quad
           \text{no vertex has degree three}.} \tag{2b}
\]

Thus any minimum-degree-two model with fewer than four central vertices
must have degree three and order divisible by six. If `m=3`, its
degree-three class has size one or two; if `m=2`, its size is at most
four. In particular **orders not divisible by three have four central
vertices** whenever the minimum degree is two. This does not yet imply
sharp-degree regularity at every other vertex.

## The four-degree possibility at order twelve

Suppose the order is twelve and the occurring degrees are exactly
`2,3,4,6`. Let `U` and `V` be the degree-three and degree-four classes,
of sizes `f,g>0`. The preceding theorem gives `|T|=4`, and hence

\[
 f+g=8-m. \tag{3}
\]

Every degree-three vertex has two top successors and predecessors.
Its remaining successor and predecessor have degree four: the edge
degree inequality excludes degrees two and three, and the unique
remaining edges are sharp because `3·4=12`. Thus every vertex of `U`
has sharp in-degree and out-degree one.

A degree-four vertex also has two top successors and predecessors.
Its other two successors lie in `U∪V`, and likewise for predecessors.
The edges to `U` are sharp, and every such vertex has at least one
sharp edge in each direction. Consequently its sharp in-degree and
out-degree each belong to `{1,2}`. If the out-degree is `p`, its
number of successors within `V` is `2−p`; the corresponding statement
holds for in-degrees.

Counting sharp edges between `U` and `V` in each direction gives

\[
 g\le f\le2g. \tag{4}
\]

Equations (3) and (4) leave only these possibilities:

| `m` | `f` | `g` | Ordinary adjacency restricted to `V` |
|---|---|---|---|
| 2 | 3 | 3 | A permutation digraph on three vertices |
| 2 | 4 | 2 | No edges |
| 3 | 3 | 2 | Exactly one edge |
| 4 | 2 | 2 | A permutation digraph on two vertices |

Here a permutation digraph includes possible loops. In the first and
last rows, every sharp in-degree and out-degree on `V` is one, so
every internal in-degree and out-degree is one. In the second row,
all sharp degrees on `V` are two. In the third row the two sharp
out-degrees are one and two, as are the two sharp in-degrees, leaving
exactly one internal edge.

These are necessary incidence patterns, not constructions. The last
two cases are excluded below; the first two are excluded in the
[order-twelve proof](1485_order_twelve.md).

## Four central vertices exclude an outside vertex of degree three

Continue with minimum degree two, but allow arbitrary order. Suppose
`m=4`, and put `K=Z∪T`. If the whole magma has order four it is central
and there are no outside vertices. Otherwise `Z` and `T` are disjoint,
and `|K|=8`.

Every ordered pair of top vertices has a central good middle: the four
central vertices each account for four distinct endpoint pairs in
`T×T`, and these sixteen pairs exhaust `T×T`. Thus `T*T⊆Z`. Every
product with a central factor is top, so `K` is a submagma.

For `t∈T`, its restricted row on `K` has exactly four outputs. Its
two central successors occur as products with top inputs: if `t→z`
and `z→u` with `u∈T`, centrality gives `t*u=z`. Its two top successors
occur as products with central inputs: if `t→u` and `u→z` with
`z∈Z`, centrality gives `t*z=u`. No other outputs on `K` are possible.

The global nonempty fibers of `L_t` have size `n/(n/2)=2`. Its eight
inputs in `K` already fill four such fibers, so no input outside `K`
can produce an output in `K`. The dual argument applies to `R_t`.
Consequently, for `X=M\K`,

\[
 T*X\subseteq X,\qquad X*T\subseteq X. \tag{5}
\]

Now fix `x∈X`. The four inputs `t∈T` all give outputs `x*t∈X`.
For any one such output `y`, every corresponding input `t` is a top
successor of `y`, by the product path `x→y→t`. Each vertex has only
two top successors, so at least two distinct outside outputs occur.
The row of `x` also contains its two top successors. Therefore

\[
 x\notin Z\cup T\quad\Longrightarrow\quad d(x)\ge4
 \qquad(m=4). \tag{6}
\]

In particular the order-twelve possibility `(m,f,g)=(4,2,2)` is
impossible, because it contains degree-three vertices outside `Z∪T`.

## Three central vertices are impossible at order twelve

Suppose `(m,f,g)=(3,3,2)`. The central incidence table supplies a top
vertex `t` with two central predecessors and one central successor.
Let `α^+,α^-` count its degree-three successors and predecessors,
and `β^+,β^-` its degree-four successors and predecessors. Put
`Δα=α^+−α^-` and `Δβ=β^+−β^-`.

Its ordinary in-degree and out-degree are both six, and it has two
top neighbors in each direction. Therefore

\[
 Δα+Δβ=1.
\]

The weighted balance identity, obtained by counting products equal to
`t` using the uniform translation fibers, is

\[
 \sum_{y\in\operatorname{Row}(t)}\frac1{d(y)}
 =\sum_{y\in\operatorname{Col}(t)}\frac1{d(y)}.
\]

It gives `−1/2+Δα/3+Δβ/4=0`, or `4Δα+3Δβ=6`.
Together the two equations imply `Δα=3` and `Δβ=−2`.
Since there are only three degree-three vertices, `t` has all of them
as successors and none as predecessors.

Each degree-three vertex has one sharp degree-four successor. There
are three such sharp edges and only two degree-four vertices, so some
degree-four vertex `b` has two distinct sharp predecessors `a,a'`
of degree three. Both paths

\[
 t\to a\Rightarrow b,
 \qquad t\to a'\Rightarrow b
\]

are good, because each contains a sharp edge. They have the same
endpoints and different middles, contradicting unique goodness.
Thus the possibility `(m,f,g)=(3,3,2)` is excluded.
