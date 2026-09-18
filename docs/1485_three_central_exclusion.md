# Minimum degree two excludes exactly three central vertices

Research note, 18 September 2026. This proves the following global finite
statement, without a restriction on the other occurring degrees:

**Theorem.** A finite E1485 magma whose minimum translation degree is two
cannot have exactly three central vertices.

The proof uses the finite degree, uniform-fiber, and sharp-edge theorems in
[the graph note](1485_graph_research.md), strict degree decrease from
[the projection note](1485_image_research.md), and the incidence and
degree-three results in [the minimum-degree-two note](1485_min_degree_two.md).
No assertion here has been added to Lean. The separate
[two-central-vertex proof](1485_two_central_exclusion.md) excludes the
other nonstandard possibility and completes the central-cardinality
theorem at minimum degree two.

## Setup and finite consequences used

Suppose for a contradiction that `M` has order `n`, minimum degree two,
and central set `Z` of cardinality three. Write `T` for its set of
maximum-degree vertices. The cited results give:

* The maximum degree is `s=n/2`, and `|T|=4`.
* Every vertex has exactly two ordinary predecessors in `T` and exactly
  two ordinary successors in `T`.
* Every nonempty fiber of a translation at a vertex of `T` has size two.
* Every vertex has a sharp predecessor and successor. A sharp edge
  `x⇒y` satisfies `d(x)d(y)=n`, and any two-edge path containing a
  sharp edge is good.
* The product `x*y` is the unique minimum-degree middle among all paths
  from `x` to `y`. A bad path has strictly larger middle degree than
  its good replacement.
* Degree three occurs: the minimum-degree-two note proves that absence
  of degree three is equivalent to having four central vertices.

Here `Z` and `T` are disjoint. Otherwise a vertex would have both minimum
and maximum degree, forcing `s=2`, `n=4`, and every vertex central.

For later use, let `A={q:d(q)=3}`. For `t∈T`, let `ℓ_t` be the number
of its central successors and `α_t` its number of successors in `A`.
The minimum-degree-two note proves

\[
 \alpha_t\le4-2\ell_t. \tag{1}
\]

Indeed, each central output of `L_t` uses two top inputs. A degree-three
output has exactly two top successors and one other successor; the latter
is its unique sharp successor. Its two-element `L_t`-fiber contains that
sharp successor and one top input. Thus these outputs use
`2ℓ_t+α_t` distinct elements of the four-element set `T`. The dual bound
holds for central and degree-three predecessors of `t`.

## Equal adjacency sets give equal translations

If `Row(x)=Row(y)`, then for any `z` the possible middles of paths from
`x` to `z` and from `y` to `z` form the same set,
`Row(x)∩Col(z)=Row(y)∩Col(z)`. Their unique minimum-degree middle is
therefore the same, giving `x*z=y*z` for every `z`. Consequently equal
ordinary rows imply `L_x=L_y`. Dually, equal ordinary columns imply
`R_x=R_y`.

Two central vertices cannot have both equal rows and equal columns. To
see this, fix any central vertex `h`. Every central vertex `x` satisfies

\[
 x=(h*x)*(x*h). \tag{2}
\]

If central `x,y` have both translation equalities, then `h*x=h*y` and
`x*h=y*h`, so (2) gives `x=y`.

## Excluding a connected incidence path

Form the loopless multigraph on `T` whose three edges are the sets
`Row(z)`, for `z∈Z`. Its degree multiset is `{1,1,2,2}`. As established
in the minimum-degree-two note, it is either a path on four vertices or
a double edge together with a disjoint single edge. The same alternatives
hold for the multigraph whose edges are `Col(z)`.

Suppose first that the row multigraph is a path. For any `x∈M`, its
set of top predecessors meets each `Row(z)` in exactly one vertex: all
paths starting at the central vertex `z` are good. On a connected path,
this forces the top predecessor set to be one of its two bipartition
classes. Each class has two vertices.

It follows that the two top vertices in each bipartition class have
identical ordinary rows: either both precede `x`, or neither does, for
every `x`. Hence they have identical left translations.

Take `t,v∈T`, let `t'≠t` be the other vertex in the same bipartition
class as `t`, and put `q=t*v`. Then `t'*v=q` as well. The two-element
fiber of `R_v` at `q` is therefore exactly `{t,t'}`. Choose a sharp
predecessor `e⇒q`. Since `q→v`, the path `e⇒q→v` is good, so
`e*v=q`. Thus `e∈{t,t'}` is top. Sharpness gives
`d(q)=n/d(e)=2`, making `q` central.

We have shown `T*T⊆Z`. Each central vertex accounts for exactly four
ordered top endpoint pairs, namely its two predecessors times its two
successors. These pairs are disjoint by unique goodness. Since every
top-top product is central, they exhaust `T×T`, giving `4|Z|=16`,
contrary to `|Z|=3`.

The column-path case is dual: its two bipartition classes give pairs
of top vertices with identical right translations. A fiber of `L_t`
then contains an entire such pair; a sharp successor of its output must
belong to that pair, again making every top-top product central.

## Excluding two double-edge incidence patterns

Both incidence multigraphs must therefore consist of a double edge and
a disjoint single edge. The duplicated pair of central vertices for
the row multigraph cannot be the duplicated pair for the column
multigraph: the preceding translation argument and (2) would identify
those two central vertices.

Two distinct two-element subsets of the three-element set `Z` have
exactly one common element. We may consequently label its vertices
`a,b,c` so that

\[
 \begin{aligned}
 U&=\operatorname{Row}(a)=\operatorname{Row}(b),
 &V&=\operatorname{Row}(c),\\
 X&=\operatorname{Col}(a)=\operatorname{Col}(c),
 &Y&=\operatorname{Col}(b).
 \end{aligned} \tag{3}
\]

The pairs `U,V` partition `T`, and so do `X,Y`. Each of their four
intersections has exactly one element: for any central endpoints, every
two-edge path is good, so its row-column intersection has cardinality
one.

The top endpoint pairs admitting a central middle are precisely

\[
 X\times U,\qquad Y\times U,\qquad X\times V, \tag{4}
\]

corresponding to middles `a,b,c`, respectively. In particular, **no
ordered pair in `Y×V` admits a central middle**.

Every `t∈X` has the two central successors `a,c`. Equation (1) therefore
excludes degree-three successors of `t`. Each `q∈A` has two top
predecessors, so both must be the members of `Y=T\X`. Dually, every
`t∈U` has two central predecessors `a,b`, and the dual of (1) excludes
degree-three predecessors of `t`. The two top successors of `q` must
therefore be exactly `V=T\U`. We have proved

\[
 \operatorname{TopPred}(q)=Y,\qquad
 \operatorname{TopSucc}(q)=V\qquad(q\in A). \tag{5}
\]

Choose `q∈A`, which exists, and fix `t∈Y`. For each `v∈V`, equation
(5) gives a path `t→q→v`. If it were bad, strict degree decrease would
give `d(t*v)<3`. The minimum degree is two, so the replacement middle
would be central, contradicting (4). Thus both paths are good and

\[
 t*v=q\qquad(v\in V). \tag{6}
\]

Finally choose a sharp successor `q⇒w`. Its degree is `n/3`, strictly
less than the top degree `n/2`, so `w∉T`. The path `t→q⇒w` is good,
giving `t*w=q`. Together with (6), the fiber `L_t^{-1}(q)` contains
both elements of `V` and the distinct element `w`. This contradicts its
cardinality two and completes the theorem.

## The missing central corner

As a consequence, in a minimum-degree-two finite model, the existence
of three distinct central vertices forces exactly four central vertices:
the central rectangle bound gives `|Z|≤4`, and the theorem excludes
`|Z|=3`.

In particular, for central `a,b,c` with the translation equalities in
(3), the missing corner

\[
 p=(a*b)*(c*a)
\]

is central. Indeed `p∈B_a`, where
`B_a={u*v:u∈Row(a),v∈Col(a)}` has four elements and contains every
central vertex. Thus `B_a=Z`. This conclusion uses finiteness and the
minimum-degree-two hypothesis; unrestricted central rectangle closure
remains false in infinite models.
