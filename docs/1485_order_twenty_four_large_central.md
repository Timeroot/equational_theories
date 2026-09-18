# Order twenty-four at minimum degree three: at most six central vertices

Research note, 18 September 2026. This is a pen-and-paper reduction,
not a Lean declaration or a complete exclusion of order 24.

**Theorem.** If a finite E1485 magma has order 24 and minimum
translation degree three, it has at most six central vertices.

We use the finite degree, centrality, uniform-fiber, and strict-descent
theorems from the [graph](1485_graph_research.md) and
[projection](1485_image_research.md) notes. The
[two-degree theorem](1485_two_degree_lower_bound.md) and
[full-central-core gaps](1485_min_two_neighbor_gap.md) are also used.

## Basic incidence constraints

The occurring degrees are exactly `3,4,6,8`: degrees divide 24 and
come in complementary pairs, and the two-degree possibility `3,8`
is excluded by the two-degree cardinality theorem.
Write `Z,A,B,T` for these respective classes, and put

\[
 m=|Z|,\quad f=|A|,\quad g=|B|,\quad h=|T|,
 \qquad m+f+g+h=24. \tag{1}
\]

Here `f,g>0`, and the central rectangle bound gives `m≤9`.
The case `m=9` would give a full central core. Its degree gap excludes
degree four, which lies strictly between three and six. Thus `m≤8`.
We will exclude `m=7,8`.

For each top vertex `t`, let `k_t^-` and `k_t^+` be the numbers of
its central predecessors and successors. Both lie in `{1,2,3}`.
Central incidence and unique goodness give

\[
 \sum_t k_t^- =\sum_t k_t^+=3m,
 \qquad \sum_t k_t^-k_t^+=m^2. \tag{2}
\]

The two signs are kept separate throughout; their equality at a top
vertex is not assumed. Since every `k_t^+≥1`, equation (2) also gives
`m²≥3m`, and hence `m≥3`.

For any vertex `x`, every central row meets its top predecessor set
exactly once. Summing this observation, and its dual, gives

\[
 \sum_{t\in T\cap\operatorname{Col}(x)}k_t^-=m,
 \qquad
 \sum_{t\in T\cap\operatorname{Row}(x)}k_t^+=m. \tag{3}
\]

A degree-four vertex can have neighbors only in `B` and `T`, and
its `B` neighbors are precisely its sharp neighbors. There is at least
one sharp neighbor in each direction, so it has at most three top
neighbors. If `m≥7`, equation (3) forces at least three top neighbors.
Thus every `A` vertex has exactly three top neighbors and one sharp
`B` neighbor in each direction. Counting sharp `A,B` edges gives

\[
 g\le f\le3g. \tag{4}
\]

At a top vertex, let `α_t` count its successors in `A`. The fiber of
`L_t` at a central output consists of three top inputs. A degree-four
output has one sharp `B` successor in its three-element fiber; its
other two inputs must be top. Consequently

\[
 3k_t^++2\alpha_t\le h,
 \qquad \sum_t\alpha_t=3f,
 \qquad \sum_t k_t^-\alpha_t=mf. \tag{5}
\]

The last equality follows from (3). There is an entirely dual version.
Also

\[
 \alpha_t\le g: \tag{6}
\]

different `A` successors of `t` must have different sharp successors
in `B`, or two good paths would have the same endpoints and different
middles. Summing the first inequality in (5) gives

\[
 9m+6f\le h^2. \tag{7}
\]

## Restricting the top-class size

Put `a_t=3−k_t^-` and `b_t=3−k_t^+`. These integers belong to
`{0,1,2}`, and (2) gives

\[
 \sum a_t=\sum b_t=3h-3m,
 \qquad \sum a_tb_t=m^2-18m+9h.
\]

Use `0≤a_tb_t≤a_t+b_t` to obtain

\[
 \left\lceil2m-\frac{m^2}{9}\right\rceil
 \le h\le
 \left\lfloor\frac{m(12-m)}3\right\rfloor.
 \tag{8}
\]

Thus `m=8` allows `h=9,10`, whereas `m=7` allows `h=9,10,11`.
For either value of `m`, `h=9` is impossible: equations (1) and (4)
force `f≥4`, contradicting (7).

## Eight central vertices are impossible

Suppose `m=8`. We have just proved `h=10`. Fix `a∈A`, and write
`X` for its three top predecessors. Since each `t∈X` has `α_t≥1`,
(5) gives `k_t^+≤2`. Meanwhile (2) gives

\[
 \sum_t k_t^-(3-k_t^+)=9m-m^2=8.
\]

By (3), `Σ_{t∈X}k_t^-=8`. All terms are nonnegative, so equality
forces `k_t^+=2` for each of the three elements of `X` and
`k_t^+=3` for every other top vertex. Their sum would be
`3h−3=27`, contradicting `Σ k_t^+=3m=24`.

## Seven central vertices cannot have ten top vertices

Suppose `m=7,h=10`. Equations (1) and (4) give `f≥4`.
For `k_t^+∈{1,2,3}`, inequality (5) says exactly

\[
 \alpha_t\le2(3-k_t^+)-\mathbf1_{k_t^+=1}.
\]

There is at least one top vertex with `k_t^+=1`. Otherwise the sum
`Σ k_t^+=21` on ten vertices would force nine values two and one
value three. Then `Σ k_t^-k_t^+≤2·21+3=45`, contrary to (2),
which requires 49. Multiplying the displayed bound by `k_t^-` and
summing therefore gives

\[
 7f=\sum_t k_t^-\alpha_t
 <2\sum_t k_t^-(3-k_t^+)=2(63-49)=28.
\]

This contradicts `f≥4`.

## The three central profiles when `m=7,h=11`

Only `h=11` remains. Equations (1) and (4) give precisely
`(f,g)=(3,3)` or `(4,2)`.

In the deficit notation above, `Σa=Σb=12` and `Σab=22`.
Thus

\[
 \sum_t(a_t+b_t-a_tb_t)=2. \tag{9}
\]

The summand vanishes only for top types `(k^-,k^+)=(1,1),(3,3)`;
it is one for `(1,2),(2,1),(2,2),(2,3),(3,2)` and two for
`(1,3),(3,1)`. Equal marginal sums exclude a single type with
summand two. Two types with summand one must balance their marginal
differences; the sum `Σk^-=21` excludes the two possibilities whose
combined first coordinates are odd. The resulting complete list is:

| Profile | Common types | Remaining two top vertices |
| --- | --- | --- |
| Symmetric | five `(1,1)`, four `(3,3)` | two `(2,2)` |
| Asymmetric | five `(1,1)`, four `(3,3)` | `(2,1)` and `(2,3)` |
| Dual asymmetric | five `(1,1)`, four `(3,3)` | `(1,2)` and `(3,2)` |

This list is a small integer calculation from (2), not an enumeration
of multiplication tables.

### The case `(f,g)=(4,2)`

Now `Σα=12` and `Σk^-α=28`. Inequalities (5)--(6) give
`α_t≤2` everywhere, and `α_t≤1` where `k_t^+=3`.

In the symmetric profile, the total `α` on weight-three vertices
is at most four, and its total on weight-two vertices at most four.
Therefore `Σk^-α≤12+2·4+4=24`.
In the asymmetric profile, those two bounds are four and three, giving
`Σk^-α≤12+2·4+3=23`.
In the dual asymmetric profile there are no weight-two vertices, and
the total `α` on weight-three vertices is at most six, giving
`Σk^-α≤12+2·6=24`.
All three bounds contradict the required value 28.

### Asymmetric profiles with `(f,g)=(3,3)`

Write `t=(2,1)` and `u=(2,3)` for the exceptional vertices in the
asymmetric profile. Now `Σα=9` and `Σk^-α=21`.
Let `H,M,L` be the totals of `α` on vertices of respective first
weights three, two, one. We have `H≤4`, `α_t≤3`, and `α_u≤1`,
so `M≤4`. The two sums give

\[
 H+M+L=9,\qquad 3H+2M+L=21,
\]

or `M+2L=6` and `H=3+L`. The bounds imply
`L=1,M=4,H=4`. Hence `α_t=3` and `α_u=1`.

Every `A` vertex therefore has `t` as a top predecessor. Its three
top predecessor weights sum to seven by (3). One weight is two,
so the other two must be two and three. The only other weight-two
top vertex is `u`. Thus `u` is also a predecessor of every `A`
vertex, contrary to `α_u=1`.

The dual argument excludes the dual asymmetric profile.

### The symmetric profile with `(f,g)=(3,3)`

Again write `H,M,L` for the totals on first weights three, two, one.
We have `Σα=9`, `Σk^-α=21`, `H≤4`, and `M≤4`. Thus

\[
 21=9+2H+M\le9+8+4=21.
\]

Equality forces each weight-three vertex to have one `A` successor,
and each of the two weight-two vertices to have two. The dual argument
gives the same numbers of `A` predecessors.

A three-element top neighborhood with weight sum seven must have
weights `3,3,1` or `3,2,2`. Thus a top neighborhood containing either
weight-two vertex contains both. The two weight-two top vertices
consequently have the same two `A` successors, a set `I`, and the
same two `A` predecessors, a set `J`.

Every pair in `J×I` has both these top vertices as common middles.
On the other hand, `f=g=3` and each `A` vertex has exactly one sharp
neighbor in either direction. Every `B` vertex needs a sharp neighbor,
so its sharp degrees are also one. Therefore the `A×A` pairs with
a sharp `B` middle form a permutation graph on the three `A` vertices.

For any other `A×A` pair, its good middle must be top: its only possible
ordinary middles lie in `B` or `T`. It can have no second top middle,
because a bad middle has strictly larger degree than the good middle,
and all top vertices have degree eight. Thus every pair in `J×I`
must lie in that permutation graph.

This is impossible: `I` and `J` both have two elements, whereas a
permutation graph contains only one pair in each row. The final profile
is excluded, proving `m≤6`.

## What remains

The result leaves central cardinalities three through six as possible
incidence cases at order 24 and minimum degree three. It does not claim
that any of them is realizable. The minimum-degree-two case is excluded
separately by the
[six-times-square full-core theorem](1485_six_times_square_full_core.md).
