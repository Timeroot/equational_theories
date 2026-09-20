# Three central vertices cannot have nine degree-four vertices

Research note, 18 September 2026. This is a pen-and-paper restriction
independent of the total order; it is not yet formalized in Lean.

**Theorem.** A finite E1485 magma with minimum degree three and exactly
three central vertices has at most eight degree-four vertices.

The [first-top-output theorem](1485_three_central_minimum_top_output.md)
proves that degree four occurs, and the earlier counting bound allows
at most nine such vertices. We exclude equality. The final step is a
genuine closed submagma of order 24, not an assumption that an arbitrary
local incidence configuration is a submagma.

## The saturated profile grid

Suppose the degree-four class `A` has nine vertices. Write `Z` for
the three central vertices, `T` for the nine top vertices, and `B`
for the reciprocal degree class, of degree `n/4`. Every vertex of
`A` has one sharp neighbor and three top neighbors in each direction.
Let

\[
F,G:A\longrightarrow B
\]

be its sharp successor and predecessor maps. Both are surjective,
and every fiber has size at most three. Unique goodness of sharp
two-edge paths also gives

\[
|G^{-1}(b)\cap F^{-1}(c)|\le1.                  \tag{1}
\]

In particular `|B|≥3`. The parity argument from the
[three-central profile reduction](1485_order_twenty_four_three_central_reduction.md#predecessor-and-successor-parities-are-opposite-and-constant)
applies without the order-24 assumption: an `A×A` endpoint pair has
only top middles and, if `F(a)=G(c)`, a sharp `B` middle. If there
is no sharp middle, its top middle is unique. Consequently all top
predecessor permutation transversals of `A` have one parity, and all
successor transversals have the opposite parity. The only size input
needed for that parity argument is `|B|≥3`.

Call the three predecessor transversals `P_0,P_1,P_2`, and the
three successor transversals `Q_0,Q_1,Q_2`. They partition `T` in
each direction, with

\[
t_{pq}=P_p\cap Q_q.
\]

Two degree-four vertices cannot have the same profile pair: the six
noncentral endpoint pairs in that rectangle would have two good
middles. Hence all nine profile pairs occur exactly once. Write
`a_pq` for the vertex with profiles `P_p,Q_q`.

Each `F`-fiber meets each `P`-row of this nine-cell grid at most
once: sharp predecessors of one vertex have disjoint ordinary
columns. Dually each `G`-fiber meets each `Q`-column at most once.

## A missing profile row forces top inputs into a sharp fiber

Call an `F`-fiber a *full column* if it is exactly
`{a_0q,a_1q,a_2q}` for some `q`. Denote its value by `b_q`.

Fix `a∈A` and a `P`-row `p` disjoint from `F^{-1}(G(a))`.
We claim that

\[
t_{pq}\in\operatorname{TopSucc}(F(a))           \tag{2}
\]

unless column `q` is a full `F`-fiber and row `p` meets
`G^{-1}(b_q)`.

For the proof, choose any `c=a_pj` in row `p`. By the row's
disjointness, `F(c)≠G(a)`, so

\[
c*a=t_{P(a),j}.
\]

If some `d` in column `q` satisfies `F(d)≠G(c)`, then
`d*c=t_pq`. E1485, with `x=a,y=c,z=d`, gives

\[
t_{P(a),j}*(a*t_{pq})=a.                        \tag{3}
\]

The value `a*t_pq` lies in `Row(a)={F(a)}∪Q(a)`. If it lies
in `Q(a)`, equation (3) forbids precisely the one top element of
`Q(a)` whose central predecessor equals the central successor of
`t_{P(a),j}`. As `j` varies over the three values, these three
forbidden elements exhaust `Q(a)`.

There fails to be an eligible `d` for a particular `c` exactly
when all three members of column `q` lie in `F^{-1}(G(c))`.
Since an `F`-fiber has size at most three, this is exactly the
exception in the claim. Outside that exception, all three equations
(3) hold and force `a*t_pq=F(a)`. Because `a⇒F(a)` is sharp,
its full translation fiber is `Row(F(a))`, proving (2).

Every set `TopSucc(F(a))` has exactly three elements. This is the
capacity constraint used below. The dual statements exchange `F,G`
and rows and columns.

## There are exactly three reciprocal-degree vertices

Put `b=|B|`, so `3≤b≤9`.

First suppose an `F`-fiber is a singleton, at a cell in row `p_0`,
and choose `a` with `G(a)` equal to that fiber's value. The other
two rows are missing rows in (2). They give six top positions,
all forced into the three-element set `TopSucc(F(a))` except at
full-column exceptions. A single full column can save at most two
of these positions. Therefore there must be at least two full
`F`-columns.

If `b≥5`, some `F`-fiber is a singleton, since nine elements cannot
fill five fibers of size at least two. The two full columns use six
cells, so necessarily `b=5`: the remaining column is split into
three singleton fibers. The dual argument gives two full `G`-rows
and three singleton fibers in its remaining row. Every `G`-fiber is
therefore contained in one row. In the preceding six-position
argument, each of the two full `F`-column values can now save a
position in at most one of the missing rows. At most two positions
are saved, leaving at least four in a three-element set. Thus
`b≥5` is impossible.

Suppose `b=4` and `F` has no singleton. Its fiber sizes are
`3,2,2,2`. The size-three fiber meets all three rows. Each size-two
fiber misses one row, and the three missed rows are distinct: after
removing the size-three fiber, exactly two cells remain in each row.
There is at most one full `F`-column.

For each value `β` with size-two `F`-fiber, and each `a` with
`G(a)=β`, equation (2) puts at least two points of its missing
`P`-row into `TopSucc(F(a))`. Two distinct such values `β` have
disjoint missing `P`-rows. Thus no value `γ=F(a)` can occur for
two different such `β`: that would put at least four points into
`TopSucc(γ)`. By (1), it cannot occur twice for the same `β`
either. Hence at most four vertices of `A` can have `G`-value
among these three `β`'s. At least six do, because the fourth
`G`-fiber has size at most three. Contradiction.

The dual reasoning excludes `b=4` when `G` has no singleton.
In the remaining case both maps have singleton fibers. Each has
two full columns or rows, respectively, and a `2+1` split in the
remaining column or row. In particular every `G`-fiber is again
contained in one row. The six-position argument with an `F`
singleton again has at most two exceptions and gives the same
contradiction.

We conclude that

\[
\boxed{|B|=3.}                                  \tag{4}
\]

All `F`- and `G`-fibers consequently have size three.

## A closed 24-element submagma

Set `S=Z∪A∪B∪T`. These four classes are disjoint. Indeed degree
four divides `n`, as does degree three, so `12|n`. Equality
`n/4=3` would give only the two degrees three and four at order
12, contrary to the two-degree theorem; equality `n/4=4` would
give `n=16`, incompatible with `3|n`. Top degree `n/3` differs
from `n/4` and from four once order 12 is excluded. Thus `|S|=24`.

Each degree-four vertex accounts for six top endpoint products.
Their nine disjoint sets exhaust the 54 noncentral top endpoint
pairs. Therefore `T*T⊆Z∪A`.

Every `B` vertex has three sharp `A` successors. Their ordinary
rows are disjoint, so their three-element top successor sets partition
the nine top vertices. All the corresponding paths are good, giving
`B*T⊆A`. The dual argument gives `T*B⊆A`.

The nine sharp paths `B⇒A⇒B` have distinct ordered endpoint pairs
by unique goodness. There are exactly nine pairs in `B²`, so these
paths account for every product, giving `B*B⊆A`.

Any product with a factor in `A` belongs to `T∪B`, by its ordinary
row or column description. Any product with a central factor is top.
These cases prove that **`S` is closed under multiplication**.

The restriction to `S` would be an E1485 magma of order 24.
Its central vertices still have degree three, its `A` vertices
still have degree four, and its sharp `A,B` edges force the
restricted degree of `B` to be six. Its central/top sharp edges
likewise force the restricted degree of `T` to be eight. Thus it
has precisely the class sizes `(3,9,3,9)` at degrees `(3,4,6,8)`,
contradicting the [analytic exclusion of that case](1485_order_twenty_four_three_central.md).
In particular, this step needs neither of the incidence enumerations
used in the broader order-24 theorem. This proves the theorem.

## Eight degree-four vertices exclude degree five

There is a further necessary condition immediately below saturation:
if `|A|=8`, degree five does not occur.

Indeed `|B|≥3`, so the same opposite-parity profile argument applies.
Exactly one cell `(p_0,q_0)` of the nine-cell profile grid is missing.
Every noncentral top endpoint pair whose product has degree greater
than four consequently lies in the one rectangle `P_p0×Q_q0`.
That rectangle has exactly six noncentral endpoint pairs.

Suppose `a` had degree five. Besides its three top successors it has
only two non-top successors. Each top predecessor's three-element
fiber at `a` must therefore contain a top input. Dually every top
successor participates in some good top endpoint pair with middle
`a`. Hence its three top predecessors are exactly `P_p0`, and its
three top successors exactly `Q_q0`.

All six noncentral pairs in this rectangle must have good middle `a`.
A bad path through `a` could only have a replacement of degree three
or four; the former is excluded by being a noncentral endpoint pair,
and the latter by the missing profile cell. Thus `g=6`.

The [top-fiber slot bound](1485_three_central_minimum_top_output.md#a-general-top-fiber-slot-bound)
with `r=3,q=4,p=5` contradicts this. There are only two non-top
successors, so the sharp out-degree is `k=1` or `k=2`; equation (4)
of that note gives respectively `g≤4` or `g≤3`. This excludes
degree five in the eight-vertex case. It does not exclude eight
degree-four vertices themselves.

## Eight degree-four vertices have at most six reciprocal-degree vertices

Continue to assume `|A|=8`, with the missing profile cell placed in
row two and column two. The first two rows and columns each have
three cells; the last ones have two. Then

\[
3\le |B|\le6.
\]

The missing-row argument (2) still applies to a full three-cell row.
Its column exception now means that the entire occupied column is
one `F`-fiber; the last column has only two cells.

If `|B|≥7`, there is at most one nonsingleton `F`-fiber. It meets
the short row at most once, so one of that row's two cells is an
`F`-singleton. Choose `a` whose `G`-value is this singleton's value.
The two full rows are both missing rows for `a`. Their six top
positions are forced into `TopSucc(F(a))` except at full-column
exceptions. There is at most one such column, which saves at most
two positions. At least four points would lie in a three-element
set, a contradiction.

If `|B|=6`, each of the maps `F,G` must have fiber sizes
`2,2,1,1,1,1`. The only other partition is `3,1,1,1,1,1`, and the
same singleton-in-the-short-row argument excludes it. Both cells
in the short row must lie in the two distinct size-two `F`-fibers;
otherwise that argument applies again. In particular there is no
full `F`-column: a possible two-cell full column would be the short
column, which has no cell in the short row, leaving one short-row
cell in a singleton. Dually the two size-two `G`-fibers cover the
short column, and there is no full `G`-row.

These restrictions do not by themselves exclude reciprocal-class
sizes three through six.
