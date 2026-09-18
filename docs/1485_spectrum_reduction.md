# E1485 spectrum: the remaining degree patterns

Research status, 18 September 2026. The full square/twice-square converse
is still open in this work. This note records a reduction that includes
all models with at most three distinct translation degrees. The arguments
are pen-and-paper proofs, not new Lean declarations.

Let `M` be a nonempty finite E1485 magma of order `n`. The
[finite structure theorems](1485_graph_research.md) give
`d(x)=|Row(x)|=|Col(x)|`, uniform nonempty translation fibers, and a
sharp successor and predecessor of every element. An edge `x⇒y` is
sharp precisely when `d(x)d(y)=n`.

## Odd numbers of degree values force square order

Let `D={d(x):x∈M}` be the set of distinct degree values. If `d∈D`,
choose a vertex of degree `d` and a sharp successor. That successor
has degree `n/d`. Thus the map

\[
 d\longmapsto n/d
\]

is an involution of `D`. If `|D|` is odd, this involution has a fixed
point: its non-fixed orbits have size two. For a fixed degree `d`,
`d=n/d`, and hence

\[
 \boxed{|D|\text{ odd}\quad\Longrightarrow\quad n=d^2.}
\]

In particular this handles every model with one or three degree values,
and equally applies to five, seven, or any other odd number of values.
Equivalently, if `n` is not a square, its occurring degree values come
in distinct complementary pairs.

## Two degree values force twice-square order

If `D={r,s}` with `r<s`, the extremal product theorem gives `n=rs`.
The [three five-cycle counts](1485_two_degree_lower_bound.md) prove

\[
 \boxed{s=2r,\qquad n=2r^2.}
\]

No hypothesis about constancy of sharp-neighbor counts is used here.
Their constancy is a stronger structural question, still open in general;
it is not needed for this cardinality theorem.

Every product of two distinct primes is consequently excluded. Such an
order cannot have a constant row (constant-row models have power-of-two
order), and degree divisibility and the extremal product then force
exactly the two prime degrees. They cannot have ratio two.

## What a remaining counterexample would have to look like

A finite model whose order is neither a square nor twice a square must
have **an even number of distinct translation degrees, at least four**.
For four values, write them in increasing order as

\[
 r<a<b<s.
\]

The complementary-degree involution is order reversing, so

\[
 rs=ab=n.
\]

This does not yet force `b=2a`, or otherwise give the desired square
class of `n`. The two-degree proof cannot simply be applied to the
middle degree classes: their union need not be closed under multiplication.

At minimum degree two, there are exactly four maximum-degree vertices,
and every vertex has exactly two neighbors of maximum degree in each
direction; see the [incidence proof](1485_min_degree_two.md). The
[two-central](1485_two_central_exclusion.md) and
[three-central](1485_three_central_exclusion.md) exclusions now prove
that there are exactly four central vertices as well, and hence no
degree-three vertices. Every central coordinate rectangle is the central
set in this case. This does not yet construct a Boolean quotient or
classify all orders with minimum degree two. The
[full-central-core argument](1485_full_central_core.md) additionally
shows that all central auxiliary relations coincide with `B(a)=a*T`,
where `T` is the maximum-degree class. It gives exact neighborhood-overlap
formulas but does not yet prove all edges of `B` sharp. The subsequent
[neighbor-gap proof](1485_min_two_neighbor_gap.md) excludes degree five,
proves sharp regularity at degree six, and proves `4|n` for every
minimum-degree-two model. More generally, under `|Z|=r²`, it excludes
the degree intervals `(r,2r)` and `(2r,3r)` and proves sharp regularity
at degrees `2r` and `3r`. A further
[path-matrix argument](1485_six_times_square_full_core.md) excludes
order `6r²` under that full-central-core hypothesis. In particular,
order 24 cannot have minimum degree two; its possible minimum-degree-three
case is not excluded by this argument. The
[order-twelve proof](1485_order_twelve.md) now excludes all its possible
degree patterns. Its final two cases use a binary-coordinate contradiction
and incompatible ranks of two path-count matrices, respectively. This
supplies an analytic exclusion without relying on a SAT certificate.

The [sharp-degree defect note](1485_sharp_degree_defect.md) gives a
separate global reduction. The integer

\[
 \Delta=\sum_x d(x)-\sum_x n/d(x)
\]

is nonnegative, and vanishes if and only if every sharp in-degree and
out-degree equals the minimum ordinary degree. Its vanishing remains
unproved. This structural target is stronger than the cardinality
conclusion already established for two-degree models; it must not be
treated as a necessary intermediate step for every spectrum proof.

The general goodness-reflecting Boolean quotient theorem remains another
possible route. Its uniform square fibers are proved, but existence of
such a quotient for every finite model remains unproved. In particular,
uniform fibers of individual translations must not be confused with
uniform joint fibers of `x↦(h*x,x*h)` for central `h`: the latter claim
is false, as the explicit order-eight example in the
[projection note](1485_image_research.md) shows.
