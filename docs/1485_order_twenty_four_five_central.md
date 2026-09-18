# Order twenty-four with five central vertices: one remaining case

Research note, 18 September 2026. This is an analytic reduction using
the [small-central incidence note](1485_order_twenty_four_small_central.md),
[finite structure](1485_graph_research.md), and
[strict degree descent](1485_image_research.md).

The remaining case in this analytic reduction is now excluded by the
[finite central-incidence calculation](1485_order_twenty_four_five_central_finite.md).
The distinction matters: this note is analytic, while that completion
uses an explicit finite enumeration not yet checked in Lean.

Write `Z,A,B,T` for the degree classes `3,4,6,8`, with respective
cardinalities `m,f,g,h`. Assume `m=5`. The earlier incidence restrictions
leave `h=9` or `h=10`. This note excludes all `h=10` cases and the
`h=9,f=6` case. The only remaining class sizes are

\[
 (m,f,g,h)=(5,5,5,9). \tag{1}
\]

## A general central injection

For every vertex `x`, the map

\[
 z\longmapsto(x*z,z*x)\qquad(z\in Z)
\]

takes values in `TopSucc(x)×TopPred(x)`: products with a central
factor are top vertices. It is injective, since centrality of `z`
gives `(x*z)*(z*x)=z`. Consequently

\[
 |Z|\le |\operatorname{TopSucc}(x)|\,
             |\operatorname{TopPred}(x)|. \tag{2}
\]

A degree-four vertex has neighbors only in `B` and `T`, and its
`B` neighbors are exactly its sharp neighbors. Ordinary degree balance
and reciprocal-degree balance make its sharp in-degree and out-degree
equal. If this common sharp degree were at least two, its top degrees
would both be at most two, contradicting (2) when `m≥5`.
Thus, for `m=5` (and also for `m=6`), every `A` vertex has exactly
one sharp `B` neighbor and three top neighbors in each direction.

In particular `f≥g`. If `h=9`, then `f+g=10`, so `f≥5`.
The top-input bound `9m+6f≤h²` gives `f≤6`. If `h=10`, then
`f+g=9`, again implying `f≥5`.

Let `k_t^-` and `k_t^+` be the central predecessor and successor
counts of a top vertex. As before,

\[
 \sum_t k_t^- =\sum_t k_t^+=15,\qquad
 \sum_t k_t^-k_t^+=25. \tag{3}
\]

Let `α_t` count its `A` successors. Every `A` contributes three
top predecessors, whose central-predecessor weights sum to five.
Thus

\[
 \sum_t\alpha_t=3f,\qquad
 \sum_t k_t^-\alpha_t=5f. \tag{4}
\]

Each central output of `L_t` uses three top inputs. Each `A` output
uses its one sharp `B` input and two top inputs. The nonempty fibers
of `L_t` have size three, giving

\[
 3k_t^++2\alpha_t\le h. \tag{5}
\]

All these facts have dual versions.

## Ten top vertices force five tops of each of two types

Suppose `h=10`. Put `u_t=k_t^-−1`, `v_t=k_t^+−1`.
They lie in `{0,1,2}`, and (3) gives

\[
 \sum u_t=\sum v_t=5,\qquad \sum u_tv_t=5.
\]

Inequality (5) says
`α_t≤3−v_t−1_{v_t=2}`. From (4),

\[
 2f=\sum u_t\alpha_t
 \le 3\sum u_t-\sum u_tv_t-\sum_{v_t=2}u_t
 =10-\sum_{v_t=2}u_t. \tag{6}
\]

Since `f≥5`, equality forces `f=5` and `u_t=0` wherever `v_t=2`.
The dual argument forces `v_t=0` wherever `u_t=2`.
Thus a nonzero product `u_tv_t` can occur only at `(u_t,v_t)=(1,1)`.
Its sum is five, so there are exactly five such vertices. These
already exhaust both marginal sums five; the other five vertices
have `(u_t,v_t)=(0,0)`. The central profile is therefore

\[
 \text{five }(1,1)\text{ tops }U,
 \qquad\text{five }(2,2)\text{ tops }V. \tag{7}
\]

Every central row has weight pattern `(1,2,2)`, so contains one
`U` vertex and two `V` vertices. The dual assertion holds for columns.
Consequently the central predecessor and successor maps of the five
`U` vertices are bijections.

## A five-by-five matrix contradiction

Label `U_i` by its unique central predecessor `z_i`. Let `P` be the
permutation matrix of its central successor map. Let `R` be adjacency
from `Z` to `V`, and `S` adjacency from `V` to `Z`. Both `R,S` are
five-by-five zero-one matrices with all row and column sums two.
Central-to-top and top-to-central adjacency matrices are

\[
 C=[I\ R],\qquad D=\begin{bmatrix}P\\S\end{bmatrix}.
\]

Central endpoints have a unique good top middle, hence

\[
 CD=J_5,\qquad RS=J_5-P. \tag{8}
\]

The matrix `J_5−P` is invertible over the rationals: if
`(J_5−P)x=0`, then `Px=(Σx)1`, so `x` is constant, and then it
must vanish. Thus both `R` and `S` are invertible.

Let `K=DC` be the central-middle matrix on the ten top vertices.
Its entries are zero or one, because two central middles for the
same endpoints would both be good. In block form,

\[
 K=\begin{pmatrix}P&PR\\S&SR\end{pmatrix}.
\]

The block `SR` has all row and column sums four. Therefore

\[
 SR=J_5-Q \tag{9}
\]

for another permutation matrix `Q`.

Fix any `a∈A`. Its three top predecessor weights sum to five,
so its predecessor set is one `U_i` and two `V` vertices, indexed
by a two-element set `I_a`. Its successor set similarly consists
of one `U_j` and two `V` vertices, indexed by `J_a`.

The restriction of `K` to this three-by-three endpoint rectangle
is a permutation matrix. Indeed each top fiber at `a` has one sharp
`B` input and two top inputs, so exactly one path through `a` is bad
from each predecessor endpoint. Dually exactly one is bad at each
successor endpoint. Such a path is bad exactly when it has a central
middle, the only possible smaller degree.

In the two-by-two `V×V` subrectangle, (9) has at least one one in
each row and each column. The permutation-matrix restriction forces
exactly one in each. The two `V` rows and two `V` columns have then
used their unique ones, so the remaining `U_i,U_j` entry must be one:

\[
 P_{ij}=1. \tag{10}
\]

The three top predecessors of `a` meet every central row exactly once.
Writing `1_{I_a}` for the indicator vector of its two `V` predecessors,

\[
 R1_{I_a}=1-e_i.
\]

On the other hand, (8) and (10) give
`R(S e_j)=1-e_i`. Invertibility of `R` yields

\[
 S e_j=1_{I_a}. \tag{11}
\]

Thus both `V` predecessors of `a` have central middles to its `U_j`
successor. This contradicts the permutation restriction: its `U_j`
column already has its one at `U_i`. No `A` vertex can exist, excluding
`h=10`.

## Nine tops and six degree-four vertices are impossible

Suppose `h=9,f=6`. Let
`r=Σ_{k_t^+=3}k_t^-`. Each central row has weight pattern `(1,1,3)`
or `(1,2,2)`, so `r` is the number of rows of the first kind and
`r≤5`. Summing central row incidences gives

\[
 \sum_{k_t^+=1}k_t^-=5+r,\qquad
 \sum_{k_t^+=2}k_t^-=10-2r.
\]

The bounds in (5) are now `α_t≤3,1,0` at successor weights
`1,2,3`, respectively. Hence

\[
 30=5f\le3(5+r)+(10-2r)=25+r\le30. \tag{12}
\]

Equality forces `r=5`, so no successor weight is two. Dually no
predecessor weight is two. Equations (3) then give the exact profile

\[
 \text{four }(1,1)\text{ vertices }W,
 \quad\text{two }(1,3)\text{ vertices }U,
 \quad\text{two }(3,1)\text{ vertices }V,
 \quad\text{one }(3,3)\text{ vertex }H. \tag{13}
\]

An `A` predecessor cannot have successor weight three, by (5).
Its three predecessor weights sum to five, so it has exactly one
predecessor in `V` and two in `W`. Dually it has exactly one
successor in `U` and two in `W`.

Let `R_H,C_H⊆Z` be the central predecessor and successor triples
of `H`. The top endpoint pair `(H,H)` has at most one central middle,
so `|R_H∩C_H|≤1`. Since both sets have size three in a five-element
set, their intersection has size one and their union is `Z`.

Every central row now has pattern `(1,1,3)`. Therefore the unique
central predecessors of the two `U` vertices are exactly `Z\R_H`.
Dually the unique central successors of the two `V` vertices are
exactly `Z\C_H`. These two complements are disjoint. Consequently
no pair in `V×U` has a central middle.

Every `A` vertex supplies a path from its unique `V` predecessor to
its unique `U` successor. These paths are all good, because a bad
degree-four middle would require a central replacement. Their endpoint
pairs must be distinct by uniqueness. But there are six `A` vertices
and only four pairs in `V×U`, a contradiction.

Together with the initial class-size bounds, these exclusions leave
precisely (1). No exclusion of that last case is claimed here.
