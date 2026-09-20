# Order forty: mixed-path return capacities from the internal incidence matrices

Research note, 20 September 2026. These are analytic necessary
conditions, not an exclusion by themselves. They apply to every
order-forty branch with degree classes `Z,A,B,T` of degrees
`4,5,8,10`, four central vertices and sixteen top vertices.
The size of `A` is not fixed here. No profile-affineness assumption
or computation is used in the proof.

As usual, `D` is ordinary adjacency within `B`, and `C_bd=1`
records the unique sharp path `b⇒a⇒d` through `A`. Its row
and column sums are the sharp degrees `j_b`; those of `D` are
`4−j_b`. Define

\[
G_{db}=\#\{(x,y)\in B^2:
dDxDyDb,\ C_{dy}=C_{xb}=0\},
\qquad K=CD+DC+G.                                      \tag{1}
\]

Thus `G` counts the all-`B` three-edge paths for which both
successive two-edge paths are good. The larger number `K_db`
counts **all** such good-good paths `d→x→y→b` whose two
internal vertices belong to `A∪B`.

Indeed the contribution with `(x,y)∈A×B` is `(CD)_db`,
and the contribution from `B×A` is `(DC)_db`. Every path
in either contribution is good-good because every incident `A—B`
edge is sharp. The `A×A` contribution is zero, since `A`
is independent. Each `C` entry records exactly one vertex of
`A`, so these counts have no multiplicities hidden in the notation.

## 1. A degree-five return has mixed-path count at most four

Suppose `b*d=a∈A`, equivalently `C_bd=1`. The return
matching has fibers

\[
X=L_a^{-1}(d),\qquad Y=R_a^{-1}(b),\qquad |X|=|Y|=8.
\]

The path `b⇒a⇒d` is sharp, hence

\[
X=\operatorname{Row}(d),\qquad
Y=\operatorname{Col}(b).
\]

Each of these sets has four top and four non-top members.
No central member occurs, since a degree-four vertex cannot be
adjacent to a degree-eight vertex at order forty. Applying the
[return boundary identity](1485_general_return_matching.md#3-arbitrary-subsets-give-a-boundary-capacity-identity)
with the subset `A∪B` gives

\[
g_{TT}(d,b)=8-4-4+K_{db}=K_{db}.
\]

The matched edges with two top endpoints form a matching between
two four-element sets. Consequently

\[
\boxed{C_{bd}=1\quad\Longrightarrow\quad K_{db}\le4.}    \tag{2}
\]

## 2. A degree-eight return gives both upper and lower mixed-path bounds

Suppose `b*d=e∈B`. Equivalently `C_bd=0` and there is
a unique ordinary internal middle `bDeDd`. Put

\[
\beta=\beta(e,d)=\#\{x:eCx,\ dDx\},\qquad
\eta=\eta(b,e)=\#\{x:xDb,\ xCe\}.                     \tag{3}
\]

The five-element return fibers

\[
X=L_e^{-1}(d),\qquad Y=R_e^{-1}(b)
\]

have respectively `1+β` and `1+η` top members, by the
exact top-fiber count on the internal edges `e→d` and `b→e`.
Their non-top counts are therefore `4−β` and `4−η`.
The same boundary identity gives

\[
g_{TT}(d,b)
=5-(4-\beta)-(4-\eta)+K_{db}
=K_{db}-3+\beta+\eta.                                 \tag{4}
\]

This is nonnegative and at most the smaller of the two top-fiber
sizes. Rearranging yields

\[
\boxed{3-\beta-\eta\ \le K_{db}
\ \le4-\max(\beta,\eta).}                             \tag{5}
\]

All the quantities in (2) and (5) are determined by the two
binary matrices `C,D`. These tests count the mixed `A/B`
paths as well as the all-`B` paths; they must not be replaced
by the latter alone. In particular, they add constraints beyond
the earlier upper bound `G_db≤40/d(b*d)−j_b−j_d`.

## 3. The upper bound four holds for every return

If the return is top-valued, its entire matching has only four
edges, so again `K_db≤4`. Together with (2) and (5), this gives

\[
\boxed{K_{db}\le4\quad\text{for every }b,d\in B.}
\]

In particular an incidence checker must apply this bound even
when `C_bd=0` and `(D²)_bd=0`; those are exactly the top-return
pairs. Their finer non-top fiber sizes still need additional profile
information. The [general four-degree theorem](1485_four_degree_mixed_return_capacity.md)
extends these bounds to `n=2r(r+k)` with minimal central count.
