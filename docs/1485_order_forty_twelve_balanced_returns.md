# Order forty, balanced twelve/eight profiles: all return weights are one

Research note, 20 September 2026. This is an analytic consequence of
the remaining single-coset profile pattern. It uses no finite search.
It proves uniform internal bad-extension counts and sharper profile
margins, but does not by itself exclude the balanced configuration.

Suppose the degree classes `Z,A,B,T` have degrees `4,5,8,10` and
sizes `4,12,8,16`, with sharp degrees `(2^4,1^4)` on `B`. Write
`M,L⊆B` for the four medium- and four low-sharp vertices. Both
degree-five profile families lie in single cosets, with multiplicities
`(3,3,3,3)` on each side. Thus their four missing profile pairs form
a permutation; label the predecessor lines `P_i` and successor lines
`Q_i` so that the holes are exactly `(P_i,Q_i)`.

Write

\[
m_{bi}=|U_b\cap P_i|,\qquad n_{bi}=|V_b\cap Q_i|.
\]

Both rows sum to four and have entries at most three, by the no-line
theorem. The medium profiles are affine transversals of the opposite
partition, so each medium intersection row is `(1,1,1,1)` or a
permutation of `(2,2,0,0)`. The low profiles are not assumed affine.

## 1. Every edge incident to a medium vertex has weight one

For an internal edge `bDd`, let

\[
\beta(b,d)=\sum_x C_{bx}D_{dx},\qquad
\eta(b,d)=\sum_y D_{yb}C_{yd}.
\]

These are equal by bad-extension balance. If `I_d` is the set
of predecessor-line colors of the `F`-fiber at `d`, the exact
top return equation is

\[
\sum_{i\in I_d}m_{bi}=3-\eta(b,d).                  \tag{1}
\]

Suppose `b∈M`. If its row is `(1,1,1,1)`, the left side is
`j_d`. A low target would give `η=2`, contradicting `η≤j_d=1`.
For a medium target it gives `η=1`. If the row has type `(2,2,0,0)`,
the left side is even. The right side belongs to `{1,2,3}` because
`η≤2`; hence both sides equal two and again `η=1`.

The dual argument treats edges whose target belongs to `M`, using
the affine successor profile of that target. Therefore

\[
\boxed{\beta(b,d)=\eta(b,d)=1
\quad\text{whenever }bDd\text{ and }\{b,d\}\cap M\ne\varnothing.}
                                                               \tag{2}
\]

On an edge between low vertices the weight is at most one. Thus
every internal weight is zero or one, and a zero weight can occur
only on an edge inside `L`.

## 2. A three-point predecessor intersection has at most eight good top pairs

This small geometric bound does not use affineness. Suppose a profile
`U_b` has intersection row of type `(3,1,0,0)`, with its three
points on `P_i` and its remaining point on `P_j`, `j≠i`.
Put `s=n_{bi}`, `t=n_{bj}`. Then `0≤s,t≤3` and `s+t≤4`.

Only the two corresponding hole rectangles can contribute good top
pairs with product `b`. On the heavy rectangle there are `3s`
endpoint pairs. The three first endpoints have distinct central
successor labels, and the `s` second endpoints have distinct central
predecessor labels. Among the four possible central labels their
intersection therefore has at least `max(0,s−1)` elements. Every
matching label gives a central product, not a good pair through `b`.
The light rectangle contributes at most `t` pairs. Consequently

\[
g_b\le3s-\max(0,s-1)+t\le8.                         \tag{3}
\]

For the last inequality, `s=0` gives at most three; if `s≥1`,
the bound is `2s+1+t≤s+5≤8`. This remains valid if additional
constraints discard some of the counted pairs.

## 3. Zero weights are impossible

Suppose `bDd` has weight zero. Both endpoints are low by (2).
The `F`-fiber at `d` has one predecessor-line color `i`. Equation
(1) gives `m_{bi}=3`, so the row of `b` has type `(3,1,0,0)`.

No internal successor of `b` can be medium: by (2) such an edge
would make (1) equal two, but the sum on two distinct entries of
`(3,1,0,0)` is never two. Every internal successor is therefore
low. On any such edge (1) selects just one row entry, which must
be `3−η∈{2,3}`. Only the value three occurs. Thus all three
internal outgoing edges of `b` have weight zero.

The bad-extension count at `b` is

\[
\tau_b=\sum_{d:bDd}\beta(b,d)=0.
\]

The exact good-pair formula gives

\[
g_b=12-3j_b-\tau_b=9,
\]

contradicting (3). Hence there are no zero-weight edges. We have proved

\[
\boxed{\beta=\eta=1\text{ on every internal edge},\qquad
g_b=4\ (b\in M),\quad g_b=6\ (b\in L).}              \tag{4}
\]

The proof does not use the Eulerian structure of the zero-edge graph,
an ATP, SAT, or the stronger exact per-top-input fiber identities.

## 4. No partner profile meets a line three times

With (4), equation (1) has value two on every internal edge.
No subset of the entries of `(3,1,0,0)` sums to two. Since every
vertex has an internal successor, no predecessor intersection row
can have that type. The dual argument excludes it from the successor
rows. Thus

\[
\boxed{m_{bi},n_{bi}\le2\quad\text{for all }b,i.}      \tag{5}
\]

A low row cannot be `(1,1,1,1)` either: the total number of hole
endpoint pairs is then at most the sum of the opposite row, namely
four, contrary to its six good pairs in (4). Hence both intersection
rows of every low vertex have type `(2,2,0,0)` or `(2,1,1,0)`.
This is a statement about line intersections; it does not assert
that every low profile is a transversal of the opposite coset.

## 5. The sharp-path matrix preserves the two sharp-degree classes

For `b∈L`, let `c` be the unique target in its row of `C`.
Equation (4) says `dDc` for all three distinct internal successors
`d` of `b`. Thus `c` has internal indegree at least three, and
must lie in `L`. Every low column of `C` has sum one, so these
four targets give a permutation of `L`, leaving no entries of
`C` between `L` and `M` in either direction. Therefore

\[
\boxed{C_{LL}\text{ is a permutation matrix},\quad
C_{LM}=C_{ML}=0,\quad C_{MM}\text{ has both margins two}.}
                                                               \tag{6}
\]

These exact analytic restrictions can be added to any remaining
balanced-profile search, with all their dependencies visible above.
