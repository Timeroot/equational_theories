# Eight central elements cannot have only small profiles at sixteen or more tops

Independently audited analytic proof, 20 September 2026. Assume order
forty, minimum degree four, eight central elements, and `16≤h≤18`
tops. Then not every degree-five element can have top-profile size
three. No finite enumeration or SAT premise is used in this theorem;
it is not yet a Lean proof.

Write `a,b` for the numbers of degree-five and degree-eight elements,
and suppose for contradiction that all `a` degree-five elements have
three top predecessors and successors. Their sharp-neighbor count is
two. Sharp coverage and the class counts give

\[
                 b=32-h-a\le2a,
                 \qquad a\ge\left\lceil\frac{32-h}{3}\right\rceil
                           \ge5.                     \tag{1}
\]

As usual `P,C` denote top central block sizes, and `α,β` count
degree-five successors and predecessors.

## 1. The all-small hypothesis improves the local capacities

Every degree-five predecessor and successor partition has pattern
`332`. Hence `P=1` forces `α=0`, and `C=1` forces `β=0`.
The ordinary support bound is `α≤(4,3,1)_C` and its dual.

At `C=1`, equality `α=4` would make the
[singleton-source saturation identity](1485_singleton_source_first_degree_saturation.md)
give `h=4+4(3−1)=12`, contrary to `h≥16`. Thus `α≤3`.

At `C=2`, suppose `α=3`. Apply the
[unused-top identities](1485_first_degree_source_unused_tops.md#1-removing-any-selected-collection-of-first-degree-outputs)
to these three successors. All have profile size three. The unused
top count is

\[
                   |W|=h-4\cdot2-3(3-1)=h-14\ge2.
\]

Their total successor-block size, however, is

\[
                   \sum_{w\in W}|C_w|
                       =\sum_{i=1}^3|C_{d_i}|-8\le1,
\]

because every retained central block has size at most three.
Every unused block is nonempty, a contradiction. Therefore

\[
                       \alpha\le(3,2,1)_C,
                       \qquad\beta\le(3,2,1)_P.      \tag{2}
\]

## 2. The two triple-block families force too many singleton blocks

The incidence moments and `α=0` at `P=1` give

\[
                  \sum_{P=3}\alpha
                       =\sum(P-2)\alpha=2a\ge10.
\]

If `p,c` count triple blocks in the two directions, (2) gives
`3p≥10`; the [one-hole bound](1485_one_hole_first_output_grid.md)
gives `p≤4`. Thus `p=4`, and dually `c=4`.

Put `z=n13,w=n31,t=n33`. The four predecessor triples have
total degree-five successor capacity

\[
             2a\le3w+2(4-w-t)+t=8+w-t.
\]

Since `a≥5`, this implies `w−t≥2`; the dual inequality is
`z−t≥2`.

On the other hand, the central mixed moment and singleton margin are

\[
                  n11=4h-64+z+w-t,
                  \qquad n_{P=1}=2h-28.
\]

The inequality `n11+z≤n_(P=1)` consequently gives

\[
                    2z+w-t\le36-2h\le4.
\]

But `z,w≥t+2` make its left side at least `2t+6≥6`.
This contradiction proves the theorem.

## Consequences for the current frontier

This analytically excludes `(h,a,q)=(16,6,6),(17,5,5),(17,6,6),
(18,5,5),(18,6,6)`, where `q` counts small profiles. It replaces
the earlier finite-assisted exclusion of the last two cases.

The separate [fifteen-top theorem](1485_order_forty_eight_central_fifteen_profile_bound.md#6-consequence-fifteen-tops-are-impossible-at-order-forty)
excludes that top count, and the weighted bounds exclude all other
top counts. Thus every still-open eight-central order-forty model
must have at least one size-four degree-five profile. This is a
necessary condition, not a construction or a full spectrum proof.
