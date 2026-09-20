# Eight central elements cannot have nineteen tops

Independently audited analytic proof, 20 September 2026. This excludes nineteen
tops in the order-forty eight-central branch. It uses no enumeration,
SAT premise, or optimization certificate, and is not yet a Lean theorem.
The remaining eight-central top counts are fifteen through eighteen;
this note does not exclude that entire branch.

Write `Z,T,A,B` for the degree classes `4,10,5,8`, and suppose
`|Z|=8`, `|T|=19`. Put `a=|A|`, `b=|B|`, and let `q`
count members of `A` having three top neighbors in each direction.
The others have four.

## 1. Two possible class-size cases

The [weighted top bound](1485_order_forty_eight_central_top_bound.md)
and sharp-neighbor coverage give

\[
 a+b=13,\qquad 4a+q\le27,\qquad2a+q\ge13,
 \qquad0\le q\le a.
\]

They force either

\[
             a=5,\quad3\le q\le5,
 \qquad\text{or}\qquad
             a=6,\quad1\le q\le3.                       \tag{1}
\]

For each top abbreviate `P=|P_u|`, `C=|C_u|`, and let `α`
count its ordinary successors in `A`. All blocks have size at most
three. The central and degree-five incidence moments are

\[
 \sum1=19,\quad\sum P=\sum C=32,\quad\sum PC=64,
 \qquad\sum\alpha=4a-q,\quad\sum P\alpha=8a.            \tag{2}
\]

## 2. There are at most eleven singleton predecessor blocks

Let `p` count triple `P` blocks. The first two moments give the
numbers of singleton and double `P` blocks as

\[
                       n_1=6+p,\qquad n_2=13-2p.
\]

In particular `p≤6`. Equality would give exactly one double `P`
block. But every central column has four predecessor blocks partitioning
eight labels. Its possible size patterns are

\[
                         3311,\quad3221,\quad2222.
\]

A column containing a double block therefore contains at least two
distinct double-block tops. The unique-double possibility is impossible.
Thus

\[
                             p\le5,\qquad n_1\le11.     \tag{3}
\]

This bound does not require a size-three profile in `A` or any
classification of its possible partitions.

## 3. The small weighted defect

The [degree-five support bound](1485_order_forty_eight_central_high_five.md#1-central-parameter-capacity-excludes-twelve-degree-five-elements)
says `α≤4,3,1` when `C=1,2,3`, respectively. Consequently

\[
                  v_u=7-2C-\alpha
                  \quad\text{satisfies}\quad0\le v_u\le5.
\]

Every central row has four tops, its `C` blocks sum to eight,
and its `α` values sum to `a`. Hence

\[
                      \sum_{u\in Row(z)}v_u=12-a.        \tag{4}
\]

Equations (2) give

\[
 \sum v_u=69-4a+q,\qquad\sum P v_u=96-8a,
\]

so the exact nonnegative weighted defect is

\[
                     E:=\sum(P-1)v_u=27-4a-q.           \tag{5}
\]

Let `W` be the total `v` weight on nonsingleton-`P` tops,
counting each occurrence in a central row. Since a top occurs in
exactly `P` such rows, and `P≤2(P−1)` for `P≥2`,

\[
             W=\sum_{P>1}P v_u\le2\sum(P-1)v_u=2E.    \tag{6}
\]

## 4. Every central row needs more than the global allowance

For a central row at `z`, let `k_z` count its singleton-`P`
tops and let `w_z` be its `v` weight on all other tops. Thus

\[
                         \sum_z k_z=n_1,\qquad
                         \sum_z w_z=W.                  \tag{7}
\]

If `a=6`, the row's weight sum is six by (4). Since every
singleton top has weight at most five,

\[
                              k_z+w_z\ge2.
\]

Indeed `k_z≥2` is immediate; at `k_z=1` the other tops must
supply at least one unit, and at `k_z=0` they supply all six.
Sum over the eight central rows. Using (1), (3), (5), and (6),

\[
              16\le n_1+W\le11+2(3-q)\le15,
\]

a contradiction.

If `a=5`, the row's weight sum is seven. The same argument gives

\[
                             2k_z+w_z\ge4:
\]

with one singleton the other tops supply at least two units, and
with none they supply all seven. Summing now gives

\[
             32\le2n_1+W\le22+2(7-q)\le30,
\]

again a contradiction. This excludes both cases in (1), proving the
theorem.

Equivalently, both row inequalities are
`(7−a)k_z+w_z≥2(7−a)`. Their sum implies `3a+2q≤19`,
which contradicts (1). The expanded cases above exhibit the small
integer deficits directly.

Together with the previously proved lower bound, the new top-count
range is therefore

\[
                              \boxed{15\le h\le18.}
\]
