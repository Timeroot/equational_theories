# Eighteen tops and seven degree-five elements cannot have two small profiles

Independently audited proof, 20 September 2026. This excludes
the order-forty configuration `m=8,h=18,a=7,q=2`. The reduction
is analytic; its pure central subcase uses the existing audited
200-fixture lemma. There is no new finite enumeration or SAT premise,
and no balanced-degree-eight assumption. The cases `q=0,1` remain
outside this theorem, and no Lean theorem is asserted here.

For a top let `P,C` be its central block sizes, `α,β` its
degree-five successor and predecessor counts, and

\[
                   v^+=7-2C-\alpha,\qquad v^-=7-2P-\beta.
\]

The [weighted identities](1485_order_forty_eight_central_top_bound.md)
give

\[
                   \sum(P-1)v^+=\sum(C-1)v^-=4.        \tag{1}
\]

Each row has `v^+` sum five, and each column has `v^-` sum
five. The support bounds give `α≤(4,3,1)_C` and the dual
bound, sharpened by
[singleton-source saturation](1485_singleton_source_first_degree_saturation.md)
to `α≤3` when `C=1` and `β≤3` when `P=1`.
Thus singleton blocks have their corresponding deficit at least two.
We use the usual top counts `I,O` and identities

\[
 I,O\ge3,\quad I+P+\beta\le10,\quad O+C+\alpha\le10,
 \qquad O-I=5(C-P)+3(\alpha-\beta).                   \tag{2}
\]

## 1. Distinct singleton labels and the extreme mixed types

A row without a singleton predecessor would have deficit at most
the global weighted sum four, not five. Thus every label supports
a singleton `P` block, and dually a singleton `C` block. The
[one-hole bound](1485_one_hole_first_output_grid.md) gives at most
four triple blocks per direction. The singleton margins are four
plus the triple counts; consequently there are exactly four triples
and eight distinct singleton labels in each direction.

Write `u=n12,z=n13,v=n21,w=n31,t=n33`. From (1),

\[
 u+2z\le2,\quad v+2w\le2,
 \qquad t=u+2z+w=v+z+2w.                             \tag{3}
\]

The last equalities are the central moments with both triple counts
four. Suppose `z=1`. Its unique `(1,3)` top `s` has `β=3`
by (1) and the singleton bound. Equation (2) excludes `α=1`,
so `(α_s,β_s)=(0,3)` and its deficits are `(1,2)`.

The row at its singleton `P` label `r` needs four further units
of outgoing deficit. It has no other singleton predecessor. To
attain the entire weighted sum four in this one row, every positive
weighted outgoing deficit must occur on predecessor pairs containing
`r`; a predecessor triple or a positive block outside that row
would waste part of the budget. In particular `w=0`. Equations
(3) give `u=0,t=2,v=1`.

The dual weighted sum is consumed entirely by `s`, so all other
tops with `C>1` have `v^-=0`. At `(2,2)` this gives `β=3`
and forces `α=3` by (2); at `(2,3)` it gives `β=3` and
forces `α=1`. Predecessor triples have no positive outgoing
deficit, as just proved. The only remaining positive outgoing
deficit is therefore at the unique `(2,1)` top `b`, with
`v_b^+=4`, hence `α_b=1`. Equation (2) forces `β_b=0`.

Its singleton successor label `c` has no other singleton-`C`
top. Since `v_b^-=3`, that column needs two more units, supplied
only by `s`. Thus `c∈C_s`; the outgoing argument already gives
`r∈P_b`. Their rectangles overlap at `(r,c)`, impossible.
This excludes `z=1`, and duality excludes `w=1`.

We are left with

\[
 n12=n21=n33=u\in\{0,1,2\},\quad n11=8-u,
 \qquad n22=2,\quad n23=n32=4-u.                     \tag{4}
\]

For `u=0`, this is the familiar profile `8(11),2(22),4(23),4(32)`.
Its unit singleton labels are distinct, every row and column is
`3221`, and equality in the one-hole bound gives the required
maximal-block intersections and deficiency separation. The
[common 200-fixture lemma](1485_order_forty_eight_central_eighteen_two_small.md#common-finite-central-profile-lemma)
excludes even one small first-output profile, hence excludes `q=2`.

For `u=2`, the two `(2,1)` tops consume all outgoing weighted
deficit, each with weight two. Dually both `(1,2)` tops have
`β=3`; (2) then forces `α≥1`, so their `v^+≤2`.
A row containing either `(1,2)` has no other singleton predecessor.
It cannot contain two `(2,1)` tops: its successor partition contains
a double, so is not `3311`. Its total deficit is consequently at
most `2+2=4`, not five. This excludes `u=2`.

## 2. The last mixed pair forces one exceptional double-double top

Suppose `u=1`. Let `x` be the unique `(1,2)` top, `y` the
unique `(2,1)` top, and write `P_x={r},C_y={c}`. Their
rectangles cannot have both `r∈P_y` and `c∈C_x`. By duality
we may assume

\[
                              r\notin P_y.            \tag{5}
\]

The row at `r` has no unit top and does not contain `y`, hence
has no singleton successor and is `2222`. Its three nonsingleton
predecessors need deficit `5-v_x^+=2+α_x`. The top `y`,
which is outside the row, consumes at least two of (1). Thus

\[
 \alpha_x=0,\quad v_y^+=2,\quad\alpha_y=3,
\]

and all the remaining outgoing weighted deficit two lies at
predecessor pairs in that row. Predecessor triples have zero
deficit, as do `(2,3)` tops, which cannot be in a `2222` row.
Only the two `(2,2)` tops can carry this remaining deficit.

Since `α_x=0`, (2) and (1) give `β_x∈{1,2}`. If `β_x=1`,
its dual weight four would exhaust (1), forcing both `(2,2)`
tops to have `β=3` and hence `α=3`. That contradicts their
positive outgoing deficit. Therefore `β_x=2`, leaving one unit
of dual weighted deficit.

Every `(2,2)` top with positive outgoing deficit has `α≤2`
and must have `β≤2` by (2). Each uses at least one dual unit.
Hence exactly one such top, say `e`, carries all this deficit:

\[
        (\alpha_e,\beta_e)=(1,2),\qquad r\in P_e.
\]

The other `(2,2)` top has `(3,3)`. The remaining nonsingleton
types are fixed as well: `(2,3)` has `(1,3)`, `(3,2)` has
`(3,1)`, and `(3,3)` has `(1,1)`.

At `y`, (2) with `α_y=3` gives `β_y∈{1,2}`. Its column
needs at least three units from nonsingleton successor blocks. The
only such positive deficits are `v_x^-=3` and `v_e^-=1`, so
`c∈C_x`. Since `r∈P_e∩P_x`, rectangle disjointness gives
`C_e∩C_x=∅`; in particular `c∉C_e`. Its exact column
deficit then forces `β_y=1`.

Thus the complete nonunit neighbor-count table is

| Type | `(α,β)` |
| --- | --- |
| `(1,2)` | `(0,2)` |
| `(2,1)` | `(3,1)` |
| Exceptional `(2,2)` | `(1,2)` |
| Other `(2,2)` | `(3,3)` |
| `(2,3)` | `(1,3)` |
| `(3,2)` | `(3,1)` |
| `(3,3)` | `(1,1)` |

## 3. Two forced three-neighbor tops leave a central row too small

The predecessor pairs `P_e,P_y` are disjoint. Otherwise their
common row, which is not `r` by (5), would have its unit top
contributing at least two deficit units, and `e,y` contributing
two each: at least six instead of five. Write `P_e={r,d}`.

For the seven unit tops, the row deficits now determine all `α`
values. The three with predecessor labels in `P_y∪{d}` have
`α=2`; the other four have `α=0`. Dually, the unit with
successor label in `C_x\{c}` has `β=3`, the two with labels
in `C_e` have `β=1`, and the other four have `β=0`.
Here the disjointness of `C_e,C_x` was proved in §2.

A unit top with `α=2,β=0` would have `O−I=6` by (2),
despite `O≤7,I≥3`. Thus the three unit tops with positive
`α` are exactly the three with positive `β`. The unit top
at predecessor label `d` cannot have its successor in `C_e`,
since its rectangle would overlap `P_e×C_e`. Its successor is
therefore the unique label of `C_x\{c}`, and its neighbor
counts are `(α,β)=(2,3)`.

For this unit, (2) gives `O=I−3` and `I≤6`; since `O≥3`,
we have `I=6,O=3`. Exactly the same conclusion holds for `e`,
whose counts are `(1,2)` and whose central type is `(2,2)`.

The central row at `d` contains this unit and `e`; it has
pattern `3221`. Its other double is not `x`, whose predecessor
label is `r`, so it has `α=3` and hence `O≤5`. Its triple
has `α=1`, hence `O≤6`. The four top-successor counts in
this row total at most

\[
                              3+3+5+6=17.
\]

But their exact sum is `h=18`: the top successor sets of the
four tops in any central row partition the top class, by unique
good middle at a central endpoint. This contradiction excludes
`u=1` and completes the proof.

Together with the
[bound excluding at least three small profiles](1485_order_forty_eight_central_eighteen_seven_profile_bound.md),
any remaining eighteen-top case with seven degree-five elements
has `q=0` or `q=1`. Neither remaining case is resolved here.
