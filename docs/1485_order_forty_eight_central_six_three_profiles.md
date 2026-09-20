# Eight central elements have at most six three-profiles

Independently audited analytic theorem, 20 September 2026. This is a
necessary finite E1485 restriction, not a Lean theorem or a complete
exclusion of eight-central models. No enumeration or SAT premise is used.

Assume order forty, minimum degree four, and eight central elements.
Let `a` count degree-five elements and `q` count those with three top
predecessors and three top successors; the other `a−q` have four.

**Theorem.** `q≤6`.

This has no lower-bound hypothesis on `a`. In particular, together with
the [ten-degree-five profile bound](1485_order_forty_eight_central_ten_five_profile_bound.md),
the [three-profile exclusion](1485_order_forty_eight_central_three_three_profiles.md),
and the later [unused-top source bound](1485_first_degree_source_unused_tops.md#3-fifteen-tops-and-eight-central-elements),
it leaves only `h=16,q∈{1,2}` when `a=10`.

## 1. A nonnegative local potential

For a top write `P,C` for its central predecessor and successor block
sizes, and `α,β` for its degree-five successor and predecessor counts.
The existing support bounds give

\[
 1\le P,C\le3,\qquad \alpha\le f(C),\quad\beta\le f(P),
 \qquad f=(4,3,1).
\]

Set

\[
 H=P+C-PC+4(\alpha+\beta)-2(P\alpha+C\beta)
       +7(\mathbf1_{P=3}+\mathbf1_{C=3}).
\]

The following table, together with its dual, proves `H≥0` using only
these bounds and the nonnegativity of `α,β`:

| `(P,C)` | `H` |
| --- | --- |
| `(1,1)` | `1+2α+2β` |
| `(1,2)` | `1+2α` |
| `(1,3)` | `8+2α−2β` |
| `(2,2)` | `0` |
| `(2,3)` | `6−2β` |
| `(3,3)` | `11−2α−2β≥7` |

Write `p_3,c_3` for the numbers of triple blocks in the two directions.
The exact moments are

\[
 \sum P=\sum C=32,\quad\sum PC=64,
 \quad\sum\alpha=\sum\beta=4a-q,
 \quad\sum P\alpha=\sum C\beta=8a.
\]

Consequently

\[
                  0\le\sum H=7(p_3+c_3)-8q.            \tag{1}
\]

If `q>0`, the [one-hole grid theorem](1485_one_hole_first_output_grid.md)
gives `p_3,c_3≤4`. Thus (1) gives `q≤7`.

## 2. Equality would force an impossible degree-five profile

Suppose `q=7`. Then `p_3=c_3=4` and every local potential vanishes.
In particular there are no block types `(1,1),(1,2),(2,1),(3,3)`;
every `(1,3)` top has `(α,β)=(0,4)`, and every `(3,1)` top has
`(α,β)=(4,0)`.

Let `n_ij` count tops of type `(i,j)`. The remaining types are
`13,31,23,32,22`. Since the number of triple blocks in each direction
is four, the marginal equations give

\[
 n_{13}=n_{31}=2h-28.
\]

On the other hand,

\[
 \sum(P-2)(C-2)=4h-64=-n_{13}-n_{31}.
\]

Hence `h=15`, and the complete block inventory is

\[
             n_{13}=n_{31}=n_{23}=n_{32}=2,
             \qquad n_{22}=7.                         \tag{2}
\]

Every top with a singleton predecessor block therefore has `α=0`.
No four-profile degree-five element has such a top predecessor. Its
four predecessor blocks partition eight central labels, so the number
of singleton parts equals the number of triple parts. It follows that
**no four-profile element has a top predecessor with `P=3` either**.

Choose a type-`31` top `u`, which exists by (2). It has `α=4,β=0`.
Write `I,O` for its numbers of top predecessors and successors.
Reciprocal balance and the ordinary degree bound give

\[
 O-I=5(C-P)+3(\alpha-\beta)=2,
 \qquad I\ge3,\qquad O\le10-C-\alpha=5.
\]

Thus `I=3,O=5`, and `u` has no ordinary degree-eight successor.
The [small-block top-return theorem](1485_top_return_small_blocks.md)
also forbids a top-valued top product with first input `u`, since
`P_u=3`. All fifteen top inputs in the row of `u` therefore produce
central or degree-five outputs.

If `γ` counts its three-profile degree-five successors, their exact
top-input fibers have size two, whereas the four-profile successors'
fibers have size three. The central output contributes four. Therefore

\[
                   15=4+2\gamma+3(4-\gamma)=16-\gamma.
\]

So `γ=1` and `u` has three four-profile successors. This contradicts
the preceding conclusion that no `P=3` top precedes any four-profile
element. Equality is impossible, proving `q≤6`.
