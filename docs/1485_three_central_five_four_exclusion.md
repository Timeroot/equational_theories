# Five degree-four vertices are impossible

Research note, 19 September 2026. This is an analytic finite E1485
proof, not a Lean declaration. It does not use the independent
finite five-vertex profile check.

**Theorem.** At minimum translation degree three with exactly three
central vertices, the degree-four class cannot have size five.

Write `A,B,C,D` for the degree classes `4,n/4,5,n/5`. The
[degree-five necessity theorem](1485_three_central_requires_five.md)
gives `C≠∅` and `60|n`, so these classes are distinct. Suppose
`|A|=5`. The sharp maps `F,G:A→B` are onto, their fibers have
size at most three, and their joint map is injective. In particular
`5≤|B|²`, so `|B|≥3` and the
[opposite-parity profile argument](1485_three_central_saturated_four.md#the-saturated-profile-grid)
applies.

Use the resulting three predecessor profiles `P_p`, three successor
profiles `Q_q`, and nine tops `t_pq=P_p∩Q_q`. The five members of
`A` occupy five distinct cells `(p,q)`. An `F`-fiber meets each
`P`-row at most once; a `G`-fiber meets each `Q`-column at most
once. Write `H(t),C(t)` for the central predecessor and successor
labels of a top vertex.

## 1. A degree-five vertex has sharp count one

Fix `c∈C`, with top profiles `U,V`. Each has size three. Its
two non-top neighbors on either side have complementary degree
four or five; those of complementary degree five are sharp. If
the sharp in/out counts are `k⁻,k⁺`, the established weighted
row/column balance gives

\[
9+5k^++4(2-k^+)=9+5k^-+4(2-k^-).
\]

Thus `k⁺=k⁻∈{1,2}`. Every top predecessor and successor of
`c` participates in a good top pair: a size-three top fiber cannot
fit inside its two non-top neighbors. The
[slot bound](1485_three_central_five_profiles.md#notation-and-elementary-capacity)
gives `3≤g(c)≤4`, with `g(c)≤3` when the sharp count is two.

As in the [profile-line argument](1485_three_central_five_profiles.md#neither-profile-can-be-a-degree-four-profile-line),
`U` cannot be a `P`-line and `V` cannot be a `Q`-line. For
example, if `U=P_p`, every `v∈V` must belong to an unoccupied
profile column of row `p`, by activity. Its two noncentral pairs
with `P_p` are then both good, giving `g(c)=6`, a contradiction.

Suppose the sharp count is two. There are no `B` neighbors of
`c`. Hence for every `a∈A` the mixed products `(a,c)` and
`(c,a)` have a unique top middle, and

\[
|Q(a)\cap U|=|P(a)\cap V|=1.
\]

At least two `Q`-columns and two `P`-rows are occupied by `A`:
one profile line holds at most three vertices. The displayed
equalities and the size-three profiles therefore make `U`
transversal to all three `Q`-columns, and `V` transversal to
all three `P`-rows, even if a line is empty.

The elementary order-three Latin-square argument in the profile
note now makes `U` a central column `C=k` and `V` a central
row `H=l`: the other options were the prohibited `P,Q` lines.
Activity requires `k≠l`, so all nine endpoint pairs are noncentral.
Exactly five have their degree-four middle, one for each occupied
profile cell. The other four have good middle `c`, contradicting
`g(c)≤3`. Thus the sharp count is one in both directions.

## 2. Neither top profile can be a central line

We first sharpen the
[companion-output lemma](1485_three_central_singleton_exclusion.md#3-a-two-entry-good-row-forces-degree-four-companion-outputs).
If a good column at a top `v` has two inputs, their two degree-four
companions are the **same vertex**. Indeed the three-element fiber
`R_v⁻¹(c)` already contains its two top inputs and the sharp
predecessor of `c`. Its other non-top predecessor `b∈B` is
outside that fiber. In each associated central-row triple,
absorption and strict descent force the other noncentral output
to equal `b*v`, of degree four. Thus the companion value is
independent of which of the two good inputs was chosen.

Those two inputs cannot have the same central successor label.
In the original top grid `z_i*z_j`, suppose they have labels
`(i₁,j),(i₂,j)`, with `i₁≠i₂`, and `H(v)=k≠j`.
Their companions have labels `(i₁,h),(i₂,h)`, where `h` is
the third label besides `j,k`. They would belong to the top
predecessor permutation profile of the same member of `A`, despite
having the same central successor label. This is impossible.

Now suppose `U` is a central column. The preceding paragraph
excludes a two-entry good column, so all three good columns have
one entry. Hence `g(c)=3`, also one entry in each good row.
Every top left fiber at `c` consequently contains both its non-top
successors. If `b∈B` is the nonsharp one, then

\[
u*b=c\qquad(u\in U).
\]

Choose `a∈A` with `F(a)=b`. The permutation profile `P(a)`
meets the central column `U` once. At their common top vertex `u`,
the sharp path `u→a⇒b` gives `u*b=a`, a contradiction.
Thus `U` is not a central column. Dually `V` is not a central row.

## 3. Two exceptional sharp fibers must intersect twice

The Latin-square argument and the exclusions above show that `U`
is not transversal to the three `Q`-columns, and `V` is not
transversal to the three `P`-rows. Put

\[
m_q=|U\cap Q_q|,\qquad n_p=|V\cap P_p|.
\]

Since each list sums to three and is not `(1,1,1)`, each has at
least two entries different from one. The
[mixed-product constraint](1485_three_central_five_profiles.md#exceptional-profiles-fit-inside-a-single-sharp-fiber)
puts all occupied cells of the exceptional columns `m_q≠1`
inside a single `F`-fiber. Dually the exceptional rows lie in
a single `G`-fiber.

There cannot be a full occupied `P`-row: it would put two cells
of that row in the one exceptional `F`-fiber, whereas an `F`-fiber
meets each row at most once. Dually no `Q`-column is full.
Since there are five occupied cells, the row counts and column
counts are both `(2,2,1)`, in some order.

The exceptional columns number exactly two: all three would require
a fiber of size five. Their occupancies total at most three and at
least three, so they are the short column and one long column.
Their three occupied cells form an entire `F`-fiber. Let `q₀`
be the omitted long column. The fiber meets all three rows once,
so column `q₀` occupies both long rows and neither short row.

Dually, the exceptional rows form an entire three-element `G`-fiber
and omit a long row `p₀`, which occupies both long columns.
In particular their crossing `(p₀,q₀)` is occupied. The two
exceptional fibers consequently intersect in

\[
5-2-2+1=2
\]

members of `A`. They have the same `F`-value and the same
`G`-value, contradicting joint injectivity. This excludes `|A|=5`.
