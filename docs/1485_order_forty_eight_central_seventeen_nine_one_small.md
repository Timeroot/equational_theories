# Seventeen tops cannot have nine degree-five elements and one small profile

Independently audited analytic proof, 20 September 2026. This
excludes the order-forty configuration `m=8,h=17,a=9,q=1`, where
`q` counts degree-five elements with three top neighbors. No finite
enumeration, SAT result, or assumption that the degree-eight top
counts are balanced is used. This is not a Lean theorem or an
exclusion of every eight-central configuration.

## 1. Central deficits and singleton saturation

Let `Z,T,A,B` be the degree classes `4,10,5,8`, of sizes
`8,17,9,6`. For a top `u`, let `P_u,C_u` be its central
predecessor and successor blocks, and write `P,C` for their sizes.
Let `α,β` count its successors and predecessors in `A`.

The [block and support bounds](1485_order_forty_eight_central_high_five.md)
give

\[
 1\le P,C\le3,\qquad
 \alpha\le f(C),\quad\beta\le f(P),\qquad f=(4,3,1).
\]

Define the nonnegative deficits

\[
 v^+=7-2C-\alpha,\qquad v^-=7-2P-\beta.               \tag{1}
\]

In particular `v^+≥1` if `C=1`, and `v^-≥1` if `P=1`.
In each central row the four `C` blocks partition eight labels and
the `α` values sum to nine. Thus its `v^+` sum is three.
Dually each central column has `v^-` sum three. Every top occurs
in a central row and column, so `v^+,v^-≤3` individually.

The central moments and degree-five incidence counts are

\[
\begin{gathered}
 \sum1=17,\quad \sum P=\sum C=32,\quad\sum PC=64,\\
 \sum\alpha=\sum\beta=35,\qquad
 \sum P\alpha=\sum C\beta=72.
\end{gathered}
\]

Consequently

\[
 \sum v^+=\sum v^-=20,\qquad
 \sum Pv^+=\sum Cv^-=24,
 \qquad
 \sum(P-1)v^+=\sum(C-1)v^-=4.                         \tag{2}
\]

These are the specialized
[weighted central identities](1485_order_forty_eight_central_top_bound.md).
The existence of the one three-element first-output profile gives,
by the [one-hole theorem](1485_one_hole_first_output_grid.md), at
most four triple blocks in either direction.

If `p` counts predecessor triples, its singleton count is `p+2`,
so there are at most six singleton `P` blocks. Meanwhile

\[
 W^+:=\sum_{P>1}Pv^+\le2\sum(P-1)v^+=8.              \tag{3}
\]

If at most five central labels supported a singleton `P` block,
at least three central rows would contain no such top. Each would
contribute its full deficit three to (3), giving `W^+≥9`.
Therefore there are exactly six singleton `P` blocks, with six
distinct labels, and exactly four predecessor triples. There are
exactly two rows without a singleton-`P` top; every other row
contains exactly one. Applying the same argument dually gives six
distinct singleton `C` labels and four successor triples.

Put

\[
 J^+=\sum_{P=3}v^+,\qquad J^-=\sum_{C=3}v^-.
\]

From (2),

\[
 \sum_{P=2}v^+=4-2J^+,
 \qquad W^+=8-J^+.
\]

The two rows without singleton `P` tops contribute six to `W^+`,
so `J^+≤2`. Equality would put all positive nonsingleton-`P`
deficit in those two rows. But a positive-deficit triple `P` block
meets three rows. Hence equality is impossible, and

\[
 J^+,J^-\le1,\qquad
 \sum_{P=1}(3-v^+)=2-J^+,
 \quad\sum_{C=1}(3-v^-)=2-J^-.                       \tag{4}
\]

## 2. Only two central type matrices remain, up to duality

Let `n_pc` count tops of type `(P,C)=(p,c)`. Set

\[
 x=n_{11},\quad u=n_{12},\quad z=n_{13},\quad
 v=n_{21},\quad w=n_{31},\quad t=n_{33}.
\]

A type `(1,3)` top has `v^+≤1`, spending at least two units
of the singleton deficit in (4). Thus `z≤1`; if `z=1`, then
`J^+=0`, this top has `v^+=1`, and all other singleton-`P`
tops have `v^+=3`. Dually `w≤1`, with the analogous equality
statements. Both cannot equal one: a `(3,1)` top contributes at
least one to `J^+`.

We also need a local inequality at type `(1,2)`:

\[
                         v^-\ge v^+.                 \tag{5}
\]

Here is the full degree check, used again below. Let `I,O` be a
top's top predecessor and successor counts. The central shadows
are partitions of eight labels by blocks of size at most three,
so `I,O≥3`. Degree ten and reciprocal balance give

\[
 I+P+\beta\le10,\quad O+C+\alpha\le10,
 \qquad O-I=5(C-P)+3(\alpha-\beta).                   \tag{6}
\]

For type `(1,2)`, a failure of (5) would mean `β−α≥3`.
Then `β≥3`, `I≤6`, and `O-I≤-4`, contradicting `O≥3`.
This proves (5).

The dual weighted deficit in (2) is at least
`Σ_(12)v^+ + 2z`: use (5), and `v^-≥1` at each type `(1,3)`.
On the other hand (4), after accounting for the at least two
units used by each `(1,3)`, gives

\[
 \sum_{(1,2)}v^+\ge3u-(2-J^+-2z).
\]

Combining yields, and dually yields,

\[
                 3u+4z+J^+\le6,
                 \qquad3v+4w+J^-\le6.               \tag{7}
\]

The singleton margins and mixed moment are

\[
        x+u+z=x+v+w=6,
        \qquad x+t-z-w=4.                            \tag{8}
\]

For `z=w=0`, (7) gives `u,v≤2`, so (8) forces
`x=4,u=v=2,t=0`. For `z=1,w=0`, (7) forces
`u=0,x=5,v=1,t=0`. The remaining case is its dual.
All other entries follow from the block-size margins. Thus, with
rows indexed by `P=1,2,3` and columns by `C=1,2,3`, the only
possibilities are

\[
 \mathrm A:\quad
 (n_{pc})=\begin{pmatrix}4&2&0\\2&1&4\\0&4&0\end{pmatrix},
 \qquad
 \mathrm B:\quad
 (n_{pc})=\begin{pmatrix}5&0&1\\1&3&3\\0&4&0\end{pmatrix},
 \quad\text{or }\mathrm B^{\mathsf T}.                \tag{9}
\]

This is an analytic case split, not an enumerated list assumed as
a premise.

## 3. Case A: a central row demands a missing singleton weight

In case A, (7) with `u=v=2` forces `J^+=J^-=0` and equality
in its derivation. All four type-`(1,1)` tops consequently have
`v^+=v^-=3`, hence `(α,β)=(2,2)`.
The two type-`(1,2)` tops have

\[
 v^-=v^+,\quad \beta=\alpha+2,
 \qquad \sum_{(1,2)}\alpha=2.
\]

Dually the two type-`(2,1)` tops have

\[
 \alpha=\beta+2,\qquad \sum_{(2,1)}\beta=2,
 \qquad\sum_{(2,1)}\alpha=6.
\]

Equality in the weighted sums leaves no other positive deficit
with `P>1` or `C>1`. Therefore the remaining types have

| Type | `(α,β)` |
| --- | --- |
| `(2,2)` | `(3,3)` |
| `(2,3)` | `(1,3)` |
| `(3,2)` | `(3,1)` |

There is no central row of pattern `3311`. Its two `C=3` tops
would contribute two to the `α` sum. Its two `C=1` tops
contribute at most six: two units contribute four, a unit and a
type `(2,1)` at most six, and the two type-`(2,1)` tops together
exactly six. Their total cannot be nine.

The number of singleton-`C` occurrences in all central rows is
`4+2·2=8`. If `R_3311,R_3221,R_2222` count their three possible
patterns, this gives `R_3311-R_2222=0`. Hence no row is `2222`
either: every row has pattern `3221`.

A row containing a type-`(1,2)` top contains no other such top:
the six singleton `P` labels are distinct. Its other `C=2` top
therefore has `α=3`, and its `C=3` top has `α=1`. If the
chosen top had `α=0`, the singleton `C` top would need `α=5`,
impossible. Both type-`(1,2)` tops thus have `α≥1`; their sum
two forces `α=1` each. By the dual argument, both type-`(2,1)`
tops have `β=1` and therefore `α=3`.

Now a row through either type-`(1,2)` top needs a singleton `C`
top with `α=9-1-3-1=4`. But all singleton `C` tops have
`α=2` or `3`. This excludes case A.

## 4. Case B: two rectangles are forced to overlap

Let `s` be the unique type-`(1,3)` top, with `P_s={r}`.
The equality conclusions after (4) give

\[
 \alpha_s=0,\qquad
 \alpha=2\text{ at every type }(1,1),\qquad J^+=0.
\]

Since `s` contributes at least one to `J^-≤1`, it has
`v_s^-=1`, hence `β_s=4`, and `J^-=1`. All type-`(2,3)`
tops therefore have `β=3`. They also have `α=1`: if `α=0`,
(6) gives `O-I=-4` with `I≤5`, impossible. All type-`(3,2)`
tops have `α=3` because `J^+=0`; if `β=0`, (6) gives
`O-I=4` with `O≤5`, again impossible. Thus

\[
       (\alpha,\beta)=(1,3)\text{ at type }(2,3),
       \qquad(3,1)\text{ at type }(3,2).              \tag{10}
\]

Let `D={d_1,d_2}` be the two labels not supporting a singleton
`P` block. Each of the other five singleton-`P` rows has a
unit top supplying its entire `v^+` sum three. The row `r`
has `s` supplying one and needs two more. The rows `d_1,d_2`
need three each. Since `J^+=0`, all these additional positive
deficits lie on `P=2` blocks, necessarily contained in
`{r,d_1,d_2}`.

View a positive-deficit `P=2` block as an edge weighted by its
`v^+`; if several tops have the same block, add their weights.
The vertex weights are `(2,3,3)`, so the three combined edge
weights are exactly

\[
 \{r,d_1\}:1,\qquad \{r,d_2\}:1,
 \qquad\{d_1,d_2\}:2.                               \tag{11}
\]

By (10), the only possible positive edges are the unique
type-`(2,1)` top and type-`(2,2)` tops.

The dual geometry is even more rigid. Let `E` be the pair of
labels not supporting a singleton `C` block. The total positive
deficit incidence at nonsingleton `C` blocks is `W^-=8-J^-=7`.
The two columns in `E` already account for six. The block `C_s`
has size three and weight `v_s^-=1`, so it must contain both
labels in `E` and one outside, using the sole remaining incidence.
Consequently every positive-deficit `C=2` block equals `E`.
The weighted sum in (2) leaves total `v^-` weight two on such
blocks; by (10) these are all type `(2,2)`.

There is again no `3311` row. Its two `C=3` tops contribute
at most two to `α`. Its two distinct `C=1` tops include at
most one type `(2,1)`, so they contribute at most `4+2=6`.
The total is at most eight, not nine. This time the singleton
`C` occurrences total `5+2=7`, giving

\[
                       R_{3311}-R_{2222}=-1.
\]

Thus exactly one row is `2222`. It contains no singleton-`P`
top, since those all have `C=1` or `3`. Rename `d_1,d_2`
so that this row is `d_1`. The unique type-`(2,1)` top cannot
occur there. Its positive edge in (11) must therefore be
`{r,d_2}`, with weight one. The remaining positive type-`(2,2)`
blocks have combined weights

\[
                  \{d_1,d_2\}:2,
                  \qquad\{r,d_1\}:1.                \tag{12}
\]

At type `(2,2)`, positive `v^+` forces positive `v^-`.
Indeed if `v^-=0`, then `β=3`; if `v^+>0`, then `α≤2`.
Equation (6) would give `O-I≤-3`, whereas `I≤5,O≥3`.

The two distinct blocks in (12) therefore require at least two
tops with positive `v^-`. Its total on type `(2,2)` is two, so
there are exactly two such tops, each of dual weight one. Their
`P` blocks are `{d_1,d_2}` and `{r,d_1}`, respectively, while
both their `C` blocks are `E`. Their central rectangles overlap
in `{d_1}×E`, contradicting the disjoint central rectangle tiling.

This excludes case B; passing to the opposite magma excludes its
transpose. All possibilities in (9) are impossible, completing the
analytic exclusion of `m=8,h=17,a=9,q=1`.

The [profile-capacity inequality](1485_order_forty_eight_central_profile_potentials.md)
already gives `q≤1` for these class sizes whenever `q>0`.
Consequently every remaining seventeen-top case with nine degree-five
elements must have **all nine profiles of size four**. The present
argument does not exclude that all-four-profile case.
