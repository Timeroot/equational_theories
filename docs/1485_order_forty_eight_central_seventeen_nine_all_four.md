# Seventeen tops cannot have nine all-four degree-five profiles

Independently audited analytic proof, 20 September 2026.
Assume order forty, minimum four, eight central elements, seventeen
tops, and nine degree-five elements, all with four top neighbors in
each direction. We exclude this case: first extreme mixed blocks,
then three elementary count inventories, then the last two matrices
by a quadrant count and overlapping weighted stars. No enumeration,
SAT premise, or balance assumption
at the degree-eight vertices is used.

Write `P,C` for top central block sizes, `α,β` for degree-five
successor and predecessor counts, and

\[
 v^+=7-2C-\alpha,\qquad v^-=7-2P-\beta.
\]

The standard central and class-count identities give

\[
 \sum1=17,\quad\sum P=\sum C=32,\quad\sum PC=64,
 \quad\sum\alpha=\sum\beta=36,
 \quad\sum(P-1)v^+=\sum(C-1)v^-=5.                    \tag{1}
\]

Each central row has `v^+` sum three, and each column has
`v^-` sum three. The support bounds and the
[singleton-source saturation theorem](1485_singleton_source_first_degree_saturation.md)
give `α≤(3,3,1)_C`, `β≤(3,3,1)_P`. At singleton `C`
blocks the row bound also gives `α≥2`; dually `β≥2` at
singleton `P` blocks. We use

\[
 I,O\ge3,\quad I+P+\beta\le10,\quad O+C+\alpha\le10,
 \qquad O-I=5(C-P)+3(\alpha-\beta).                   \tag{2}
\]

## 1. Four is still an upper bound for triple counts

A central row of pattern `3311` has `α` sum at most eight,
not nine. Hence every central row and column has pattern `3221`
or `2222`. In particular the opposite blocks of the `P=3`
tops are pairwise disjoint, and their total size is at most eight.
The same holds dually. The `P` blocks of all `C=1` tops are
also pairwise disjoint, and so are the `C` blocks of `P=1` tops.

Put `u=n12,z=n13,v=n21,w=n31,t=n33` and `U=u+2z,V=v+2w`.
Since singleton deficits are at least two, (1) gives `U,V≤2`.
The central moments give

\[
\begin{aligned}
 n11&=4+z+w-t,\\
 p&=2+U+w-t,&q&=2+V+z-t,\\
 n32&=2+U-2t,&n23&=2+V-2t,\\
 n22&=9-2U-2V+4t,                                   \tag{3}
\end{aligned}
\]

where `p,q` count predecessor and successor triples. Thus `p≤5`.
Equality forces `U=2,w=1,t=0`, giving
`Σ_(P=3)C=w+2n32+3t=9`, contrary to the disjointness bound.
Therefore `p≤4`, and dually `q≤4`, without assuming any
three-element first-output profile.

Let `J^+=Σ_(P=3)v^+`. Equation (1) gives

\[
                        W^+:=\sum_{P>1}Pv^+=10-J^+\le10.
\]

There are `2+p` singleton `P` tops. If `p≤2`, at least four
rows lack such a top, contributing at least twelve to `W^+`.
Hence `p≥3`; dually `q≥3`.

If `p=3`, the five singleton `P` labels are distinct, for a
repeat would again leave four empty rows. They cannot include a
type `(1,3)` top: the three empty rows contribute nine to `W^+`,
while that top's own row, having `v^+≤1`, needs at least two
more units from nonsingletons. Therefore

\[
 p,q\in\{3,4\},\qquad p=3\Rightarrow n13=0,
 \qquad q=3\Rightarrow n31=0.                        \tag{4}
\]

## 2. Both extreme mixed types cannot occur

At a type `(1,3)` top, (1) gives `2(5−β)≤5`, while
singleton-source saturation gives `β≤3`. Thus `β=3`.
If `α=1`, (2) gives `O−I=4`, but `O≤6,I≥3`.
Consequently

\[
 (1,3)\Rightarrow(\alpha,\beta)=(0,3),\qquad
 (3,1)\Rightarrow(\alpha,\beta)=(3,0).                \tag{5}
\]

Each type occurs at most once. Suppose both occur. By (4),
`p=q=4`; (3) gives `u=v=0,t=1`, and the matrix is

\[
                    \begin{pmatrix}5&0&1\\0&5&2\\1&2&1\end{pmatrix}.
\]

The `(3,1)` top consumes four units of the outgoing weighted
deficit, and `(1,3)` consumes four of the dual one. A type
`(2,3)` with `α=0` would require `β≤2` by (2), consuming
at least two additional dual units; thus all `(2,3)` tops have
`(α,β)=(1,3)`. Dually `(3,2)` tops have `(3,1)`, and the
`(3,3)` top has `(1,1)`. The remaining unit of each weighted
deficit lies on `(2,2)`. They must be the same top: a top with
`(α,β)=(2,3)` would give `O−I=-3,I≤5`, impossible.
Thus exactly one `(2,2)` has `(2,2)`, and the other four have
`(3,3)`.

These nonunit tops contribute 26 to `Σα=36`, so the five unit
tops, each with `α≥2`, all have `α=2`. Dually they have
`β=2`. The row through `(1,3)` contains it with `α=0` and
has pattern `3221`; it therefore needs its singleton `C` top
to have `α=3`. The only such singleton top is `(3,1)`.
Dually the column through `(3,1)` needs `(1,3)`. Their central
rectangles overlap, a contradiction.

## 3. A lone `(1,3)` also leads to a contradiction

Suppose `n13=1,n31=0`. Then `U=2,u=0` and (4) forces
`p=4`. Equation (3) gives `t=0`, `v∈{0,1}`, and

\[
 n11=5,\quad n22=5-2v,\quad n23=2+v,\quad n32=4.     \tag{6}
\]

Let `s` be the `(1,3)` top, so `(α_s,β_s)=(0,3)`.
Its contribution four leaves exactly one unit of dual weighted
deficit. This lies at exactly one `C=2` top, either `(2,2)`
with `β=2` or `(3,2)` with `β=0`. All other `(2,2)` tops
have `β=3,α=3`; all `(2,3)` tops have `β=3,α=1`.

Consider the three columns indexed by `C_s`. Each contains `s`
as its unique predecessor singleton, so its pattern is `3221`.
The maximal `β` values are `3,3,3,1`, totaling ten. To obtain
nine, each column needs one unit of deficit from these maxima.
Apart from a possible `(2,1)` top, the only source is the one
exceptional `C=2` top, whose block meets just two columns.
Thus `v=1`, and the unique `(2,1)` top, say `t`, has its
singleton label `c∈C_s`. Its value must be `β_t=2`: smaller
values would already give a column deficit at least two. Equation
(2) then forces `α_t=3` (values at singleton `C` are two or
three).

The exceptional dual-deficit top cannot be `(3,2)`. Otherwise
all outgoing deficit apart from the two units at `t` would occur
on predecessor triples, giving the impossible parity equation
`5=2+2J^+`. It is therefore a `(2,2)` top `e` with `β_e=2`.
Equation (2) gives `α_e≥1`, so `v_e^+∈{0,1,2}`. Again
counting the outgoing weighted deficit gives

\[
                          5=2+v_e^++2J^+.
\]

Consequently `v_e^+=1,J^+=1`. All normal `(3,2)` tops have
`β=1`, and (2) forces `α≥2`, so exactly one of them has
`v^+=1`. Call it `b`. The complete positive nonsingleton
outgoing-deficit list is therefore

\[
          t:(P,v^+)=(2,2),\qquad
          e:(2,1),\qquad b:(3,1).                    \tag{7}
\]

Write `P_s={r}`. If `r∈P_t`, the rectangles of `s,t`
overlap at `(r,c)`, because `c∈C_s`. Otherwise the row at
`r`, containing `s` with `α_s=0`, must have a unit top with
`α=3` as its singleton successor. Thus `s` shares its `P`
label with a unit. The five unit `P` labels are distinct by §1,
so exactly three central rows have no predecessor singleton.
They contribute nine to `W^+=10−J^+=9`, exhausting it.

All three blocks in (7) are therefore contained in this three-label
set `L`. The triple block `P_b` is all of `L`. On the two
labels of `P_t`, its weight two plus the weight one from `b`
already supply the full row deficit three. The pair `P_e` must
avoid both labels, but cannot fit in the one remaining label.
This contradiction excludes a lone `(1,3)`; the dual argument
excludes a lone `(3,1)`.

## 4. Five intermediate paired counts

We have proved `n13=n31=0`. Equations (3)–(4) now give
`u,v∈{1,2}`, and either `t=0`, or `t=1,u=v=2`.
The five remaining matrices are

\[
 \begin{pmatrix}4&1&0\\1&5&3\\0&3&0\end{pmatrix},
 \quad\begin{pmatrix}4&1&0\\2&3&4\\0&3&0\end{pmatrix},
 \quad\begin{pmatrix}4&2&0\\1&3&3\\0&4&0\end{pmatrix},
 \quad\begin{pmatrix}4&2&0\\2&1&4\\0&4&0\end{pmatrix},
 \quad\begin{pmatrix}3&2&0\\2&5&2\\0&2&1\end{pmatrix}.
\]

These are necessary central incidence inventories, not models.

## 5. Three of the matrices are impossible

First note the exact identity

\[
                    \sum_{P=1}\alpha=\sum_{P=3}\alpha, \tag{8}
\]

obtained by subtracting `2Σα=72` from `ΣPα=72`.
In any `3221` central row, a `C=2` top must have `α≥2`:
the other three tops contribute at most `3+3+1=7` to the
required total nine.

Consider the second displayed matrix, with `u=1,v=2,t=0`.
The two `(2,1)` tops consume at least four of the weighted
deficit five. A positive deficit on a predecessor triple would cost
at least two, so every `P=3` top has `v^+=0`. There are
three such tops, all `(3,2)`, giving `Σ_(P=3)α=9`.
The four units contribute at least eight to the left side of (8),
forcing the unique `(1,2)` top to have `α≤1`. But singleton
successor occurrences total `4+2·2=8`, and there are no `3311`
rows. Every row is therefore `3221`, where this top must have
`α≥2`. This contradiction excludes the second matrix; duality
excludes the third.

Now consider the fifth matrix, `u=v=2,t=1`. The same weighted
deficit argument forces `v^+=0` on predecessor triples. These
are two `(3,2)` tops and one `(3,3)`, so
`Σ_(P=3)α=2·3+1=7`. The three units already contribute at
least six to (8). The singleton successor occurrences total
`3+2·2=7`, so exactly one row is `2222` and the others are
`3221`. Since `p=3`, the two `(1,2)` tops have distinct
singleton predecessor labels by §1; at least one lies in a
`3221` row and has `α≥2`. Thus the left side of (8) is
at least eight, not seven. This excludes the fifth matrix.

Only the first and fourth matrices remain:

\[
 \boxed{
 \begin{pmatrix}4&1&0\\1&5&3\\0&3&0\end{pmatrix},
 \qquad\begin{pmatrix}4&2&0\\2&1&4\\0&4&0\end{pmatrix}.}
\]

The next section excludes the second inventory. The first is treated
separately after it.

## 6. The four-triple inventory overfills a four-by-four quadrant

Consider

\[
                         \begin{pmatrix}4&2&0\\2&1&4\\0&4&0\end{pmatrix}.
\]

Singleton successor occurrences total `4+2·2=8`. Since there
are no `3311` rows, every row is `3221`; the dual statement
holds for columns. The two `(2,1)` tops consume at least four
units of the outgoing weighted deficit, so every predecessor triple
has `v^+=0`, giving `α=3` at all four `(3,2)` tops.
Equation (8) therefore gives `Σ_(P=1)α=12`. The four units
have `α≥2`, and the two `(1,2)` tops have `α≥2` because
their rows are `3221`. All six bounds are equalities. Applying
the same argument dually, then (2) and the remaining weighted
deficit, determines every pair of neighbor counts:

| Central type | `(α,β)` |
| --- | --- |
| `(1,1)` | `(2,2)` |
| `(1,2)` | `(2,3)` |
| `(2,1)` | `(3,2)` |
| `(2,2)` | `(2,2)` |
| `(2,3)` | `(1,3)` |
| `(3,2)` | `(3,1)` |

For clarity, at `(1,2)` the already known `α=2` and (2)
force `β=3`; dually `(2,1)` has `α=3`. These pairs consume
four units of each weighted deficit. Its last unit lies at the unique
`(2,2)` top, giving `(2,2)` there. All remaining nonsingleton
weighted deficits are zero, giving the last two rows of the table.

Let `S` be the union of the two predecessor pairs on `(2,1)`
tops. They are disjoint, because a central row has only one
singleton successor; hence `|S|=4`. Unit predecessor labels are
exactly `Z\S`. At a row indexed by `Z\S`, the unit contributes
`α=2` and the successor triple contributes one, so both successor
doubles must be `(3,2)` tops with `α=3`. At a row in `S`,
the singleton contributes three and the triple one, so exactly one
double is `(3,2)` and the other is `(1,2)` or `(2,2)`.

Thus the two singleton `P` blocks from `(1,2)` and the pair
from `(2,2)` partition `S`. The predecessor-triple multiplicity
at each central label is

\[
                           \lambda_z=2-\mathbf1_S(z).
\]

Dually let `T` be the union of the two successor pairs on `(1,2)`.
It has size four, unit successor labels are `Z\T`, and the
two singleton `C` blocks from `(2,1)` and the pair from `(2,2)`
partition `T`. The successor-triple multiplicity is

\[
                           \mu_z=2-\mathbf1_T(z).
\]

There are four maximal blocks in each direction, each pair
intersecting in at most one central label. Consequently

\[
             16\ge\sum_z\lambda_z\mu_z=16+|S\cap T|.
\]

Therefore `S,T` are complementary four-element subsets of `Z`.
Every maximal predecessor block contains exactly two labels in `T`:
it meets each of the two `(1,2)` successor pairs, which partition
`T`, at most once, and the total incidence on `T` is eight
across four such blocks. Its remaining label lies in `S`. Dually,
each maximal successor block has two labels in `S` and one in `T`.

Now count rectangle cells in `S×T`. The two `(1,2)` rectangles
lie there and contribute four cells; the two `(2,1)` rectangles
contribute four more, and `(2,2)` contributes another four.
The unit rectangles lie in the opposite quadrant `T×S`.

The four `(3,2)` successor pairs partition `Z`, since every
central column has exactly one predecessor triple. Each corresponding
predecessor triple contains exactly one element of `S`. These
rectangles therefore contribute

\[
              \sum_{(3,2)}|P\cap S|\,|C\cap T|
                   =\sum_{(3,2)}|C\cap T|=4
\]

cells to `S×T`. Dually, the four `(2,3)` predecessor pairs
partition `Z`, and their successor triples each contain one
element of `T`, so they contribute four cells as well.

The disjoint central rectangle tiling would thus put
`4+4+4+4+4=20` cells into a quadrant with only `4·4=16`
cells. This contradiction excludes the four-triple inventory.

## 7. The three-triple inventory forces two overlapping stars

It remains to exclude

\[
                         \begin{pmatrix}4&1&0\\1&5&3\\0&3&0\end{pmatrix}.
\]

Let `x` be its unique `(1,2)` top and `y` its unique `(2,1)`
top. Put `J=Σ_(P=3)v^+`. Its five singleton predecessor labels
are distinct by §1. Let `L` be the other three labels. Those
three rows contribute nine to `W^+=10−J`, so `J≤1`.
Equation (8), or the unweighted deficit sum, gives
`Σ_(P=1)α=9−J`.

If `J=1`, the four units must all have `α=2`, and `α_x=0`.
Each singleton-predecessor row already has deficit three, so every
positive nonsingleton predecessor block is contained in `L`.
There is exactly one positive-deficit predecessor triple, with
weight one, and its block equals `L`. The pair `P_y` has
weight `v_y^+≥2`; its two labels therefore receive at least
three each. Their required deficit is three, so `v_y^+=2` and
both are saturated. The weighted total five leaves one more unit
on a predecessor pair. That pair would have to lie in `L` but
avoid both saturated labels, impossible. Thus `J=0`; duality gives
`Σ_(C=3)v^-=0` as well.

Consequently all `(3,2)` tops have `(α,β)=(3,1)` and all
`(2,3)` tops have `(1,3)`. For example, `(3,2),α=3,β=0`
would give `O−I=4` in (2), despite `O≤5,I≥3`.

The five singleton predecessor deficits now sum to fourteen, and
each is at most three. Exactly one has weight two and the other
four have weight three. Let `r` be that exceptional singleton
label. All positive nonsingleton deficit is on predecessor pairs;
their weighted incidence vector is

\[
                   (3,3,3,1)\quad\text{on }L,\{r\}.   \tag{9}
\]

The pair `P_y` has weight at least two, so cannot contain `r`.
If its weight were three, its two labels would be saturated. All
remaining pairs would then equal the pair of `r` and the third
label of `L`, forcing equal residual degrees at those two labels.
Their required degrees are one and three, a contradiction. Thus
`v_y^+=2` and `α_y=3`.

After removing this pair from (9), only `(2,2)` tops have
positive outgoing deficit. Their weighted degrees are three at the
label `l∈L\P_y` and one at each of the other three labels.
Their total edge weight is three, so every edge contains `l`;
the other labels each require a distinct edge of weight one.
Exactly three `(2,2)` tops therefore have `v^+=1,α=2`,
and their predecessor blocks all contain `l`. The other two
`(2,2)` tops have `α=3`.

Dually exactly three `(2,2)` tops have `v^-=1,β=2`, and
their successor blocks all contain one label `d`; the other two
have `β=3`. At type `(2,2)`, (2) gives

\[
                            \alpha=3\iff\beta=3.
\]

Indeed `α=3,β≤2` would force `O−I≥3`, whereas
`O≤5,I≥3`; the converse is dual. Hence the three positive
tops are the same in both directions. All three of their central
rectangles contain `(l,d)`, contradicting rectangle disjointness.
This excludes the last inventory.

All cases are now impossible, proving the analytic exclusion of
`m=8,h=17,a=9,q=0`. The
[one-small-profile proof](1485_order_forty_eight_central_seventeen_nine_one_small.md)
already excludes every `q>0` at these class sizes, using the
profile-capacity bound `q≤1`. Thus **no seventeen-top case with
nine degree-five elements exists**. Other class sizes, and the
full spectrum characterization, are not settled by this proof.
