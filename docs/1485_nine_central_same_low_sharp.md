# Nine central elements and sixteen tops: the same sharp degree-five output

Research note, 20 September 2026. This is a small, exhaustively checked
finite incidence lemma, not a purely analytic proof or a Lean theorem.
The reduction is mathematical; the final check ranges over nine cases
of sixteen Boolean entries, without SAT/SMT or floating-point arithmetic.
Accepted partial incidence fixtures are **not** claimed to be magmas.

Use the final configuration in
[the degree-count note](1485_nine_central_sixteen_degree_counts.md#13-central-pair-capacity-locates-the-exceptional-sharp-degree):
there are nine central elements, sixteen tops, seven degree-five
vertices `A`, and eight degree-eight vertices `B`. Exactly two
vertices of `A` have three top neighbors (`A3`); the other five
form `A4`. The two four-element subsets `L,H⊂B` have respectively
three and five top neighbors. The unique sharp-degree-two vertex
belongs to `L`, and all other sharp degrees equal one.

Let `D` be ordinary adjacency on `B`, and let `Q_xz=1` record
the unique sharp path `x⇒a⇒z` through `a∈A`.
Write `τ_L` for the number of bad internal two-edge paths whose
middle lies in `L`. The analytic central-pair budget already proves

\[
                              \tau_L\ge25.              \tag{1}
\]

We exclude the case in which the remaining sharp `A4` source and
target incidences at `L` belong to the **same** vertex of `A4`.
The complementary case is handled separately in
[the full sixteen-top exclusion](1485_nine_central_sixteen_exclusion.md).

## 1. Complete normalization: nine sharp tables

Each of the two `A3` vertices gives a two-by-two rectangle in
`L×L`. These rectangles are disjoint: otherwise a pair would have
two different products. Their row pairs, or their column pairs,
must consequently be disjoint. Taking the opposite operation if
necessary, assume the row pairs are disjoint. Label the exceptional
vertex `0`, its mate in the first pair `1`, and the other pair
`2,3`. The `A3` row pairs are now `{0,1}` and `{2,3}`.

Let `V1,V2` be the corresponding two-element column pairs.
The column sharp degrees are `(2,1,1,1)`. Removing the two
`A3` incidences leaves exactly one `A4` column incidence, at
some `m`. Similarly the unique remaining `A4` row incidence is
at `0`. In the present case the same `A4` vertex supplies both,
so `Q_L` is the two `A3` rectangles plus the single cell `(0,m)`.
That cell cannot already lie in an `A3` rectangle.

The column pairs either partition the four labels or overlap only
at `0`. In the first case `m=0`, and `0∉V1` is necessary,
giving three possibilities. In the second case
`V1={0,a},V2={0,b}` with distinct `a,b∈{1,2,3}`; the omitted
label is `m`, giving six possibilities. These are all nine cases.

No `Q` cell joins `L` and `H` in this case. Each `A3` has
both sharp sides in `L`; the designated `A4` uses up the remaining
sharp incidence in each direction at `L`.

## 2. Sixteen-bit necessary conditions and the exact objective

Let `F=D|_{L×L}`. The internal `D` degrees on `L` are
`(3,4,4,4)`, since a vertex of degree eight has three top neighbors
and respectively two or one sharp neighbors in `A`.
The four vertices of `H` each have internal degree two.
Therefore the number of `L→H` edges is
`ℓ=15−|F|≤8`. In particular `|F|≥7`, and row and column
zero of `F` each have at most three entries.

Every repeated internal two-step path forces a sharp replacement.
Consequently

\[
             (F^2)_{xy}\ge2\quad\Longrightarrow\quad (Q_L)_{xy}=1.
                                                               \tag{2}
\]

For an internal edge `xFy`, all top neighbors of both endpoints
have triple central blocks. The weighted auxiliary-fiber identity
therefore equates its bad predecessor and bad extension counts:

\[
 \eta(x,y)=\#\{z:zFx,\ (Q_L)_{zy}=1\}
 =\#\{z:yFz,\ (Q_L)_{xz}=1\}=\beta(x,y)\le3.              \tag{3}
\]

There are no omitted terms from `H` in (3), because `Q` has
no cross-class cells. The bound three follows because `η` counts
top members of the corresponding fiber, contained in the three top
predecessors of `x`.

Every `L→H` edge has exactly one bad predecessor, by the analytic
cross-edge restriction in degree-count §13: its high endpoint has
sharp degree one and all sharp neighbors there belong to `A4`.
Thus the objective is exactly

\[
 \tau_L=\sum_{xFy}\eta(x,y)+15-|F|
       =\sum_{(Q_L)_{xz}=1}(F^2)_{xz}+15-|F|.             \tag{4}
\]

Equations (2)–(4), the nine sharp tables, and the elementary degree
bounds are all necessary for a hypothetical magma. They are not
asserted sufficient to construct one.

## 3. Exact exhaustive check and controls

The checker is
[1485_nine_central_same_low_sharp.py](../scripts/1485_nine_central_same_low_sharp.py).
It generates the nine tables from the sharp-degree deficits and scans
all `2^16` binary matrices `F` for each. It tests the displayed
necessary conditions with exact integer and bit-set arithmetic,
then asserts `τ_L<25` on every survivor. It refuses `python -O`,
which would disable these assertions.

| `V1` | `V2` | `m` | Accepted partial fixtures | Maximum `|F|` | Maximum `τ_L` |
| --- | --- | ---: | ---: | ---: | ---: |
| `01` | `02` | 3 | 16 | 8 | 20 |
| `01` | `03` | 2 | 16 | 8 | 20 |
| `02` | `01` | 3 | 5 | 7 | 18 |
| `02` | `03` | 1 | 10 | 8 | 19 |
| `03` | `01` | 2 | 5 | 7 | 18 |
| `03` | `02` | 1 | 10 | 8 | 19 |
| `12` | `03` | 0 | 35 | 8 | 18 |
| `13` | `02` | 0 | 35 | 8 | 18 |
| `23` | `01` | 0 | 20 | 8 | 17 |

Every normalized case has surviving partial data, so the necessary
conditions are not accidentally always false. The explicit row-mask
fixture `Q_L=(7,3,9,9), F=(7,3,12,1)` attains `τ_L=20`.
An independent implementation using literal sets and triples checks
that fixture and deterministically selected accepted and rejected masks.
The all-ones matrix is an explicit rejected control.

The run

```sh
python3 scripts/1485_nine_central_same_low_sharp.py --reference-audit 256
```

checked **589,824 masks**, with **152 accepted partial incidences**,
and found the exact maximum **20**, in **8.053 seconds**. The
reference formulation agreed on all audited masks. This contradicts
(1), excluding the same-`A4` case. The displayed maxima are checked
finite conclusions, not claimed to follow from an unprovided analytic
argument.
