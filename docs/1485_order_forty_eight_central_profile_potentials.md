# Eight central elements: two short profile-capacity inequalities

Independently audited analytic inequalities, 20 September 2026.
These are necessary finite E1485
conditions, not a Lean formalization or an exclusion of all remaining
eight-central cases. No optimizer status is a proof premise.

Assume order forty, minimum degree four, and eight central elements.
Let `h` count tops, `a` count degree-five elements, and `q>0` count
degree-five elements with three top neighbors. The other `a−q`
have four. The [one-hole grid theorem](1485_one_hole_first_output_grid.md)
gives at most four triple central blocks in each direction.

**The inequalities are:**

\[
 \begin{array}{ll}
 a\ge8:&58h+8a+30q\le1168,\\[2pt]
 a\ge9:&118h+24a+34q\le2272.
 \end{array}                                            \tag{1}
\]

For example, at seventeen tops they give `q≤3` when `a=8`,
and `q≤1` when `a=9`. At sixteen tops they give `q≤5` when
`a=8`, and `q≤4` when `a=9`. They make no assertion about
constructing any of the remaining possibilities.

## 1. Local facts needed by both potentials

For a top write `P,C` for its two central block sizes and `α,β`
for its degree-five successor and predecessor counts. Then

\[
 1\le P,C\le3,\qquad
 \alpha\le f(C),\quad\beta\le f(P),\qquad f=(4,3,1).
\]

As in the [weighted-defect argument](1485_order_forty_eight_central_all_four.md#2-small-weighted-central-slacks),
the weights `7−2C−α` are nonnegative and sum to `12−a`
in every central row; the argument is unchanged by smaller profiles.
Thus `C=1` forces `α≥a−7`, and dually `P=1` forces
`β≥a−7`.

One more local implication is useful:

\[
                      P=1,\ C=2,\ \alpha=0
                      \quad\Longrightarrow\quad\beta\le2. \tag{2}
\]

Indeed reciprocal balance says `O−I=5−3β`. If `β≥3`,
then `I≥O+4≥7`, whereas `I+P+β≤10` gives `I≤6`.
Here `I,O≥3` follows from the central partition into blocks of
size at most three. No information about individual size-three
profiles is needed for (2).

## 2. The complete local checks

Put `J=1_(P=3)+1_(C=3)` and define

\[
 \begin{aligned}
 F={}&-58+28(P+C)-12PC+15(\alpha+\beta)
                      -8(P\alpha+C\beta)+18J,\\
 G={}&-118+56(P+C)-22PC+17(\alpha+\beta)
                      -10(P\alpha+C\beta)+12J.
 \end{aligned}
\]

The following six entries, and their duals, prove `F≥0` for
`a≥8` and `G≥0` for `a≥9`:

| `(P,C)` | `F` | `G` |
| --- | --- | --- |
| `(1,1)` | `−14+7(α+β)` | `−28+7(α+β)` |
| `(1,2)` | `2+7α−β` | `6+7α−3β` |
| `(1,3)` | `36+7α−9β` | `52+7α−13β` |
| `(2,2)` | `6−α−β` | `18−3(α+β)` |
| `(2,3)` | `28−α−9β` | `42−3α−13β` |
| `(3,3)` | `38−9(α+β)` | `44−13(α+β)` |

In the first row use `α,β≥1` or `≥2`, respectively. In the
second row, (2) handles `α=0`; for `α≥1`, use `β≤4`.
Every other entry is nonnegative directly from the support bounds.
For instance, `(2,3)` has `α≤1,β≤3` and `(3,3)` has
`α,β≤1`.

## 3. Summing the pointwise inequalities

Let `p_3,c_3` count triple blocks. The exact moments are

\[
 \sum P=\sum C=32,\quad\sum PC=64,\quad\sum1=h,
 \qquad\sum\alpha=\sum\beta=4a-q,
 \qquad\sum P\alpha=\sum C\beta=8a.
\]

Consequently

\[
 \begin{aligned}
 0\le\sum F&=1024-58h-8a-30q+18(p_3+c_3),\\
 0\le\sum G&=2176-118h-24a-34q+12(p_3+c_3).
 \end{aligned}
\]

Use `p_3+c_3≤8` from the one-hole theorem to obtain (1).
The six-row table and these exact sums are the entire proof;
no numerical linear-programming certificate is required.
