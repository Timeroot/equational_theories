# Eight central elements when all degree-five profiles have size four

Research reduction, 20 September 2026. These are analytic necessary
conditions, not a complete exclusion of the eight-central case and not
Lean declarations. No search, SAT result, or optimization certificate is
used in the arguments below.

Assume order forty, minimum degree four, eight central elements, and
that **every degree-five element has four top predecessors and four
top successors**. Write `Z,T,A,B` for the degree classes `4,10,5,8`,
and put `h=|T|`, `a=|A|`, `b=|B|`. Thus `a+b=32−h`.

The reduction in this note gives the class-size possibilities

\[
\boxed{(h,a,b)=(17,8,7),\ (17,9,6),\ (18,7,7),\ (18,8,6).}
\tag{1}
\]

Only the third row automatically has balanced top and sharp counts
at every member of `B`. Section 3 explicitly describes the possible
imbalances in the other rows; they must not silently be excluded.

Subsequent proofs exclude the
[second](1485_order_forty_eight_central_seventeen_nine_all_four.md) and
[fourth](1485_order_forty_eight_central_eighteen_all_four.md) splits.
The current all-four frontier is therefore `(17,8,7)` or `(18,7,7)`.

## 1. Reducing the top count and degree-class sizes

The [full-block exclusion](1485_order_forty_ten_central_full_blocks.md)
gives `1≤|P_u|,|C_u|≤3` at every top. Central shadows therefore
give at least three top neighbors in both directions at every vertex.
Every member of `A` has exactly one sharp neighbor in `B` in each
direction, while each member of `B` has at least one in `A`.
Consequently `a≥b`.

The [variable-top-count inequalities](1485_order_forty_variable_top_counts.md#2-three-top-neighbors-suffice-for-a-useful-bound)
give

\[
 h^2\ge128+7a+10b=448-10h-3a,
 \qquad12a\le h^2-128,
 \qquad h^2+8h\ge384.                                  \tag{2}
\]

The last inequality gives `h≥16`. At `h=16`, the first would
require `a≥11`, whereas the second requires `a≤10`.
Thus `h≥17`. In particular no all-size-four case at sixteen tops
needs a separate graph argument, even when `a=10`.

For a top `u`, abbreviate `P=|P_u|`, `C=|C_u|`, and let `α`
count its successors in `A`. The
[auxiliary support bound](1485_order_forty_eight_central_high_five.md#1-central-parameter-capacity-excludes-twelve-degree-five-elements)
gives

\[
 \alpha\le f(C),\qquad(f(1),f(2),f(3))=(4,3,1).
\]

Let `q` count the tops with `C=3`, and put `X=Σ_(C=1)P`.
The central moments and exact size-four profile counts imply

\[
 \sum P=\sum C=32,\quad \sum PC=64,\quad
 \sum\alpha=4a,\quad \sum P\alpha=8a.
\]

The singleton-`C` margin is `2h−32+q`, so `X≥2h−32+q`.
Since `f(C)=7−2C−1_(C=1)`,

\[
 \sum f(C)=5h-32-q,\qquad \sum Pf(C)=96-X.
\]

Therefore

\[
 \begin{aligned}
 4a&=\sum(P-1)\alpha\\
   &\le\sum(P-1)f(C)
    =128-5h+q-X\le160-7h.                              \tag{3}
 \end{aligned}
\]

Together with `a≥(32−h)/2`, this gives `5h≤96`, hence `h≤19`.
At `h=19`, sharp coverage requires `a≥7`, while (3) gives
`a≤6`. Thus `h=17` or `18`.

At seventeen tops, these bounds give `8≤a≤10`; at eighteen
tops they give `7≤a≤8`. The
[ten-degree-five-element argument](1485_order_forty_eight_central_ten_five.md#2-seventeen-tops-are-impossible)
already excludes `h=17,a=10`, even when some degree-five profiles
have size three. This proves (1).

## 2. Small weighted central slacks

For a top define

\[
                 v_u=7-2|C_u|-\alpha_u.
\]

The support bounds give `v_u≥0`, and `v_u≥1` whenever `C_u`
is a singleton. Every central row contains four tops, its `C`
blocks sum to eight, and its `α` values sum to `a`. Thus

\[
 \sum_{u\in Row(z)}v_u=12-a,\qquad0\le v_u\le12-a.
\]

Summing unweighted and with central predecessor weights gives

\[
 L:=\sum v_u=7h-64-4a,\qquad
 \sum|P_u|v_u=8(12-a),
\]

and hence the exact nonnegative defect

\[
 \boxed{\sum(|P_u|-1)v_u=160-7h-4a.}                   \tag{4}
\]

The opposite-magma weights satisfy the dual identity. If `n_pc`
counts tops with block sizes `(p,c)`, this in particular gives

\[
 n_{21}+2n_{31}\le160-7h-4a,\qquad
 n_{12}+2n_{13}\le160-7h-4a.                            \tag{5}
\]

The exact values are:

| `(h,a,b)` | Per-row `v` sum | Total `L` | Defect in (4) |
| --- | ---: | ---: | ---: |
| `(17,8,7)` | 4 | 23 | 9 |
| `(17,9,6)` | 3 | 19 | 5 |
| `(18,7,7)` | 5 | 34 | 6 |
| `(18,8,6)` | 4 | 30 | 2 |

At a singleton `C` block, the same pointwise bound says
`α≥a−7`; its dual applies to singleton `P` blocks. These are
necessary restrictions only. In particular the last row's very small
defect does not by itself exclude that row.

## 3. Precisely when degree-eight counts can be unbalanced

For `x∈B`, let `I,O` be its top predecessor and successor counts,
and let `j^-,j^+` be its sharp predecessor and successor counts in
`A`. We have

\[
 I,O\ge3,\quad j^-,j^+\ge1,\quad
 I+j^-\le8,\quad O+j^+\le8,
 \qquad O-I=3(j^+-j^-).                                \tag{6}
\]

The top counts lie between three and seven. If they differ, their
difference is therefore exactly three in absolute value. Suppose
`O>I`. Then `j^+=j^-+1≥2`, so `O≤6`. It follows that
`I=3,O=6,j^-=1,j^+=2`. The other possibility is its dual.
Thus the only unbalanced types are

\[
 (I,O;j^-,j^+)=(3,6;1,2),\qquad(6,3;2,1).             \tag{7}
\]

Their internal `B` indegree/outdegree pairs are respectively `(4,0)`
and `(0,4)`. These two types occur equally often, since the global
sharp sums in both directions equal `a`.

All other vertices have balanced counts

\[
 I=O=t,\qquad j^-=j^+=j,\qquad3\le t\le7,
 \quad1\le j\le8-t,
\]

and internal indegree/outdegree `8−t−j`.
If each unbalanced type occurs `s` times, their contributions to
either sharp sum give the exact identity

\[
             a-b=s+\sum_{\text{balanced }x}(j_x-1).     \tag{8}
\]

In particular `s≤a−b` and `2s≤b`. For `(h,a,b)=(18,7,7)`,
(8) forces `s=0` and `j_x=1` at every `B` vertex. Its sharp
endpoint matrix is therefore a permutation, and its ordinary internal
adjacency has balanced degrees `d_x=7−t_x`. For the other three
rows, assuming such a permutation matrix without further proof would
discard the possibilities in (7) or higher sharp degrees.

No disjointness of singleton central-label sets is used here: the
earlier separation theorem at least noncentral top-output degree
`2r−1` does not apply to the present least degree-five output.
