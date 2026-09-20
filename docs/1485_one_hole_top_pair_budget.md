# One-hole grids: a two-sided budget for the remaining top products

Independently audited analytic inequality, 20 September 2026. This is a necessary
finite E1485 condition, not a general spectrum proof or a Lean theorem.
No finite enumeration or numerical optimization is used.

Assume the [one-hole hypotheses](1485_one_hole_first_output_grid.md):
minimum degree `r=t+1`, central count `m=t²−1`, `t≥3`, and a
first degree-`r+1` top output with profile size `t`. Let `h` count
tops, `a` count degree-`r+1` elements, and `b` count those with
the smaller profile size `t`. Write `p,q` for the numbers of maximal
predecessor and successor central blocks. Thus `p,q≤2t−2`.

Define

\[
 \begin{aligned}
 F&=h^2-m(t+1)^2-t(t+1)a+2tb,\\
 W&=m\big((t+1)h-(t+1)m-ta+b\big).
 \end{aligned}
\]

**Theorem.**

\[
 \boxed{F\ge0,\qquad F\le W\le tF,
                \qquad 2W\le(2t-1)F+pq.}              \tag{1}
\]

In particular one may replace `pq` in the last bound by `4(t−1)²`.
There is no hypothesis on the total order, the other occurring degrees,
or the number of higher-degree classes.

## 1. What the two counts measure

Let `S` be the set of ordered top pairs whose product is neither
central nor of degree `r+1`. A central element has exactly `r²`
top representations. A degree-`r+1` element has `t(t−1)` or
`t(t+1)` according as its profile size is `t` or `t+1`, by the
[least-degree fiber count](1485_unrestricted_central_incidence.md#the-least-noncentral-degree-has-balanced-sharp-counts).
Subtracting these disjoint sets of representations from `h²` proves

\[
                                  |S|=F.
\]

Fix a central parameter `z`. Its regular auxiliary relation has
`r h` edges starting in the top class. Exactly `r m` of these end
centrally: they are all the ordinary sharp edges from tops to central
elements. Exactly `ta−b` end in the degree-`r+1` class: each
element's `r` auxiliary predecessors split into its one or two sharp
non-top predecessors and, respectively, `t` or `t−1` tops.

Summing the remaining auxiliary edges over the `m` parameters gives
the stated value of `W`. The exact auxiliary-membership identity
counts each pair `(u,v)∈S` with weight `|C_v|`: its product appears
in the auxiliary row of `u` precisely at the central labels of that
input block, with no repetition inside a parameter. Dually the same
count weights that pair by `|P_u|`. The two values agree because the
sharp counts in the first-degree class are balanced. Hence

\[
                     W=\sum_{(u,v)\in S}|C_v|
                      =\sum_{(u,v)\in S}|P_u|.          \tag{2}
\]

Since all these block sizes lie in `[1,t]`, (2) proves
`F≤W≤tF`.

## 2. The maximal-block rectangle contains almost all near-maximal weight

There are only `pq` ordered pairs whose first predecessor block and
second successor block are both maximal. Every other pair in `S`
has positive integer defect

\[
                         (t-|P_u|)+(t-|C_v|)\ge1.
\]

By (2) the total defect is `2tF−2W`. Therefore

\[
                        F\le pq+(2tF-2W),
\]

which rearranges to the final inequality in (1).

## 3. An eight-central consequence without a total-order assumption

Take `t=3,m=8,h=15,a=8,b=3`. Then `F=19,W=56`, while
`pq≤16`. The last inequality in (1) would give

\[
                              112\le5\cdot19+16=111.
\]

Thus this central/top/degree-five split is impossible. In particular,
at order forty, fifteen tops and eight degree-five elements now require
at least four three-profiles: sharp coverage and `W≤3F` already
require at least three, and the new bound excludes equality.
