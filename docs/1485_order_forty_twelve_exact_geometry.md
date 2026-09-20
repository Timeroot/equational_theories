# Order forty, twelve/eight: exact geometry of the final single-coset case

Research note, 20 September 2026. The necessary finite system below has
a negative diagnostic SAT result. It is retained as independent
corroboration, not as a certified finite exclusion: the smaller
[regular-hole reduction](1485_order_forty_regular_hole_fibers.md) is the
preferred route for refutation certification. It treats precisely the
both-single-coset `3333/3333` case
with degree-class sizes `(4,12,8,16)` at degrees `(4,5,8,10)` and
sharp degrees `(2^4,1^4)` on `B`. No Lean theorem is asserted.

Use the [joint-capacity notation](1485_order_forty_twelve_joint_capacities.md).
The four holes form a bijection between the four predecessor and four
successor line labels; normalize them to `(p,p)`, `p∈F₂²`.
The twelve actual `A` vertices occupy the other cells.

## 1. One common central alphabet; 288 geometry choices

Before normalizing the holes, the
[single-coset affine normalization](1485_order_forty_single_coset.md#2-affine-normalization-uses-one-common-central-alphabet)
gives actual central successor and predecessor labels

\[
C(p,q)=p+q,\qquad H(p,q)=L(p+\Omega q),
\]

where `L∈GL₂(F₂)` and `Ω` is one of the two order-three matrices.
Every permutation of four labels is affine. Write the hole bijection
as `q=Rp+t`, with `R∈GL₂(F₂)`, and use `R⁻¹(q+t)` as the
new successor-line label. This diagonalizes the holes. Translating the
**common** central alphabet by `t` gives

\[
\boxed{C(p,q)=p+Rq,\qquad
H(p,q)=L(p+\Omega Rq)+\delta,}
\tag{1}
\]

where the actual offset is `δ=LΩt+t`. Allowing every `δ∈F₂²`
only weakens the conditions. Thus all geometries are covered by
`6·2·6·4=288` choices of `(L,Ω,R,δ)`.

No independent relabeling of the two central alphabets is used.
The two central labels of each top point form a genuine four-by-four
central grid: `ΩR+R` is invertible. Every `P` and `Q` line
is transversal to both central-label directions.

## 2. Actual top profiles and pointwise marginals

Represent `U_b=TopPred(b)` and `V_b=TopSucc(b)` by actual
four-point subsets of the sixteen-point grid. Centrality makes `U_b`
a transversal of the `H` labels and `V_b` a transversal of the `C`
labels. Their intersections with the `P,Q` lines are exactly the
previous matrices `M,N`.

Every top point has ten ordinary neighbors in each direction: one
central, four top, three degree-five, and therefore exactly two
degree-eight neighbors. Consequently

\[
\#\{b:t\in U_b\}=\#\{b:t\in V_b\}=2
\quad\text{for each top }t.
\tag{2}
\]

All four medium-sharp profiles are affine transversals to the opposite
partition, by the `3333` instance of the no-two-fours argument.
Thus their `U_b` sets meet each `Q` line once and their `V_b`
sets meet each `P` line once. No affine assumption is made about
the four low-sharp profiles.

## 3. Exact good top pairs and uniqueness

A pair of top endpoints `(u,v)` lies in a hole precisely when
`p(u)=q(v)`. If `u∈U_b`, `v∈V_b`, and this holds, its middle
`b` is good precisely when `C(u)≠H(v)`. A noncentral hole has
no degree-five or central replacement. On an occupied cell, by contrast,
the corresponding `A` vertex is a lower-degree replacement.

Hence the exact good-pair formula becomes

\[
\#\{(u,v)\in U_b\times V_b:p(u)=q(v),\ C(u)\ne H(v)\}
+\sum_{x,y}D_{xb}D_{by}C_{xy}=12-3j_b.
\tag{3}
\]

No noncentral hole pair can have two different `B` middles. If a
`B×B` pair `(b,d)` has neither a sharp `A` middle (`C_bd=0`)
nor an ordinary internal middle (`(D²)_bd=0`), its only possible
middles are top vertices. It therefore has exactly one:

\[
C_{bd}=0=(D^2)_{bd}\quad\Longrightarrow\quad |V_b\cap U_d|=1.
\tag{4}
\]

For `a=(p,q)∈A`, the only possible non-top middle of `(a,b)`
is `F(a)`, and it is ordinary only if `F(a)Db`. Similarly the
only non-top middle of `(b,a)` is `G(a)`. This gives

\[
\neg D_{F(a),b}\Rightarrow |Q_q\cap U_b|=1,\qquad
\neg D_{b,G(a)}\Rightarrow |V_b\cap P_p|=1.
\tag{5}
\]

All clauses allow loops and repeated vertex labels.

## 4. Bad-extension weights on medium-incident edges

On any internal edge `bDd`, the line-return sum is `3−η(b,d)`.
If `b` is medium-sharp, its predecessor-intersection row is `1111`
or `2200` up to permutation. In the latter case the selected sum
must be two, since it is a positive even number less than four.
In the former case the selected sum is `j_d`. A low-sharp target
would give `η=2`, contradicting `η≤j_d=1`; a medium target
gives `η=1`. Thus `η=β=1` on every edge out of a medium.
The dual argument treats edges into a medium.

This is the only additional weight restriction used in this encoder.
The later analytic exclusion of zero-weight low/low edges is not an
input, so the finite result does not depend on that separate argument.

## 5. Individual four-element translation fibers

Fix `t∈U_b∩P_p`. The fiber `L_t⁻¹(b)` has size four.
It contains all `j_b` sharp `A` successors of `b`. An internal
successor `d` contributes if and only if its middle is good; its
only possible lower-degree replacement is an `a∈F⁻¹(d)` with
predecessor profile `P_p`. This is exactly the absence of color `p`
from the `F`-color set `I_d`.

The remaining fiber members are precisely the good top successors
counted in §3. Therefore

\[
\boxed{
\#\{v\in V_b:q(v)=p,\ C(t)\ne H(v)\}
+\sum_dD_{bd}[p\notin I_d]=4-j_b.}
\tag{6}
\]

For `t∈V_b∩Q_q`, the dual identity is

\[
\boxed{
\#\{u\in U_b:p(u)=q,\ C(u)\ne H(t)\}
+\sum_dD_{db}[q\notin J_d]=4-j_b.}
\tag{7}
\]

Here `J_d` is the successor-color set of `G⁻¹(d)`. These are
genuine uniform-translation-fiber counts. They do not assert uniform
fibers of a mixed two-parameter map. Since the ordinary `D` degree
is `4−j_b`, the first count in (6) also equals
`Σ_dD_bd[p∈I_d]`; in particular it is constant among the points
of `U_b∩P_p`. The corresponding column count is constant on
`V_b∩Q_q`.

## 6. Encoding, controls, and current verification status

[1485_n40_twelve_exact_geometry_cnf.py](../scripts/1485_n40_twelve_exact_geometry_cnf.py)
adds these conditions to the fully specified joint-capacity encoder.
One-hot geometry variables determine the central equality table by
exact disjunctions. Actual point bits determine the line intersections
by threshold equivalences. The good-pair counts, ordinary-middle tests,
and individual-fiber sums use exact Boolean conjunctions and cardinalities.

The controls retain the joint encoder's substantive positive necessary
system. Independently, all 288 central grids and all their line
transversalities are checked directly. The central-equality CNF is
evaluated on every one-hot geometry assignment, checking every clause
and all 256 equality entries against the direct label formula. Small
truth tables also check the partition count in (6)–(7).

The diagnostic system has **76,865 variables and 263,619 clauses**
and was reported UNSAT in **64.547 seconds**. Its deterministic
encoder passed all controls in 22.530 seconds. No refutation certificate
for this larger encoding is claimed here: certification is delegated
to the smaller regular-hole argument. This file is not an additional
proof dependency and its negative solver report is not used as a theorem.
Even an exclusion of this order-forty branch would not settle the general
square-or-double-square spectrum theorem.
