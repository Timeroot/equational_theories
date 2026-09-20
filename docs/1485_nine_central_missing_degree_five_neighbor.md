# Nine central elements force a missing degree-five neighborhood

Research theorem, 20 September 2026. This is an independently audited
analytic obstruction in the remaining order-forty nine-central case.
It does not depend on a linear-programming infeasibility claim, a SAT
result, or graph enumeration. It is not yet a Lean theorem.

Use the [remaining degree split](1485_order_forty_nine_central_reduction.md):
there are nine central elements, seventeen tops, seven degree-five
elements `A`, and seven degree-eight elements `B`. Every `A` element
has four top neighbors in each direction. For a top `u`, put

\[
 P=|P_u|,\quad C=|C_u|,\quad
 \alpha=|Row(u)\cap A|,\quad \beta=|Col(u)\cap A|.
\]

## 1. Some top has no degree-five neighbors in one direction

**Theorem.** Some top has `α=0` or `β=0`.

Suppose instead that both counts are positive at every top. The
established auxiliary capacities are

\[
 1\le\alpha\le f(C),\qquad1\le\beta\le f(P),
 \qquad (f(1),f(2),f(3))=(4,3,1).
\]

Also `C=1` forces `α≥2`: a central row containing this top has
block pattern `3321`, and the other three tops have total `A`
capacity at most five, whereas that row must cover all seven elements
of `A`. Dually `P=1` forces `β≥2`.

Consider the following integer-valued expression at each top:

\[
 F=-59+21(P+C)-7PC+10(\alpha+\beta)-4(P\alpha+C\beta).
\tag{1}
\]

It is nonnegative. Here is the entire local verification; the other
three block types follow by interchanging `P,C` and `α,β`.

| `(P,C)` | Expression for `F` | Lower bound |
| --- | --- | ---: |
| `(1,1)` | `6(α+β)−24` | 0 |
| `(1,2)` | `6α+2β−10` | 0 |
| `(1,3)` | `4+6α−2β` | 2 |
| `(2,2)` | `2(α+β)−3` | 1 |
| `(2,3)` | `4+2α−2β` | 0 |
| `(3,3)` | `4−2(α+β)` | 0 |

But the exact central and degree-five incidence moments are

\[
 \sum1=17,\quad\sum(P+C)=72,\quad\sum PC=81,
 \quad\sum(\alpha+\beta)=56,
 \quad\sum(P\alpha+C\beta)=126.
\]

Summing (1) therefore gives

\[
 \sum F=-59\cdot17+21\cdot72-7\cdot81+10\cdot56-4\cdot126
       =-2,
\]

contradicting nonnegativity. This proves the theorem. The coefficients
were found with an exploratory linear program, but the displayed
six-row arithmetic check and exact moments are the whole proof.

## 2. A small number of top-valued top products cannot concentrate in one row

This auxiliary observation holds in any finite nonconstant-degree
E1485 model. Let `N>0` count products `u*v=t` with all three vertices
top. The sets of first inputs, second inputs, and outputs of these
products coincide; call this common set `S`.

Indeed for every such product, choose central `c∈P_u` and `d∈C_v`.
The return identities give

\[
                    t*(v*c)=v,\qquad(d*u)*t=u.
\]

All displayed factors are top. These identities prove all the claimed
set inclusions, in both directions. A row containing `j` top-valued
top products has `j` distinct second inputs, hence `|S|≥j`. Every
other vertex of `S` also has a nonempty such row. Consequently

\[
                         N\ge2j-1.                       \tag{2}
\]

The same bound holds for each column. In particular if `N≤6`, each
row and column contains at most three of these products. The statement
is trivial for `N=0` as well.

## 3. A missing neighborhood must occur at a size-two block

**Lemma.** Some top has `C=2,α=0` or, dually, `P=2,β=0`.

We use the already proved [internal graph bounds](1485_order_forty_nine_central_nonuniform_B.md):
`1≤d_b≤4` and `t_b=7−d_b≤6`. For a top with `α=0`,
every internal extension `u→b→y`, `b,y∈B`, is good. A smaller
replacement would have to lie in `A`, requiring an `A` successor of
`u`; a central replacement cannot precede a degree-eight element.

The four-element fiber `L_u⁻¹(b)` therefore contains the one sharp
`A` successor of `b` and all its `d_b=7−t_b` internal successors.
Its number of top inputs is exactly `t_b−4≤2`. A negative value
already rules out that ordinary edge. If `N_u` counts the top-valued
top products in this row, partitioning the seventeen top inputs gives

\[
 17=4C+\sum_{b\in Row(u)\cap B}(t_b-4)+N_u.              \tag{3}
\]

### Block type `(1,3)` cannot have `α=0`

First suppose any top has `C=3,α=0`. Fix a central `c`.
Exactly three of the four tops `v∈Col(c)` have central product `u*v`.
The fourth has noncentral product. It cannot belong to `A`, since
`α=0`, or be top, by [small-block confinement](1485_top_return_small_blocks.md).
Thus its degree is eight.

Put `t=c*u`, and write `v=z*c`. E1485 gives `t*(u*v)=u`.
Both `t,u` are top, so the
[central-block packing bound](1485_refined_top_product_packing.md#1-pack-an-entire-central-predecessor-block)
gives `8≤16−3|P_t|`, hence `|P_t|≤2`. The values `c*u`
range over every top predecessor of `u`, whose `P` blocks partition
the nine central elements. Therefore its top predecessor count is

\[
                              I_u\ge5.                  \tag{4}
\]

Now additionally suppose `P=1`. The singleton bound gives `2≤β≤4`.
Reciprocal balance and ordinary degree bounds give

\[
 O-I=10-3\beta,\qquad O\le7,\qquad I+1+\beta\le10.
\]

If `β=2`, (4) forces `O≥9`, impossible. If `β=3`, it forces
`O≥6`, leaving at most one `B` successor. But (3) requires five
noncentral top inputs, whereas that single output has at most two.

If `β=4`, the bounds force `I=5,O=3`. There are no ordinary
`B` predecessors, since `10−P−β−I=0`. In the **column** of `u`,
central outputs account for `4P=4` top inputs and degree-five outputs
for `3β=12`. There are no `B` outputs, and no top outputs:
small-block confinement excludes `u` as a second input too, since its
`C` block has size three. This would give `17=4+12`, a contradiction.

Thus type `(1,3)` has `α=1`. Dually type `(3,1)` has `β=1`.

### The potential forces the stated size-two zero

Suppose the lemma were false. The singleton bounds already forbid
`α=0` when `C=1` or `β=0` when `P=1`. By assumption any
zero therefore occurs only at `C=3` or `P=3`. The preceding
argument leaves only types `(2,3),(3,2),(3,3)` to check in (1).

At `(2,3)` with `α=0`, reciprocal balance gives `O−I=5−3β`.
The possibility `β=3` would give `I=O+4≥7`, contradicting
`I+P+β≤10`. Hence `β≤2` and `F=4−2β≥0`. Type `(3,2)`
is dual. At `(3,3)` both counts lie in `{0,1}`, so
`F=4−2(α+β)≥0`. All positive-count cases were checked in §1.

Once again `F≥0` everywhere but `ΣF=−2`. This proves the lemma.

## 4. The central gap forces nineteen or twenty internal edges

**Theorem.** Every remaining nine-central candidate satisfies

\[
 K\in\{19,20\},\qquad d_b\ge2\text{ for all }b,\qquad\tau\ge19.
 \tag{5}
\]

In particular `τ=K` at nineteen edges, and `τ=K` or `K−1` at
twenty edges. This theorem is analytic and uses no finite graph check.

After dualizing if necessary, use §3 to choose a top with `C=2,α=0`.
Let `n_i` count internal degree-`i` vertices. Put

\[
 L=\sum_b\max(t_b-4,0)=21-K+n_4.
\]

By (3) this row has at least `j≥9−L` top-valued top products.
The common-support bound (2) gives `N≥17−2L`. If `9−L≤0`,
this conclusion follows directly from `N≥0`, so no positive-count
assumption is being suppressed.

The exact [top-pair budget](1485_order_forty_nine_central_nonuniform_B.md)
and `τ≤K` give

\[
 N=-86+7K-\sum_b d_b^2+\tau
 \le-86+8K-\sum_b d_b^2.
\]

Consequently

\[
                  6K-\sum_b d_b^2+2n_4\ge61.
\]

Its left side is

\[
 5n_1+8n_2+9n_3+10n_4
 =63-(4n_1+n_2-n_4).
\]

Since `4n_1+n_2−n_4=21−K+2n_1`, this yields

\[
                              K\ge19+2n_1.
\]

The previously established `K≤20` forces `K=19` or `20` and
`n_1=0`. Writing `q=n_4`, the degree counts now give

\[
 n_2=21-K+q,\qquad n_3=K-14-2q,\qquad
 \sum_b d_b^2=5K-42+2q.
\]

Thus

\[
 N=2K-44-2q+\tau
 \ge17-2L=2K-25-2q,
\]

which forces `τ≥19` and proves (5). Here `q=0,1,2` at nineteen
edges and `q=0,1,2,3` at twenty.

## 5. Scope and the completed exclusion

This analytic argument excludes all edge counts at most eighteen,
without using the separate fifteen-edge or sixteen-edge finite checks.
Those are independent corroboration, not mathematical dependencies.

The remaining `τ=K` branch is excluded by the
[whole-orbit lemma](1485_order_forty_nine_central_dense_closed_orbits.md).
The case `K=20,τ=19` is excluded by the
[single-defect lemma](1485_order_forty_nine_central_twenty_one_defect.md).
Together these finish the [nine-central case](1485_order_forty_nine_central_exclusion.md).
Other central counts at order forty and the full spectrum conjecture
are not settled by this theorem.
