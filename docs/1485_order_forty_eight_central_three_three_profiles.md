# Sixteen tops and ten degree-five elements cannot have three three-profiles

Independently audited analytic proof, 20 September 2026. No SAT,
finite graph enumeration, or Lean theorem is used.

**Theorem.** An order-forty E1485 magma with minimum degree four,
eight central elements, sixteen tops, and ten degree-five elements
cannot have exactly three degree-five elements of top-profile size three.

Write `P,C` for a top's central predecessor and successor block sizes,
and `α,β` for its degree-five successor and predecessor counts.
Write `n_ij` for the number of tops with `(P,C)=(i,j)` and `p,c`
for the numbers with `P=3,C=3`, respectively.

## 1. There are only three possible numbers of double-double blocks

The [one-hole bound](1485_one_hole_first_output_grid.md) gives `p,c≤4`.
The [ten-degree-five local intervals](1485_order_forty_eight_central_ten_five_profile_bound.md#1-the-local-incidence-intervals)
are `α∈{3,4},{1,2,3},{0,1}` according as `C=1,2,3`, and dually
for `β` and `P`.

The nonnegative integer slack in that note's pointwise inequality is

\[
 D=-3PC+8(P+C)-19-(P-2)\alpha-(C-2)\beta
                        -\mathbf1_{P=C=2}.
\]

Here its total is

\[
                         \sum D=4-n_{22}.              \tag{1}
\]

Put `x=n13+n31`. The central moments give

\[
 n_{11}+n_{33}=x,\qquad
 n_{22}=16-2(p+c)+2x.                                 \tag{2}
\]

Indeed the numbers of singleton and triple blocks agree in each
direction, and `Σ(P−2)(C−2)=0`. Thus

\[
                         n_{22}\in\{0,2,4\}.           \tag{3}
\]

We will also use the following complete local comparison table.
The baseline entries `(α₀,β₀)` are chosen so that

\[
                         \alpha-\alpha_0\le D,
                         \qquad\beta-\beta_0\le D.     \tag{4}
\]

| `(P,C)` | `D` | Baseline `(α₀,β₀)` |
| --- | --- | --- |
| `11` | `α+β−6` | `(3,3)` |
| `12` | `α−1` | `(1,3)` |
| `13` | `4+α−β` | `(0,4)` |
| `21` | `β−1` | `(3,1)` |
| `22` | `0` | `(3,3)` |
| `23` | `3−β` | `(1,3)` |
| `31` | `4+β−α` | `(4,0)` |
| `32` | `3−α` | `(3,1)` |
| `33` | `2−α−β` | `(1,1)` |

Only the `12,21` comparisons need more than the intervals. At `12`,
`β=4` forces `α≥2`: otherwise reciprocal balance
`O−I=5(C−P)+3(α−β)` and `I+P+β≤10`, with `O≥3`,
are inconsistent. The dual implication is `21,α=4⇒β≥2`.
These prove (4). When `D=0`, every non-`22` entry is exactly its
baseline; the same reciprocal argument handles the apparently free
coordinates at `12,21,23,32`.

## 2. Four double-double blocks leave too few triple-profile labels

Suppose `n22=4`. Every slack vanishes. A type-`31` top has
`(α,β)=(4,0)`, so reciprocal balance and the degree bound give
`I=3,O=5` and no ordinary degree-eight successor. Its top-input row
has no top-valued output, by the
[small-block return theorem](1485_top_return_small_blocks.md).
If `γ` counts its three-profile successors, the row equation is

\[
                         16=4+3\cdot4-\gamma.
\]

Hence `γ=0`. Dually, no type-`13` top succeeds a three-profile element.
The pools of eligible triple-block predecessors and successors of the
three three-profile elements therefore have sizes

\[
              p-n_{31},\qquad c-n_{13},
              \qquad (p-n_{31})+(c-n_{13})=6,           \tag{5}
\]

where the last equality is (2).

Two distinct degree-five profiles sharing two top predecessors have
disjoint top-successor sets: a shared successor and those two
predecessors would form two central entries in one column of a matching,
or give two distinct good middles for a noncentral pair. The dual
statement also holds.

Each pool in (5) must have at least three members. Otherwise all three
three-profiles share their same pair of triple predecessors (or
successors), requiring three disjoint pairs in the opposite pool,
which has size at most four. Both pools thus have size exactly three.
Their three predecessor pairs cannot all differ, since then all three
triple blocks would be pairwise disjoint, requiring nine central labels.
A repeated pair, however, requires two disjoint pairs in the opposite
three-member pool. This is again impossible.

## 3. Zero double-double blocks violate the incidence sum

If `n22=0`, (2) and `p,c≤4` force `p=c=4,x=0`. The only
block types are four each of `12,21,23,32`.
Their baseline `α` sum is 32. By (4) and `ΣD=4`,

\[
                         \sum\alpha\le36.
\]

But the exact degree-five incidence sum is `4a−q=37`. Contradiction.

## 4. Two double-double blocks force one small explicit incidence table

Now `n22=2`, so `ΣD=2` and `p+c-x=7`. Thus `x=0` or `1`.

If `x=0`, then `n11=n33=0,p+c=7`. The non-`22` types have
baseline `α` sum `4(p+c)=28`, and the two `22` baselines add six.
Equation (4) gives `Σα≤36`, again impossible.

If `x=1`, then `p=c=4` and `n11+n33=1`. By duality assume
`n13=1,n31=0`. There are just two possible count inventories:

| `n11,n33` | `n12` | `n13` | `n21` | `n23` | `n32` | `n22` | Baseline `Σα` |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `0,1` | 3 | 1 | 4 | 2 | 3 | 2 | 33 |
| `1,0` | 2 | 1 | 3 | 3 | 4 | 2 | 35 |

The first has `Σα≤35` and is impossible. In the second, both
baseline sums `Σα₀,Σβ₀` equal 35. Their actual sums are 37,
so equality holds pointwise in both comparisons (4).

Inspection of the local table shows that a nonzero slack can then
occur only at `12` with `(α,β)=(2,4)`, or at `21` with
`(α,β)=(4,2)`; in both cases `D=1`. Every other top has its
baseline, including both `22` tops at `(3,3)`.
The baseline weighted sum `ΣPα₀` is 77. If `r,s` count these
special `12,21` tops, the exact weighted sum 80 gives
`r+s=2,r+2s=3`. Hence `r=s=1`.

The entire incidence table is therefore:

| Type and incidences | Number |
| --- | ---: |
| `11:(3,3)` | 1 |
| `12:(1,3)` | 1 |
| `12:(2,4)` | 1 |
| `13:(0,4)` | 1 |
| `21:(3,1)` | 2 |
| `21:(4,2)` | 1 |
| `23:(1,3)` | 3 |
| `32:(3,1)` | 4 |
| `22:(3,3)` | 2 |

## 5. Three distinguished rectangles necessarily overlap

Call the unique tops `13:(0,4)`, `12:(2,4)`, `21:(4,2)`
respectively `A,B,C`. These are top names, not degree-class names.
Every central row has four blocks partitioning eight labels and its
four `α` values sum to ten.

No central row has pattern `3311`: its triple tops have `α≤1`,
and reaching ten would require two singleton-successor tops with
`α=4`, whereas `C` is the only such top. The row through `A`
therefore has pattern `3221`. Because `α_A=0`, it must contain
`C`, the unique singleton-successor top with `α=4`.

The row through `B` cannot have pattern `2222`, because `α_B=2`
is even and all other size-two successor tops have odd `α`.
Thus it too is `3221`, and it must contain `C`: otherwise its
`α` sum is at most `2+3+1+3=9`.
The singleton sets `P_A,P_B` differ, since one row containing both
would have `α` sum at most `0+2+4+3=9`. Hence

\[
                              P_C=P_A\cup P_B.         \tag{6}
\]

Now consider a central column with label in `C_A\setminus C_B`.
It contains `A` but not `B`. A `3311` predecessor partition could
not reach total `β=10`: its two triple tops have `β=1`, and
besides `A` the only singleton-predecessor top with `β=4` is `B`.
Thus its partition is `3221`. The singleton is `A`, the triple
has `β=1`, and its two doubles must have `β` values two and three.
The unique double-predecessor top with `β=2` is `C`. Therefore

\[
                         C_A\setminus C_B\subseteq C_C.
\]

Since `|C_A|=3,|C_B|=2,|C_C|=1`, this implies `C_C⊆C_A`.
Together with (6), the rectangles `P_A×C_A` and `P_C×C_C`
intersect. This contradicts uniqueness of the top middle between
central endpoints. The final case is impossible, proving the theorem.
