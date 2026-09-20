# Eighteen tops force at least six units of degree-eight excess

Research lemma, 20 September 2026. This is an analytic necessary
condition, not an exclusion of the eighteen-top branch and not a Lean
theorem. No finite search or solver premise is used.

Assume an order-forty E1485 magma has minimum degree four, ten central
elements, and eighteen tops. Every top's central predecessor and
successor blocks have sizes `p,c∈{1,2,3}`. Its top successor and
predecessor counts are `4+δ^+`, `4+δ^-`, with `δ^±∈{0,1,2}`.
Write

\[
L=\sum_T δ^+=\sum_T δ^-,\qquad
E=\sum_{x:\ d(x)=8} (|TopSucc(x)|-4).
\]

**Theorem.** `L≤14`, and consequently `E≥6`.

## 1. The identities and an initial bound

The central incidence equations and the central row/column equations
give

\[
\sum_T p=\sum_T c=40,\quad \sum_Tpc=100,
\quad \sum_Tpδ^+=\sum_Tcδ^-=20.
\tag{1}
\]

More precisely, at every central label the sum of `δ^+` over
the tops whose `P`-block contains it is two. The dual statement
holds for the `C`-blocks and `δ^-`. In particular, the blocks
with bit value one cover each label either zero or two times;
those with value two are disjoint from this covering and from
one another.

Reciprocal-neighbor balance, writing `A^±` for degree-five neighbor
counts at a top, gives

\[
δ^+-δ^-=5(c-p)+3(A^+-A^-),
\quad\text{hence}\quad δ^+-δ^-\equiv2(c-p)\pmod3.
\tag{2}
\]

Counting all edges ending in the top class gives `E+L=20`.
Also

\[
3L-20=\sum_T(3-p)δ^+\le2\sum_T(3-p)=28,
\]

so `L≤16`. We exclude sixteen and fifteen separately.

## 2. Equality at sixteen is impossible

If `L=16`, equality above forces `δ^+=2` whenever `p<3`.
Dually `δ^-=2` whenever `c<3`. Congruence (2) therefore
forbids types `(p,c)=(1,2),(2,1)` and forces the following bits:

| Block type | `(δ^+,δ^-)` |
| --- | --- |
| `(1,1)` or `(2,2)` | `(2,2)` |
| `(1,3)` | `(2,1)` |
| `(3,1)` | `(1,2)` |
| `(2,3)` | `(2,0)` |
| `(3,2)` | `(0,2)` |

For type `(3,3)` the bits are equal. Equality of total bits and
of the `P,C` degree sums forces `n13=n31=:v` and `n23=n32=:w`:
their differences satisfy `x+2y=0` and `2x+y=0`.
Put `a0=n11`, `b0=n22`. The defect moments from (1) give

\[
4a_0+b_0=22,\qquad 2a_0+b_0+2v+w=14.
\]

Thus `a0` is four or five. If it is four, then `b0=6` and
`v=w=0`; the `(1,1),(2,2)` tops alone contribute twenty to
`L`. If it is five, then `b0=2` and `2v+w=2`; the listed tops
contribute `14+3v+2w≥17` to `L`. Both contradict `L=16`.

## 3. Fifteen forces exactly three one-valued blocks

Suppose `L=15`. For `p∈{1,2,3}`, `δ∈{0,1,2}`, the pointwise
inequality

\[
\mathbf1_{\{δ=1\}}\le3-p+(p-2)δ
\tag{3}
\]

is immediate. Summing its right side with `δ=δ^+` gives
`54−40+20−30=4`. The number of tops with `δ^+=1` is odd,
since their contributions have the parity of `L=15`. It cannot
be one: its nonempty `P`-block would cover some label once, not
zero or twice. Therefore it is exactly three. Dually there are
exactly three tops with `δ^-=1`.

The total slack in (3) is consequently one. The complete pointwise
slack table is

| `p` | `δ=0` | `δ=1` | `δ=2` |
| ---: | ---: | ---: | ---: |
| 1 | 2 | 0 | 0 |
| 2 | 1 | 0 | 1 |
| 3 | 0 | 0 | 2 |

Thus no singleton `P`-block has `δ^+=0`, no triple `P`-block
has `δ^+=2`, and exactly one double `P`-block has `δ^+≠1`.
The dual assertions hold for `C,δ^-`.

These restrictions and (2) show that

\[
p=2,\ δ^+=1\quad\Longleftrightarrow\quad
c=2,\ δ^-=1.
\tag{4}
\]

For example, if the left side holds, `c=1` would have
`δ^-∈{1,2}`, making `δ^+−δ^-∈{0,−1}` instead of the
required residue one. If `c=3`, then `δ^-∈{0,1}`, making
the difference zero or one instead of residue two. Thus `c=2`,
and the equal-size case forces `δ^-=1`. The converse is dual.

## 4. Both possible double-block counts force overlapping rectangles

Let `b1` count the tops in (4). Among the three `δ^+=1` blocks,
the total cardinality is even because each covered label occurs twice.
Of three sizes in `{1,2,3}`, this means an odd number are two.
Hence `b1=1` or `3`.

If `b1=3`, the three `P`-blocks are pairs covering each label
zero or twice. They form a triangle: a parallel pair would leave
the third edge with degree-one endpoints. The dual three `C`-pairs
also form a triangle. Every two of these tops have intersecting
`P`-blocks and intersecting `C`-blocks, contrary to disjointness
of their central rectangles.

If `b1=1`, the slack statement gives exactly two tops with a
double `P`-block and exactly two with a double `C`-block, one
of which is the common double/double top in (4). Every central
row partitions ten labels into `3331` or `3322`; thus the `P`-blocks
of the two double-`C` tops must be equal, since a label occurs in
either both or neither. As one of these tops has `P` size two,
both are double/double tops. They are also exactly the two
double-`P` tops, so the dual argument makes their `C`-blocks equal.
Their rectangles coincide, again impossible.

Thus `L=15` is excluded. Together with §2 this proves `L≤14`
and `E=20−L≥6`.
