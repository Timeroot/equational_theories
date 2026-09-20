# Overlapping singleton labels at central count `2r−1`

Research note, 20 September 2026. These are analytic necessary conditions,
not an exclusion of this central count or a Lean formalization.

Suppose a finite E1485 magma has minimum degree `r≥3`, central
count `m=2r−1`, and least noncentral top-product degree `p=2r−1`.
Let `S_C,S_P` be the labels occurring as singleton successor and
predecessor blocks of top vertices.

An additional theorem proved at the end of this note is that **every
central block has size at most `r−1`** under these boundary assumptions.
It is analytic and does not require singleton-label separation. At
minimum four and central count seven, it removes all size-four blocks.

At smaller central counts `m≤2r−2`, the
[singleton-label separation theorem](1485_singleton_central_labels_first_output.md)
proves that these sets are disjoint. At `m=2r−1`, every central
partition still has a singleton block, but it may have just one.
The exact-replacement argument still makes **every singleton
omission** a crown of size `r`; this does not require two available
omissions. The missing second omission is the only reason that the
earlier separation proof does not apply directly.

**Theorem.** If `c∈S_C∩S_P`, there are unique tops `u,v` with

\[
C_u=\{c\},\qquad P_v=\{c\}.
\]

They have profiles

\[
\boxed{
(P_u,C_u)=(\{y\},\{c\}),\qquad
(P_v,C_v)=(\{c\},\{z\}),
\quad y\in S_P\setminus S_C,
\quad z\in S_C\setminus S_P.
}                                                        \tag{1}
\]

The central row at `c` has unique singleton successor block
`C_v={z}`, and all its other successor blocks are pairs. The
central column at `c` has unique singleton predecessor block
`P_u={y}`, and all its other predecessor blocks are pairs.

Consequently any top with predecessor block of size at least three
has its successor block disjoint from `I=S_C∩S_P`: otherwise it
would occur in a common label's central column, where every
predecessor block has size at most two. Dually, a successor block
of size at least three has predecessor block disjoint from `I`.

In particular `y,c,z` are distinct. Common singleton labels cannot
support diagonal `(1,1)` tiles, or `(1,1)` arrows to another
common singleton label. Each lies on a two-step singleton-tile
path from a predecessor-only label to a successor-only label.
The maps `c↦y` and `c↦z` need not be injective by this argument.

## Proof

Fix `c∈S_C∩S_P` and choose `u` with `C_u={c}`. Suppose a
top `v` has `P_v={c}`. It belongs to `Row(c)`. Any singleton
omission from that row must omit `v`: if it retained `v`, the
crown row at `u` would contain the `r−1` retained ones, no
other crown row could contain `c`, and the column at `v` would
have just one one rather than `r−1≥2`.

There is at least one singleton successor block on `Row(c)`.
Consequently `v` is its unique singleton-block top and is also
the unique top globally with predecessor block `{c}`. Write
`C_v={z}`. The other `r−1` successor blocks have total size
`2r−2` and are nonsingletons, so all are pairs.

The dual argument shows that `u` is the unique top globally
with successor block `{c}`, that `P_u={y}` is the unique
singleton predecessor block on `Col(c)`, and that the other
predecessor blocks there are pairs.

It remains to identify `y,z` more precisely. Omit `v` from
`Row(c)` using the singleton row at `u`. Exact replacement
produces a new top `w∉Row(c)` with

`C_w=C_v={z}`.

Thus the singleton successor label `z` occurs on at least two
distinct tops, `v,w`. If `z` belonged to `S_P` as well, the
uniqueness just proved for common singleton labels would prohibit
this. Therefore `z∈S_C\S_P`. The dual replacement argument
gives `y∈S_P\S_C`, proving (1).

## A count of singleton tiles

Let `I=S_C∩S_P`, and let `N₁₁` count tops with both central
blocks singleton. The theorem gives

\[
\boxed{N_{11}\ge 2|I|.}                                 \tag{2}
\]

Indeed the tops `u_c` are distinct as `c` varies, because their
successor labels are distinct; the tops `v_c` are distinct because
their predecessor labels are distinct. These two families are also
disjoint: the successor label of every `u_c` belongs to `I`,
whereas the successor label of every `v_c` is outside `S_P`.
This is a bound on tiles, not an assertion that the outside labels
`y,z` are distinct for different common labels.

## The outside-label maps have small fibers

Although the maps in (1) need not be injective, every fiber has
size at most `r−2`. To prove this for `c↦y`, fix a predecessor-
only label `y`. A fiber of size `r` would put `r` distinct
singleton-`C` tops on `Row(y)`, covering only `r` central
successor labels instead of `2r−1`, so is impossible.

If a fiber has size `r−1`, the row contains the corresponding
unique tops `u_c`, each with predecessor block `{y}`. Its last
top `v` has a successor block of size `r`, complementary to those
`r−1` common labels. For any `x∈P_v`, the central row at `x`
contains `v` and must cover those remaining `r−1` labels with
`r−1` singleton blocks. Uniqueness for common labels forces these
tops to be the same `u_c`; since `P_(u_c)={y}`, this gives
`x=y`. Thus `P_v={y}` and the profile of `v` is `(1,r)`.
The [maximal-block theorem](1485_maximal_central_block_first_output_gap.md)
excludes this at `m=2r−1,p=2r−1`. Larger fibers also cannot
fit in the row. The dual argument handles `c↦z`.

Writing `a=|S_P\S_C|`, `b=|S_C\S_P|`, and `i=|I|`, we obtain

\[
\boxed{i\le(r-2)a,\qquad i\le(r-2)b,\qquad
i+2\left\lceil\frac{i}{r-2}\right\rceil\le2r-1.}       \tag{3}
\]

In particular `i≤2r−5`: if `i≥2r−4`, both `a,b` are at
least two and their disjoint union with `I` has at least `2r`
labels. If `r≥4` and equality `i=2r−5` holds, then `a=b=2`
and the two singleton-label sets together cover all central labels.

## Minimum-four specialization and subsequent resolution

At minimum degree four and central count seven, a common singleton
label therefore forces the row and column shapes `1+2+2+2`, with
the singleton labels pointing outward as in (1). There are at most
three common singleton labels. If there are three, the seven labels
split into two predecessor-only, three common, and two successor-only
labels, and both outside maps have fiber sizes two and one.

There is an additional restriction on a two-element outside fiber.
If common labels `c,d` both map to the same predecessor-only
label `y`, then `Row(y)` has two singleton successor blocks
`{c},{d}` and its remaining two blocks must have sizes two and
three. The only alternative is sizes one and four. A size-four
top there would force every row in its predecessor block to
cover the complementary three singleton labels, including `c,d`,
using the unique tops with predecessor `{y}`. Its predecessor
block would therefore be `{y}`, giving the forbidden profile
`(1,4)`. There is a dual restriction at a two-element fiber of
`c↦z`.

The conditions above were the initial reduction. The
[joint-fiber and block bounds](1485_common_singleton_joint_fibers.md)
now strengthen the general estimate to `i≤2r−6` for every `r≥4`.
At minimum four, the [three-label exclusion](1485_seven_central_overlap_three.md)
is analytic; the [two-label](1485_seven_central_overlap_two.md) and
[one-label](1485_seven_central_overlap_one.md) finite checks exclude the
remaining nonempty overlap cases. Thus `S_C∩S_P=∅` at `r=4,m=p=7`.
This does not by itself exclude a degree-seven first output at this
central count: the disjoint-label configurations remain to be considered.

## The exact containment restriction at the boundary

Return to the general assumptions `r≥3`, `m=p=2r−1`. No global
singleton-label separation is assumed in this section. Suppose distinct
tops `v,w` satisfy

\[
P_w\subseteq P_v,\qquad P_w\cap S_C\ne\varnothing,
\qquad |C_v|\ge2.
\]

Then the following two cases are impossible:

1. `|C_w|≥2`.
2. `|C_v|≥3`, regardless of the size of `C_w`.

Indeed, fix any `c∈P_w∩S_C` and a top `u` with `C_u={c}`.
Both `v,w` belong to `Row(c)`. Every central row has a singleton
successor block. If both `C_v,C_w` are nonsingletons, omit any singleton
top: the resulting crown retains both `v,w`. Their predecessor inclusion
makes the column at `w` entrywise at most that at `v`. Both columns have
`r−1` ones, so they are equal, contrary to distinct crown columns.

If `|C_v|=b≥3`, the other `r−1` blocks on `Row(c)` cover
`2r−1−b` labels. At least

`2(r−1)−(2r−1−b)=b−1≥2`

of those blocks are singletons. Thus one can choose a singleton omission
different from `w` even when `C_w` is singleton; the same contradiction
applies.

Consequently the **only possible exception** to the earlier unrestricted
containment theorem is

\[
\boxed{|C_v|=2,\qquad |C_w|=1,}
\]

where, for every `c∈P_w∩S_C`, the top `w` must be the unique
singleton-successor top on `Row(c)`. Otherwise another omission would
retain both columns. Such a row necessarily has shape `1+2+⋯+2`.
This describes a remaining possibility, not an existence assertion.
There is a dual statement with predecessor and successor directions
exchanged.

In particular, the usual numerical containment bound still holds at
the boundary when the opposite block has size at least three:

\[
\boxed{|C_v|\ge3,\quad P_v\subseteq S_C
\quad\Longrightarrow\quad |P_v|\le m-r=r-1.}
\]

To prove this, choose a central column not containing `v`. Its `r`
predecessor blocks partition `Z`; none can be contained in `P_v`,
by case 2 above. Each therefore contains a point outside `P_v`,
which gives `|P_v|≤m-r`. The dual numerical bound also holds.

## No central block can have size `r` at the boundary

Under the same boundary assumptions `r≥3`, `m=p=2r−1`, every top
vertex satisfies

\[
\boxed{|P_v|,|C_v|\le r-1.}
\]

This is analytic and does not assume singleton-label separation. A
central block has size at most `m-r+1=r`, so it suffices to exclude
equality. Suppose `A=P_v` has size `r`.

Every global successor block `C_w` meets `A` **exactly once**. Indeed,
place `w` in a central row containing it. That row's `r` successor
blocks partition `Z`; each intersects `A` at most once and together
they cover all `r` elements of `A`. Hence every intersection is a
singleton. In particular, every singleton successor label lies in `A`.

If `|C_v|=1`, the
[maximal-block theorem](1485_maximal_central_block_first_output_gap.md)
already gives a contradiction, because `|P_v|=m-r+1`.
Otherwise `C_v` is nonsingleton. Since a partition of `2r-1` labels
into `r` blocks has a singleton, choose any singleton successor label
`c` and a source top `u` with `C_u={c}`. The preceding paragraph
gives `c∈A`, so `v∈Row(c)`.

Omit any singleton-successor top from `Row(c)`. It is not `v`, whose
successor block is nonsingleton, so the resulting `r×r` crown retains
`v` as a column. But that column has an entry one in **every** row:
all global successor blocks, including the crown's row blocks, meet
`P_v=A` exactly once. Its column sum is `r`, not the required `r-1`.
This contradiction excludes `|P_v|=r`. The dual argument excludes
`|C_v|=r` and proves the theorem.

At `r=4,m=p=7`, all predecessor and successor blocks consequently
have size at most three. This subsumes the earlier special exclusion
of a `(4,4)` profile. It still does not exclude all size-three blocks,
and so does not by itself finish the seven-central branch.

## A size-`r` block restriction at larger central counts

There is also a useful generalization without the assumption `m=2r−1`.
Suppose `r≥3`, the least noncentral top-product degree is `p=2r−1`,
and at least one singleton-successor label exists. Then no top `v`
satisfies

\[
\boxed{|P_v|=r,\qquad
|C_v|\ge\max\{2,m-2r+3\}.}
\]

As above, every global successor block meets `P_v` exactly once, and
therefore every singleton-successor label lies in `P_v`. Choose one,
say `c`, and a source `u` with `C_u={c}`. The top `v` belongs to
`Row(c)`. Its other `r−1` successor blocks cover at most `2r−3`
labels, by the displayed size bound, so at least one is singleton.
Omit such a top. Since `C_v` is nonsingleton, the omission retains `v`.

Exact replacement still produces a crown of size `r`: the retained
central-row successor blocks cover all central labels except the omitted
singleton, and the new nonempty successor blocks partition that singleton,
so there is exactly one replacement top. This reasoning is independent
of the value of `m`. The column at `v` again has `r` ones, contrary
to the required crown column sum `r−1`.

The dual statement assumes a singleton-predecessor label and exchanges
`P,C`. In particular, at minimum four and first-output degree seven,
the presence of singleton-successor labels excludes profiles `(4,3)`
and `(4,4)` when `m=8`, and excludes `(4,4)` when `m=9`.
No singleton-label separation assumption is needed.
