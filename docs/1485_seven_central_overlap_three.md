# Three common singleton labels at seven central vertices: analytic exclusion

Research note, 20 September 2026. This is an analytic finite E1485 theorem.
It needs no enumeration or solver result and is not yet in Lean. The
earlier exact-cover checker remains an independent regression check,
not a dependency of the proof below.

Suppose the minimum degree is `r=4`, the central count is `m=7`, and
the least noncentral top-product degree is `p=7`. Then

\[
\boxed{|S_P\cap S_C|\le2.}
\]

## 1. The two possible outside-map patterns

The [boundary overlap theorem](1485_boundary_singleton_overlap.md) bounds
the common singleton-label set `I=S_P∩S_C` by three. If it has size
three, the other four labels split into the predecessor-only set `A`
and successor-only set `B`, each of size two. The outside maps

`y:I→A`, `z:I→B`

each have fiber sizes two and one. For every common label `c`, their
singleton rectangles are uniquely

`({y(c)},{c})` and `({c},{z(c)})`.

The common row at `c` has only one singleton successor block, `{z(c)}`;
its other three blocks are pairs. Dually the common column at `c` has
only the singleton predecessor block `{y(c)}`, and three pairs.

If the double fibers of `y,z` agree, the
[joint-fiber inequality](1485_common_singleton_joint_fibers.md) would give
`7−2≤(4−2)²`, or `5≤4`. Thus they differ. Relabel the common labels
as `c,d,e` and the outside labels as `A={y₀,y₁}`, `B={z₀,z₁}` so that

\[
y(c)=y(d)=y_0,\quad y(e)=y_1,
\qquad
z(c)=z(e)=z_0,\quad z(d)=z_1.
\]

We show that this remaining pattern is impossible as well.

## 2. Two residual partitions make a four-label grid

The central row at `y₀` has the two singleton successor blocks `{c}`,
`{d}`. Its remaining two blocks must have sizes two and three. For
completeness, the alternative sizes one and four are impossible: a top
with successor block of size four there would force every row meeting
its predecessor block to cover the complementary three labels with
singletons. These include `c,d`, whose singleton-successor tops both
have predecessor block `{y₀}`. The predecessor block of the size-four
top would therefore be `{y₀}`, contrary to the maximal-block theorem.

Write the residual pair and triple as `E,F`. Dually the central column
at `z₀` has singleton predecessor blocks `{c}`, `{e}` and residual
pair and triple `D,G`. Thus

\[
E\sqcup F=Z\setminus\{c,d\},\qquad
D\sqcup G=Z\setminus\{c,e\},
\]

with `|D|=|E|=2`, `|F|=|G|=3`.

Every predecessor block meets every successor block in at most one
label. Since the predecessor triple `G` avoids `c`, it must meet all
three of the other successor blocks `{d},E,F` on `Row(y₀)`.
Consequently `d∈G`. Dually `e∈F`.

Put `H=Z∖{c,d,e}=A⊔B`. The pairs

`D, G∖{d}` and `E, F∖{e}`

are two partitions of the four-element set `H`. Each of their four
cross-intersections has size at most one; together they cover all of
`H`. Every cross-intersection therefore has size exactly one. In
particular,

\[
\boxed{|D\cap E|=1.}                              \tag{1}
\]

## 3. The triple tops force the two pairs to be disjoint

Let `w∈Row(y₀)` have successor block `C_w=F`. Since `e∈F`, it also
belongs to `Col(e)`. The latter has its unique singleton predecessor
block `{y₁}`, while `y₀∈P_w` and `y₀≠y₁`. Thus `P_w` is one of
that column's pairs. Write

`P_w={y₀,h}`, where `h≠y₀`.

On `Row(h)`, the block `F` leaves exactly the four labels `{c,d}⊔E`
to be covered by the other three successor blocks. These have sizes
two, one, and one. Neither `c` nor `d` can occur as a singleton
successor block there: their unique singleton-successor tops have
predecessor block `{y₀}`, which does not contain `h`.
Therefore the pair block is `{c,d}`, and the two elements of `E`
are singleton successor labels.

But `E⊆H`, whose singleton successor labels are exactly `B`. Both
sets have size two, so

\[
E=B.
\]

Dually, the top `v∈Col(z₀)` with predecessor block `G` also belongs
to `Row(d)`, because `d∈G`. Its successor block cannot be the unique
singleton `{z₁}` on that row, because it contains `z₀≠z₁`.
It is a pair `{z₀,k}`. In `Col(k)`, the remaining three predecessor
blocks cover `{c,e}⊔D`. The common labels `c,e` cannot be singleton
predecessor blocks there, since their unique such tops have successor
block `{z₀}`. Hence the pair is `{c,e}` and both labels of `D` are
singleton predecessors. It follows that

\[
D=A.
\]

Since `A∩B=∅`, these identities contradict (1). This excludes the
different-double-fiber pattern and completes the analytic proof.

## Independent finite regression

The standalone
[1485_m7_overlap_three_check.py](../scripts/1485_m7_overlap_three_check.py)
enumerates the necessary central rectangle systems in both outside-map
normalizations. It does not use the analytic contradiction above.
It finds no central cover in either case: 605 candidate rectangles and
8,112 recursive states in the same-double-fiber case; 605 candidates
and 16,838 states in the different-double-fiber case. The two checks
take approximately one second together on the development machine.

The search branches over every candidate covering a selected uncovered
central cell, deleting overlaps and cross-intersection violations. It
requires four rectangles per central row and column and uses only
elementary line-count pruning. Its positive and negative unit-grid
controls and deterministic counts are asserted by the script. These
calculations independently corroborate the theorem but are not needed
for its analytic proof.
