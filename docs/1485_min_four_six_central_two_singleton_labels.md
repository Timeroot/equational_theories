# Two singleton labels cannot support a degree-seven first output

Research note, 20 September 2026. This is an analytic exclusion under
minimum degree `r=4`, central count `m=6`, and first noncentral top-product
degree `p=7`. It uses no finite enumeration or solver output and is not
yet formalized in Lean.

Write `P_v,C_v` for the central predecessor and successor blocks of a
top. Let `S` be the set of labels which occur as singleton `C` blocks,
and `R` the analogous set for singleton `P` blocks. We use the
singleton-label lemma: `S∩R=∅`. Its short proof is included below so
the argument does not depend on an unpublished normalization.

**Theorem.** Under these hypotheses, `|S|≠2`. Dually, `|R|≠2`.

## 1. Singleton labels and forced crowns

Every central row partitions six labels into four nonempty blocks;
in particular at least two of its `C` blocks are singletons. If
`C_u={c}`, omit any singleton-`C` top `d` from `Row(c)`. The exact
replacement argument of
[the first-output note](1485_min_four_six_central_seven_profiles.md#1-a-singleton-central-row-gives-an-exact-replacement)
gives a degree-seven output with four top predecessors `U` and four
top successors

`V=(Row(c)\{d})∪{w}`, where `C_w=C_d` and `w∉Row(c)`.

Its central-middle matrix `(|C_x∩P_y|)_(x∈U,y∈V)` is the crown
`J₄−I₄`. The row belonging to `u` has ones at the three retained
tops. No other member of `U` can have `c` in its `C` block: this
would give the same crown row. Thus none of the retained tops can
have predecessor block `{c}`, since its column would have only one
one. Given any top in `Row(c)`, one can omit a different singleton
top, because there are at least two. Consequently no top has
predecessor block `{c}`. This proves `S∩R=∅`.

We also use the previously proved
[maximal-block theorem](1485_maximal_central_block_first_output_gap.md),
which forbids central profiles `(3,1)` and `(1,3)` here.

## 2. Suppose that there are just two singleton labels

Put `S={c,d}` and `H=Z\S`, so `|H|=4`. Every central row has
exactly the singleton blocks `{c},{d}` and two pair blocks which
partition `H`. Indeed a triple would leave three distinct singleton
labels, which are unavailable. Thus every `C` block is either a
singleton in `S` or a pair contained in `H`.

Any predecessor triple contains both elements of `S`: in a central
column containing such a triple, its complementary three labels
are singleton predecessor blocks and hence belong to `R`, disjoint
from `S`. A predecessor pair belonging to `Row(c)` is either `S`
or `{c,h}` for some `h∈H`; predecessor singletons there are
impossible by Section 1.

Choose a forced crown by omitting a singleton top from `Row(c)`.
Its three retained columns consist of one singleton-`C` top and
both pair-`C` tops. The predecessor block `S` cannot occur in a
retained column: its intersection with a pair contained in `H`
is empty, and there is at most one crown row with singleton
`{c}` and at most one with singleton `{d}`. Such a column therefore has at most
two ones instead of three. In particular the retained singleton-
`C` top has predecessor block `{c,k}` for some `k∈H`.

Other than the known row `{c}`, the crown rows consist of either
three pairs in `H`, or singleton `{d}` and two pairs in `H`.
They cannot have repeated singleton or pair sets, since crown
rows are distinct.

The first alternative is impossible. On these three pair rows,
each retained column has the same incidence as one label of `H`:
its predecessor block is `{c,h}` or `S∪{h}`. The three labels
must be distinct, because crown columns are distinct, and each
occurs in exactly two of the three pair rows. These rows are
therefore the three edges of a triangle on those labels. The
replacement column, whose zero is at row `{c}`, must meet each
of these three edges in exactly one point. No subset of the
triangle vertices does so.

We are left with row `{d}` and two distinct pair rows in `H`.
Both pair rows contain `k`, in order that the retained column
`{c,k}` have three ones. If a retained pair-`C` top had a
predecessor pair `{c,h}`, both pair rows would also contain `h`.
Their intersection is `{k}`, so `h=k`, giving a repeated crown
column. Its predecessor block must therefore be a triple.

Both pair-`C` tops on `Row(c)` consequently have predecessor
triples. These contain all of `S`, so the same two tops occur
on `Row(d)`. Their successor pairs partition `H`. There are
no other predecessor triples: every predecessor triple contains
`S` and would have to occur on `Row(c)`.

Write their predecessor blocks as `S∪{h₁}` and `S∪{h₂}`.
They are distinct, since they occur in the same crown. In the
crown just considered, the two pair rows are then precisely
`{k,h₁}` and `{k,h₂}`.

## 3. A diagonal singleton top gives the contradiction

Choose `u` at the central cell `(c,c)`. Its successor block is
`{c}`. Its predecessor block is a pair `{c,k}`: predecessor
singletons are forbidden on `Row(c)`, triples paired with a
singleton are forbidden, and the pair `S` was excluded above
by retaining this top in a crown.

Omit from `Row(c)` the singleton top at central cell `(c,d)`.
The resulting crown retains `u` and the two predecessor-triple
tops. The replacement `w` has `C_w={d}`. By Section 2 its
predecessor rows have successor blocks

`{c}, {d}, {k,h₁}, {k,h₂}`.

The predecessor blocks of these four rows partition six labels
and include `P_u={c,k}`. Their sizes must therefore be
`2,2,1,1`; none is a triple. To cover label `d`, the other
predecessor pair must contain `d`, since no predecessor singleton
can use a label of `S`. This other pair cannot belong to one
of the pair-`C` rows: every top on `Row(d)` with a pair `C`
block is one of the two predecessor-triple tops. It belongs to
the row with successor block `{d}`, and so is the unique top
`x` at central cell `(d,d)`.

The replacement column must meet row `{d}`, hence `d∈P_w`.
Since `C_w={d}`, uniqueness at a central cell gives `w=x`.
Its predecessor block is a pair containing `d`, and it must
meet both pair rows `{k,h₁}`, `{k,h₂}`. Thus `P_x={d,k}`.
But `P_x` and `P_u={c,k}` overlap at `k`, contradicting the
predecessor-block partition of `U`.

This proves the theorem. The singleton-label sets would therefore
both have size three and be complementary. This conclusion alone
is a reduction, but combined with the general containment bound
it now yields the [complete six-central degree-seven exclusion](1485_min_four_six_central_seven_exclusion.md).
