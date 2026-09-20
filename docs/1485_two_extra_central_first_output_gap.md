# Two extra central vertices lower the first top-output degree

Research note, 20 September 2026. This is an analytic finite E1485
theorem. It uses no enumeration or solver result and is not yet
formalized in Lean.

Let `r` be the minimum translation degree, let `Z` be the central
class, and suppose `|Z|=r+2`. Write `P_v,C_v` for a top vertex's
central predecessor and successor blocks. If noncentral products of
two tops occur, let `p` be their least degree.

**Theorem.** If `r≥4` and `|Z|=r+2`, then

\[
\boxed{p\le 2r-2.}
\]

In particular, at `r=4,m=6`, the first noncentral top-product degree
cannot be seven. This excludes that entire first-output branch, not
every magma with six central vertices and not every minimum-four
candidate for the spectrum conjecture.

## 1. Boundary outputs and disjoint singleton labels

A central row or column partitions `r+2` labels into `r` nonempty
blocks. Its shape is either

`3+1+⋯+1` or `2+2+1+⋯+1`.

Every block has size at most three, and at least `r−2` blocks are
singletons. Let `S` be the labels occurring as singleton `C` blocks,
and `R` those occurring as singleton `P` blocks. Thus

\[
|S|,|R|\ge r-2.                                      \tag{1}
\]

A singleton top row supplies `p≤2r−1` by the
[ordered auxiliary-degree bound](1485_auxiliary_ordered_degree_bound.md).
Suppose for a contradiction that `p=2r−1`. The
[maximal-block theorem](1485_maximal_central_block_first_output_gap.md)
forbids top block sizes `(3,1)` and `(1,3)` under this assumption.

We will repeatedly use the following forced crown. If `C_u={c}`
and `d∈Row(c)` has singleton `C_d`, there is a degree-`p` output
with top profiles `U,V` such that

\[
u\in U,\qquad V=(Row(c)\setminus\{d\})\cup\{w\},\qquad
C_w=C_d,\quad w\notin Row(c),                          \tag{2}
\]

and its central-middle matrix on `U×V` is `J_r−I_r` after
reindexing. Here is why the top-profile size is exactly `r`, even
without a maximal predecessor block at `u`. Choose `z∈C_d` and
a least noncentral output `a` in `u*Col(z)`. The ordered bound
makes its degree `p`. The first-output fiber argument gives the
exact disjoint union

\[
Row(a)=L_u^{-1}(a)\ \sqcup\ (Row(c)\setminus\{d\}),
\]

as in the [maximal-block proof](1485_maximal_central_block_first_output_gap.md#2-every-omitted-central-row-point-occurs).
The `r−1` retained tops cover all central successor labels except
the singleton `C_d`. The successor blocks of the new tops
partition that singleton, so there is precisely one new top.
Both top profiles therefore have size `r`; their regular degree
`p−r=r−1` makes their central-middle matrix a crown.

For a crown in (2), row `u` has ones at the `r−1` retained tops.
No other row can have `c` in its successor block, since its crown
row would be the same. Thus a retained column cannot have
predecessor block `{c}`: it would have just one one. There are
at least `r−2≥2` singleton blocks on `Row(c)`, so any particular
top there can be retained by omitting a different singleton top.
Consequently no singleton predecessor block uses label `c`, and

\[
\boxed{S\cap R=\varnothing.}                          \tag{3}
\]

Another useful consequence is that two retained predecessor blocks
cannot be nested. Inclusion of their sets implies inclusion of
their column supports in the central-middle matrix. Both columns
have `r−1` ones, so the supports would be equal, contrary to the
distinct columns of a crown.

## 2. Predecessor triples are impossible

Suppose a top has a predecessor triple. The central column
containing it has `r−1` complementary singleton predecessor
blocks. Hence `|R|≥r−1`. Equations (1) and (3) give

\[
2r-3\le |S|+|R|\le r+2,
\]

so `r≤5`.

For `r=5`, equality forces `|S|=3`, `|R|=4`, with `S,R`
complementary. Every predecessor triple is exactly `S`, since
its complement consists of singleton predecessor labels in `R`.

For `r=4`, one has `|R|≥3` and `2≤|S|≤3`. The
[two-singleton-label theorem](1485_min_four_six_central_two_singleton_labels.md)
excludes `|S|=2`. Thus again `|S|=3`, `S,R` are complementary,
and every predecessor triple is `S`.

In either case there is at most one top `v` with a predecessor
triple. Indeed all such tops lie on every `Row(c)` for `c∈S`.
Their `C` blocks are nonsingletons, since `(3,1)` is forbidden.
Any singleton omission from such a row would retain two of them
if two existed, giving repeated crown columns with predecessor
block `S`.

Choose a central column outside `C_v`; this is possible since
`|C_v|≤3<r+2`. Its predecessor partition has no triple and
therefore consists of two pairs and `r−2` singletons. The
singleton labels are in `R`; the two pairs must cover the three
labels of `S`. Hence at least one pair `P_w` is a subset of
`S=P_v`.

Choose `c∈P_w`. Both `v,w` lie on `Row(c)`. We may omit a
singleton top different from `w`: there are at least two, and
`v` is not a singleton-`C` top. The resulting crown retains
both columns `v,w`, contradicting the nested-column observation
at the end of Section 1.

This excludes every predecessor triple. By duality it excludes
every successor triple as well.

## 3. The remaining crown has only small sets

All central blocks now have size at most two. Choose any singleton
`C_u={c}` and any singleton omission on `Row(c)`. Section 1
produces an `r×r` crown whose row and column sets all have size
at most two, and whose row at `u` is a singleton.

The elementary
[singleton crown lemma](1485_two_set_crown_bound.md#1-a-singleton-permits-at-most-three-pairs)
says such a crown has size at most three. This contradicts `r≥4`,
excludes `p=2r−1`, and proves the theorem.

The only specialized ingredient at `r=4` is the analytic
two-singleton-label argument linked in Section 2. For `r≥5`,
the proof uses just central partitions, exact first-output fibers,
the maximal-block theorem, and the elementary crown lemma.
