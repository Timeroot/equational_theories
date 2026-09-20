# Full-size central blocks at the boundary first-output degree

Research note, 20 September 2026. These are analytic finite E1485
theorems, with no enumeration or Lean dependency.

Let the minimum translation degree be `r≥2`, the central class be
`Z` of size `m`, and the top class be `T`. Write `P_v,C_v` for the
central predecessor and successor blocks of a top vertex, and let
`S_P,S_C` be the labels that occur as singleton blocks. Suppose the
least degree of a noncentral **product of two tops** is

`p=2r−1`.

**Theorem.** A central predecessor block of size `r` is incompatible
with any singleton successor block:

\[
\boxed{\exists v\in T,\ |P_v|=r\quad\Longrightarrow\quad S_C=\varnothing.}
\]

Dually, a successor block of size `r` implies `S_P=∅`. There is no
central-count bound and no assumption on the opposite block of `v`.

## 1. A size-`r` block meets every opposite block

Every global predecessor block and successor block intersect in at
most one point. If `A=P_v` has size `r`, every successor block `C_w`
meets `A` exactly once: place `w` in one of its central rows. The `r`
successor blocks on that row partition `Z`, and their intersections
with `A` have size at most one and cover all `r` elements of `A`.

In particular every singleton-successor label belongs to `A`.

## 2. Arbitrary omissions suffice

Suppose `S_C` is nonempty, choose `c∈S_C`, and take a source top `u`
with `C_u={c}`. Since `c∈A`, the top `v` belongs to `Row(c)`.
Choose **any** other top `d∈Row(c)`, so `d≠v`; such a top exists
because the row has `r≥2` members.

Choose `z∈C_d` and a least noncentral member `a` of `u*Col(z)`.
The row-local degree bound puts `d(a)≤2r−1`, while the globally
least noncentral top-output degree is `p=2r−1`. Hence `d(a)=p`.
The exact-replacement identity is

\[
Row(a)=L_u^{-1}(a)\ \sqcup\bigl(Row(c)\setminus\{d\}\bigr).
\]

The proof is in the
[arbitrary-omission replacement argument](1485_maximal_central_block_first_output_gap.md#2-every-omitted-central-row-point-occurs).
That identity itself needs only the singleton source and equality
`p=2r−1`; it does **not** need a maximal predecessor block or a
singleton omission. In particular `v∈TopSucc(a)`.

The [first-output theorem](1485_first_top_output_fibers.md) says that
`U=TopPred(a)` and `V=TopSucc(a)` have the same size `t`, where
`r≤t≤2r−2`, and that the central-middle matrix

`K_(x,y)=|C_x∩P_y|`, for `x∈U,y∈V`,

has every row and column sum `p−r=r−1`. Its column at `v`, however,
has an entry one in **every** row by Section 1. Its column sum is
therefore `t≥r`, a contradiction.

No claim that `t=r` or that this matrix is a crown is needed. This
is the additional observation that removes both the singleton-omission
condition and the central-count restriction from the earlier proof.

## 3. Consequences at and below `m=2r`

Every central block has size at most `r`, by the same orthogonality
and central-partition argument. If `m<2r`, a central partition into
`r` nonempty blocks contains a singleton on each side. Thus the
theorem immediately gives

\[
\boxed{m<2r\quad\Longrightarrow\quad |P_v|,|C_v|\le r-1
\quad(v\in T).}
\]

This subsumes the earlier
[boundary block bound and its larger-count corollary](1485_boundary_singleton_overlap.md#no-central-block-can-have-size-r-at-the-boundary).
In particular it also covers an opposite singleton block directly,
without invoking the separate maximal-partition-block theorem.

Now suppose `m=2r`. If a predecessor block has size `r`, the theorem
makes every successor block nonsingleton. Each central row partitions
`2r` labels into `r` such blocks, so every one has size exactly two.
Every top occurs on a central row, giving

\[
\boxed{m=2r,\ \exists v\ |P_v|=r
\quad\Longrightarrow\quad |C_w|=2\quad\text{for all }w\in T.}
\]

The dual holds as well. The central incidence identity
`∑_(w∈T)|C_w|=rm` then gives `|T|=r²`, and every vertex has exactly
`r` top successors, since their two-element central successor blocks
partition `Z`.

If `r≥3`, a central column containing the size-`r` predecessor block
has `r−1` other predecessor blocks covering the remaining `r` labels.
They consist of one pair and `r−2` singletons. Thus in this case

`|S_P|≥r−2`, while `S_C=∅`.

## 4. The minimum-four, eight-central reduction

At `r=4,m=8,p=7`, every size-four predecessor block therefore forces
**all** successor blocks to be pairs, exactly sixteen top vertices,
and at least two singleton-predecessor labels. The dual assertion
holds for a size-four successor block.

Consequently:

- If both singleton-label sets are nonempty, all central blocks have
  size at most three.
- If both singleton-label sets are empty, all central blocks are pairs.
- If only `S_C` is empty, all successor blocks are pairs; size-four
  predecessor blocks remain possible under this argument alone.
  There is a dual one-empty-set case.

This restricts the eight-central branch but does not exclude it. In
particular the known
[all-pair incidence examples](1485_min_four_eight_central_pair_crowns.md)
are not contradicted, and no magma is asserted to realize the
one-empty-set alternatives.

## 5. A finite graph reduction for a size-four block

In the `r=4,m=8,p=7` case with `P_v=A` of size four, put
`H=Z\A`. Every successor pair meets `A` once, so regard each top
`w` as an edge `C_w` of a bipartite multigraph `G` with parts `A,H`.
Parallel edges correspond to distinct tops having the same successor
pair; they must not be identified. Every central label belongs to
exactly four successor blocks, so `G` is four-regular and has sixteen
edges.

Every predecessor block is an independent set in `G`, by global
predecessor/successor orthogonality. For each central label `x`, the
four tops on `Row(x)` give a perfect matching of `G`; an edge `w`
occurs in exactly the matchings indexed by labels in `P_w`. Thus
one obtains eight label-indexed perfect matchings of this multigraph,
and each edge's membership-label set must be independent in `G`.
The distinguished edge `v` lies in all four matchings indexed by `A`
and none indexed by `H`.

Any other size-four predecessor block must choose **one whole
bipartition class from each connected component** of `G`. Indeed, a
four-element independent set in this four-regular eight-vertex graph
has all sixteen edge incidences leaving it. These already account
for every edge of `G`, so its complement is independent as well.
It therefore defines a bipartition; on a connected bipartite graph,
that bipartition is unique up to exchange of its two classes.

Each component has equally many labels on the two sides, by regularity.
The component half-sizes consequently form one of the five partitions

`4`, `3+1`, `2+2`, `2+1+1`, or `1+1+1+1`.

This is a precise bounded graph reduction, not an exclusion. It retains
the further perfect-matching constraints, the boundary first-output
conditions, and the actual magma identities still to be imposed.
