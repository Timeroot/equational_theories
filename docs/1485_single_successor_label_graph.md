# A single singleton successor label gives a regular multigraph

Research note, 20 September 2026. This is a finite incidence reduction,
not an exclusion of the remaining degree-seven case.

Let a finite E1485 magma have minimum degree `r≥3`, central set
`Z` of size `m=2r−1`, and top class `T`. For a top `v`, write

\[
P_v=\operatorname{Col}(v)\cap Z,\qquad
C_v=\operatorname{Row}(v)\cap Z.
\]

Assume that the set of labels occurring as singleton blocks `C_v`
is exactly `{c}`. No hypothesis on the least noncentral top-output
degree is needed for the first three conclusions below.

## 1. Exactly `r²` tops, encoded on `2r−2` labels

Every central row consists of `r` tops whose nonempty successor
blocks partition `2r−1` central labels. Such a partition has a
singleton. The only available singleton is `{c}`, and disjointness
allows it exactly once. The other `r−1` blocks have total size
`2r−2` and are therefore pairs, none containing `c`.

Every top has a central predecessor, so this describes every
successor block globally:

\[
\boxed{C_v=\{c\}\quad\text{or}\quad C_v\in\binom{H}{2},
\qquad H=Z\setminus\{c\}.}                     \tag{1}
\]

The tops with successor block `{c}` are exactly the `r` tops in
the central column at `c`. Their predecessor blocks partition `Z`.
Counting central successor incidences gives

\[
\boxed{\#\{v:C_v=\{c\}\}=r,\qquad
\#\{v:|C_v|=2\}=r(r-1),\qquad |T|=r^2.}       \tag{2}
\]

Treat the pair-block tops as distinct edge instances on `H`;
equal pair blocks give parallel edges. Each label belongs to
exactly `r` successor blocks, so this is a loopless `r`-regular
multigraph on `2r−2` vertices. Each central row chooses one of
the singleton-block tops and a perfect matching of this multigraph.
The `r` singleton-block predecessor sets partition the possible
central rows.

## 2. Every predecessor block is an independent set, away from `c`

The central-middle uniqueness inequality

\[
|P_v\cap C_w|\le1\qquad(v,w\in T)
\]

says precisely that `P_v∩H` is independent in the underlying
multigraph. If `A⊆H` is independent, its `r|A|` incident edges
all end in `H\A`, which has total incident-edge capacity
`r(2r−2−|A|)`. Consequently

\[
|A|\le r-1.
\]

Equality forces `H\A` to be independent as well, since all its
incident-edge capacity is already used by edges from `A`.
In particular,

\[
\boxed{|P_v|=r\ \Longrightarrow\
c\in P_v\text{ and the multigraph is bipartite on two
parts of size }r-1.}                              \tag{3}
\]

This assertion permits disconnected multigraphs and parallel edges;
neither can be discarded by the argument.

## 3. Every vertex has exactly `r` top successors

For an arbitrary vertex `x`, the blocks `C_v` of its top successors
partition `Z`. By (1), that partition has one singleton `{c}` and
`r−1` pairs. Therefore

\[
\boxed{|\operatorname{TopSucc}(x)|=r\qquad(x\in M).} \tag{4}
\]

The dual statement follows under the dual single-label hypothesis.
Equation (4) alone does **not** assert that every vertex also has
`r` top predecessors.

## 4. The minimum-four, seven-central, first-output-seven case

Now let `r=4`, and let the first noncentral top-product degree be
`p=7`. The [singleton separation results](1485_seven_central_overlap_one.md)
exclude `c` as a singleton predecessor label. The
[maximal-block theorem](1485_maximal_central_block_first_output_gap.md)
excludes profiles `(4,1)`. Hence the unique top whose central tile
contains `(c,c)` has predecessor-block size **two or three**.

The stronger [boundary maximal-block exclusion](1485_boundary_singleton_overlap.md)
now excludes every size-four predecessor block, not just those
opposite a singleton. Thus the remaining incidence problem has
precisely four singleton-block tops and twelve pair-block tops,
encoded by a 4-regular multigraph on six labels, and all predecessor
blocks have size at most three. Conclusion (3) is a valid general
incidence fact but its antecedent cannot occur in this boundary case.
Any exclusion must additionally use the finite replacement crowns,
ordinary top adjacency, or further magma information. The graph and
matching conclusions above by themselves do not exclude this case.
