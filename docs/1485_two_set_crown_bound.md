# Exact crown intersections of sets of size at most two

Research note, 19 September 2026. This elementary finite-set lemma
is independent of E1485. Its application is recorded in the
[one-extra-central-vertex note](1485_one_extra_central_first_output_gap.md).

Let `(A_i,B_i)`, for `i=1,...,k`, be pairs of finite sets satisfying

\[
|A_i|,|B_i|\le2,\qquad A_i\cap B_i=\varnothing,
\qquad |A_i\cap B_j|=1\quad(i\ne j).                \tag{1}
\]

Their intersection matrix is the crown matrix `J_k−I_k`.

**Theorem.** If `k≥4`, every set has size exactly two. Always
`k≤5`. Equality five is attained, and necessarily has the pentagon
form described below, up to relabeling and unused ground elements.

## 1. A singleton permits at most three pairs

Suppose `k≥4` and `A_1={a}`. For every `j>1`, the set `B_j`
contains `a`. It cannot equal `{a}`: choosing `i` distinct from
`1,j` would force `a∈A_i`, contrary to `A_i∩B_i=∅`.
Thus write `B_j={a,b_j}`.

The elements `b_j` are pairwise distinct. For `i,j>1` with
`i≠j`, the set `A_i` avoids `a,b_i` and must contain `b_j`.
Consequently it contains `k−2` distinct elements, giving `k≤4`.
At `k=4`, the three sets `A_2,A_3,A_4` are exactly the three
two-element subsets of `{b_2,b_3,b_4}`. But then

\[
\sum_{i=2}^4|A_i\cap B_1|
=2|B_1\cap\{b_2,b_3,b_4\}|
\]

is even, whereas (1) makes it three. This is a contradiction.
Empty sets are impossible when `k≥2`. The dual argument excludes
singleton `B_i`, proving the first assertion.

## 2. The graph of the first sets

It remains to bound `k` when `k≥4`, so every set has size two.
Regard the `A_i` as edges of a graph `G`. They are distinct:
equality `A_i=A_j` would contradict the diagonal and off-diagonal
intersection requirements against `B_i`. Thus `G` is simple.

For each edge `e=A_i`, the two vertices of `B_i` avoid both
endpoints of `e`. Every other edge has exactly one endpoint in
`B_i`. In particular `G−e` is bipartite, with parts `B_i` and
its complement.

If `G` has an odd cycle, every edge lies on that cycle: deleting
an edge outside it could not make the graph bipartite. Thus `G`
is exactly one odd cycle, apart from isolated vertices. The two
vertices of `B_i` cover its other `k−1` edges and each has degree
at most two. Therefore `k−1≤4`.

If `G` is bipartite, it has no cycle. Indeed an edge `e` on an
even cycle would be the only edge of that cycle not crossing the
cut `B_i`; equivalently, the odd-length path obtained by removing
`e` would have its two endpoints on the same side. This is
impossible. Hence `G` is a forest.

Every vertex has degree at most three. For an edge `e=vx`, the
set `B_i` avoids `v,x` and must contain every other neighbor of
`v`, of which there are therefore at most two.

If a vertex `v` has three neighbors `x,y,z`, the edge `vx`
forces `B_i={y,z}`. Any further neighbor of `x` would have to be
`y` or `z` to make its edge cross this cut, creating a cycle.
Thus `x` is a leaf, and the same holds for `y,z`. Their component
is a three-edge star. Its two leaves `y,z` cannot meet any edge
in another component, so in this case `G` has only three edges.

Otherwise the forest has maximum degree at most two. The two
vertices of `B_i` cover at most four edges, giving `k−1≤4`
again. This proves `k≤5`.

## 3. Equality five is the pentagon

A forest with five edges cannot attain equality. If it has a path
component with at least two edges, choose the second edge from a
leaf. The corresponding set `B_i` must contain that leaf to meet
the first edge. It can then cover at most `1+2=3` other edges,
rather than the required four. If every component is an isolated
edge, two vertices cover at most two other edges. Both possibilities
are impossible.

Thus equality requires `G` to be the five-cycle. Label its edges

\[
A_i=\{i,i+1\}\qquad(i\in\mathbb Z/5\mathbb Z).
\]

The only two vertices avoiding `A_i` and meeting every other
cycle edge exactly once are

\[
B_i=\{i+2,i+4\}.
\]

These pairs satisfy (1), so the bound five is sharp. In biclique
language, `J_5−I_5` partitions into five `2×2` rectangles.
In particular, a proposed stronger universal bound of four would
be false.
