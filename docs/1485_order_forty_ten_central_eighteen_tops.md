# Ten central elements and eighteen tops: balanced excess and sparse internal edges

Research note, 20 September 2026. The reductions below are analytic
necessary conditions for a finite E1485 magma. No Lean declaration or
finite-check premise is used. The auxiliary-support argument in §5
has been independently audited and excludes the degree-class split
`(|A|,|B|)=(8,4)`.

**This branch is now completely excluded** by the shorter
[ten-central-element proof](1485_order_forty_ten_central_exclusion.md).
The present note preserves independent quantitative bounds; none of
its excess calculations is needed for that final proof.

Assume order forty, minimum degree four, `|Z|=10`, and `|T|=18`.
By the [full-block theorem](1485_order_forty_ten_central_full_blocks.md),
all central predecessor and successor blocks `P_v,C_v` have sizes at
most three. The other degree classes are `A` of degree five and `B`
of degree eight; put `a=|A|`, `b=|B|`. The
[first-output reduction](1485_order_forty_four_central_exclusion.md#4-precisely-what-remains-at-order-forty)
gives four top neighbors and one sharp `B` neighbor in each direction
at every member of `A`. In particular `a+b=12`.

## 1. Top counts balance at every degree-eight vertex

At every vertex, its top predecessor blocks partition ten labels;
since their sizes are at most three, it has at least four top
predecessors. The dual statement holds for successors.

For `x∈B`, let `I,O` count top predecessors and successors, and
`j^-,j^+` count sharp `A` predecessors and successors. All its other
neighbors lie in `B`. The reciprocal-neighbor balance gives

\[
3(j^+-j^-)=O-I.
\tag{1}
\]

Sharp-neighbor existence and degree eight imply `4≤I,O≤7`.
The only possible unequal values permitted by (1) are four and
seven. On the seven-top side there is exactly one sharp neighbor;
(1) would give zero sharp neighbors on the other side. Thus

\[
I=O=t_x,\qquad j^-=j^+=j_x\ge1,
\qquad k_x=8-t_x-j_x\ge0.
\tag{2}
\]

Here `k_x` is the common number of internal `B` neighbors in either
direction. In particular the internal adjacency graph on `B` is
Eulerian, allowing loops. Counting sharp edges gives `Σ_B j_x=a`.

Define its total top-count excess by

\[
E=\sum_{x\in B}(t_x-4).
\tag{3}
\]

## 2. Central partitions force at least four units of excess

Every central row contains four tops, and their top-successor counts
sum to eighteen. Since each summand is at least four, every top's
number of top successors is between four and six. Write it as
`4+δ_v`, where `0≤δ_v≤2`. Each central row has sum of these
excesses two. Therefore

\[
\sum_{v\in T}|P_v|\delta_v=20.
\tag{4}
\]

Counting all edges whose endpoint is top gives `10·18=180`.
Central vertices contribute forty outgoing such edges, members of
`A` contribute `4a`, members of `B` contribute `4b+E`, and tops
contribute `72+Σ_Tδ_v`. Since `a+b=12`,

\[
\sum_{v\in T}\delta_v=20-E.
\tag{5}
\]

The predecessor-block defect sum is
`Σ_T(3−|P_v|)=3·18−4·10=14`. Using `δ_v≤2` in (4)–(5),

\[
40-3E
=\sum_{v\in T}(3-|P_v|)\delta_v
\le 2\sum_{v\in T}(3-|P_v|)=28.
\]

Thus `E≥4`. Conversely (4) and `|P_v|≤3` give
`20≤3(20−E)`, so the integer bound is

\[
\boxed{4\le E\le13.}
\tag{6}
\]

The dual argument gives the same result using successor blocks and
top-predecessor excesses. No pointwise equality of the two excesses
at a **top** vertex is asserted.

## 3. An initial list of three degree-class splits

Summing (2), the number of directed internal `B` edges is

\[
K=\sum_{x\in B}k_x=4b-a-E.
\tag{7}
\]

Since every `j_x≥1`, we have `a≥b`, hence `a≥6`. Since `K≥0`
and `E≥4`,

\[
4\le4b-a=48-5a,
\]

giving `a≤8`. Consequently

| Degree-five count `a` | Degree-eight count `b` | Allowed excess from these bounds | Internal `B` edges |
| ---: | ---: | ---: | ---: |
| 6 | 6 | `4≤E≤13` | `K=18−E`, hence `5≤K≤14` |
| 7 | 5 | `4≤E≤13` | `K=13−E`, hence `0≤K≤9` |
| 8 | 4 | `4≤E≤8` | `K=8−E`, hence `0≤K≤4` |

These are necessary ranges, not constructions. In particular the
last branch has a balanced directed graph on four vertices with at
most four edges. Section 5 excludes it without enumerating those graphs.

## 4. A quantitative good-pair bound that does not balance individual edges

Let `g_x` count ordered top pairs whose product is `x∈B`, and let
`η(x,y)` count bad internal predecessor paths on an internal edge
`x→y`. The right fiber `R_y^{-1}(x)` has five elements, of which
`8−t_x−η(x,y)` are non-top. It has `t_x−3+η(x,y)` top inputs.
Summing the four-element left fibers over the `t_x` top predecessors
of `x` therefore gives

\[
g_x=t_x(t_x-4)+3k_x-\sum_{y:x\to y}\eta(x,y).
\tag{8}
\]

The global last sum counts bad internal two-edge paths. Grouping them
by their first vertex bounds it by `Σ_x j_xk_x`, just as in the
[uniform-top-count argument](1485_order_forty_uniform_top_counts.md#2-count-bad-paths-globally-not-edge-by-edge).
Grouping by their middle also bounds it by `Σ_x k_x²`. In particular,
putting `e_x=t_x−4`, (8) yields

\[
\sum_{x\in B}g_x
\ge 10b-4a+
\sum_{x\in B}\bigl((j_x-1)(j_x-2)+e_x(e_x+j_x+1)\bigr)
\ge10b-4a+3E.
\tag{9}
\]

Only equality of the global bad-path totals is used. No equality of
bad predecessor and successor counts on an individual edge is needed.
The resulting necessary top-pair budget is

\[
324\ge160+12a+\sum_{x\in B}g_x.
\]

This budget does not by itself exclude any of the three splits in §3.

## 5. Auxiliary support excludes eight degree-five and four degree-eight elements

Let `N` be the number of ordered top pairs whose product is top, and
define the weighted count

\[
Q=\sum_{u,v\in T,\ u*v\in T}|C_v|.
\tag{10}
\]

This is the total number of top-to-top edges in the auxiliary
relations `B_z`, summed over all central parameters `z`. Indeed
`B_z(u)=u*Col(z)`, and the map `v↦u*v` on the four-element
`Col(z)` is injective. Thus each top input `v` giving a top output
contributes once for each `z∈C_v`. In particular `Q≥N`.

Fix a central parameter `z`, and let `J_z` be its number of auxiliary
top-to-top edges. The relation `B_z` is four-regular. Its top-to-central
edges number forty. Its top-to-`A` edges number `3a`, because each
`A` vertex has one sharp incoming `B` edge and three auxiliary top
predecessors. Therefore its top-to-`B` edges number
`4·18−40−3a−J_z`. Subtracting these and the `a` sharp incoming
`A` edges from the `4b` edges ending in `B` leaves

\[
\#\{\text{internal }B_z\text{ edges}\}
=4b+2a-32+J_z=16-2a+J_z.
\tag{11}
\]

For an ordinary internal edge `x→y`, write
`H_xy={z∈Z:x B_z y}`. The top inputs of `R_y^{-1}(x)` have
`P` blocks which partition `H_xy`, by the
[two-sided auxiliary identity](1485_unrestricted_central_incidence.md#the-auxiliary-relation-is-two-sided).
There are `s=1+e_x+η(x,y)` such inputs. Their blocks are a subset
of the `t_x=4+e_x` nonempty blocks partitioning `Z` at `x`.
The omitted blocks therefore give the bound

\[
|H_{xy}|\le10-(t_x-s)=7+\eta(x,y).
\tag{12}
\]

Let `τ` count all bad internal two-edge paths. Summing (11)–(12),
and using `Q≥N`, gives

\[
10(16-2a)+N\le10(16-2a)+Q
=\sum_{x\to y\text{ in }B}|H_{xy}|\le7K+\tau.
\tag{13}
\]

On the other hand (8) and the exact top-pair count give

\[
N=164-12a-\sum_{x\in B}(4+e_x)e_x-3K+\tau.
\tag{14}
\]

Substituting (14) in (13) cancels the unknown bad-path count `τ`.
Using `K=48-5a-E` yields the new necessary inequality

\[
\boxed{18a+\sum_{x\in B}e_x(6-e_x)\le156.}
\tag{15}
\]

Suppose `a=8`. Then the sum in (15) is at most twelve. But
`0≤e_x≤3`, so `e_x(6-e_x)≥3e_x`, with equality only for
`e_x∈{0,3}`. By (6) this gives

\[
12\ge\sum_x e_x(6-e_x)\ge3E\ge12.
\]

Equality would force `E=4` and every summand `e_x` to be zero or
three, an impossibility. Thus `a=8,b=4` is excluded. No bound on
individual bad predecessor/extension equality, and no classification
of the at-most-four-edge graph, was needed.

Consequently the only splits not excluded by this note are

\[
\boxed{(|A|,|B|)=(6,6)\quad\text{or}\quad(7,5).}
\]

The subsequent [ten-central-element proof](1485_order_forty_ten_central_exclusion.md)
excludes both using the supports of top-to-`A` edges and central
partitions, without further internal-graph analysis.
