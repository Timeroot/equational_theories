# Top profiles at the first degree above the minimum

Research note, 20 September 2026. These are analytic finite E1485
restrictions, not Lean declarations. They do not exclude a first
noncentral top-product degree of five at minimum degree four.

Write `r=min d`, `Z` for the central class, `m=|Z|`, and `T`
for the top class. For a top vertex `v`, put

\[
P_v=Col(v)\cap Z,\qquad C_v=Row(v)\cap Z.
\]

Suppose the first noncentral top-product degree is `p=r+1`,
and let `a` be such a top product. The
[first-output theorem](1485_first_top_output_fibers.md) gives top
profiles `U=TopPred(a)`, `V=TopSucc(a)` of equal size `t`, with

\[
2\le t\le r.
\]

The matrix

\[
K_{uv}=|C_u\cap P_v|\qquad(u\in U,\ v\in V)
\]

is a permutation matrix, since its row and column sums are `p-r=1`.
Its complement is the good top-product graph with middle `a`.

## A general bound from the two central partitions

For any vertex `x`, not necessarily of first-output degree, the
sets `P_u` with `u∈TopPred(x)` partition `Z`. Indeed each central
`z` has a unique good top middle on the path from `z` to `x`.
Dually the sets `C_v` with `v∈TopSucc(x)` partition `Z`.

For any two tops `b,c`, central-middle uniqueness gives
`|C_b∩P_c|≤1`. Consequently, putting
`I=|TopPred(x)|` and `O=|TopSucc(x)|`,

\[
|C_b|\le I,\qquad |P_b|\le O\quad(b\in T),
\qquad\boxed{m\le IO.}                                  \tag{1}
\]

The first two bounds follow by intersecting a block with each part
of the opposite partition; summing `|P_u|≤O` over the `I`
predecessors proves the last bound. Equivalently, each central label
has a unique predecessor-block and successor-block coordinate, and
these coordinates inject `Z` into an `I` by `O` grid.

At our first output this gives

\[
|P_b|,|C_b|\le t\quad(b\in T),\qquad m\le t^2.
\]

If `r>1`, in fact `t²>r`. Otherwise `r≤m≤t²≤r` forces
`m=r`. The [minimal-central-count theorem](1485_minimal_central_count.md)
then makes every vertex have exactly `r` top neighbors in both
directions, so `t=r`; this contradicts `t²≤r` when `r>1`.

## A permutation central matrix forbids a one-vertex exchange

**Theorem.** Under the first-output hypothesis `p=r+1`,

\[
\boxed{|U\cap V|\ne t-1.}                                \tag{2}
\]

Suppose instead that `U=W∪{u}` and `V=W∪{v}`, where
`u≠v` and `|W|=t−1`. Write

\[
A=P_u,\quad E=C_u,\quad D=P_v,\quad B=C_v.
\]

The predecessor partition gives `⋃_{w∈W}P_w=Z∖A`,
and the successor partition gives `⋃_{w∈W}C_w=Z∖B`.
The submatrix `K[W,W]` is a partial permutation matrix. It has
either `t−1` or `t−2` ones: a full permutation matrix can have
at most two ones outside this submatrix.

If it has `t−1` ones, the remaining entry `K_{uv}` is one.
The zero entries `K_{uw}` and `K_{wv}` force
`E⊆A` and `D⊆B`, respectively. Thus a point of `E∩D`
lies in both `A∩D` and `E∩B`, so both intersections are nonempty.

If it has `t−2` ones, let `w` and `w'` be its unique empty
row and column. Then `K_{wv}=K_{uw'}=1`. The empty common
row says `C_w⊆A`, and the empty common column says `P_{w'}⊆B`.
Thus `C_w∩D≠∅` makes `A∩D≠∅`, and
`E∩P_{w'}≠∅` makes `E∩B≠∅`.

In either case choose `α∈A∩D` and `β∈E∩B`.
The distinct tops `u,v` would both be good middles from the central
vertex `α` to the central vertex `β`. Equivalently their central
rectangles `A×E` and `D×B` overlap. This contradicts uniqueness
of the product `α*β`, proving (2).

There is also an exact restriction at the other extreme:

\[
\boxed{U=V\quad\Longrightarrow\quad m=t=r.}                \tag{3}
\]

If `U=V`, both the `P`-blocks and the `C`-blocks indexed by
this set partition `Z`. Their intersection matrix therefore has
`m` ones in total. But it is the `t` by `t` permutation matrix
`K`, so `m=t`. Finally `m≥r` and `t≤r` force equality.

## Consequences at minimum four and degree five

Here `t` can initially be two, three, or four. Formula (1) and the
strict inequality `t²>r` exclude `t=2`. The surviving possibilities
therefore satisfy:

| Top-profile size | Necessary central data | Profile overlap |
| ---: | --- | --- |
| `t=3` | `5≤m≤9`; every central block has size at most three | `|U∩V|≤1` |
| `t=4` | `m≥4` | Either `U=V` and `m=4`, or `|U∩V|≤2` |

For the first row, `m=4` is excluded by the same minimal-central-count
theorem, which would force `t=4`; `m≤9` follows from (1).
The central labels embed in a three-by-three grid with coordinates
given by the `P_U` and `C_V` partitions. Formula (2) excludes
overlap two, and (3) excludes overlap three.

These restrictions hold independently of the total order. They do
not assert that any surviving grid extends to an E1485 magma, and
they do not yet eliminate either remaining profile size.
