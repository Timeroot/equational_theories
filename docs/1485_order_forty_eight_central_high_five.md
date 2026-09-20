# Eight central elements force at most ten degree-five elements

Research proof, 20 September 2026. This is an independently audited
analytic necessary condition, not a complete exclusion of the
eight-central-element branch or a Lean theorem. No enumeration or
SAT premise is used.

**Theorem.** In a finite E1485 magma of order forty, minimum degree
four, and eight central elements, the degree-five class has size

\[
\boxed{|A|\le10.}
\]

Write `Z,T,A,B` for the degree classes `4,10,5,8`, and put
`h=|T|`, `a=|A|`, `b=|B|`. The
[full-block theorem](1485_order_forty_ten_central_full_blocks.md)
gives `1≤|P_u|,|C_u|≤3` for every top `u`.
Every member of `A` is a first noncentral top output, with common
top-profile size three or four. Let `q` count those of size three;
the others have size four. Their sharp `B` degrees are respectively
two and one. If `α_u=#(Row(u)∩A)`, then

\[
\sum_{u\in T}\alpha_u=3q+4(a-q)=4a-q.
\tag{1}
\]

## 1. Central-parameter capacity excludes twelve degree-five elements

Suppose `u→x`, with `u∈T` and `x∈A` of top-profile size
`t∈{3,4}`. The four-element fiber `L_u^{-1}(x)` contains all
`5−t` sharp non-top successors of `x` and exactly `t−1` of its
`t` top successors. The latter's `C` blocks partition `Z`.
Thus the central support of the auxiliary edge `u B_z x` is
`Z` minus one omitted block and has size at least `8−3=5`.

As in the [ten-central proof](1485_order_forty_ten_central_exclusion.md#1-a-top-to-degree-five-edge-uses-at-least-seven-central-parameters),
all `|C_u|` sharp central successors consume auxiliary slots for
every parameter. Four-regularity therefore gives

\[
5\alpha_u\le8(4-|C_u|).
\]

For `|C_u|=1,2,3`, the integer upper bounds for `α_u` are
respectively `4,3,1`. Dual bounds apply to `A` predecessors
using `P_u`.

In every central row the `α` values sum to `a`, by unique goodness
at a central endpoint. The possible block-size patterns give

| Central row's `C`-block sizes | Maximum sum of `α` |
| --- | ---: |
| `3311` | 10 |
| `3221` | 11 |
| `2222` | 12 |

Thus `a≤12`. If `a=12`, every central row must be `2222`, so
every `C` block has size two. The dual argument gives the same
for `P`. Their size sum is thirty-two, hence `h=16`.
Every vertex's top blocks partition eight labels into size-two
parts, giving four top neighbors in either direction. The
[uniform-top-count theorem](1485_order_forty_uniform_top_counts.md)
would force `|Z|≤6`, a contradiction. It remains to exclude `a=11`.

## 2. Eleven degree-five elements give two small central partitions

Suppose `a=11`. Central rows can only be `3221` or `2222`.
The `α` values in the first case are `1,3,3,4`; in the second
they are three threes and one two. Consequently singleton `C`
blocks have `α=4`, size-three blocks have `α=1`, and size-two
blocks have `α=2` or `3`.

Let `n_i` count tops with `|C_u|=i`, and set

\[
R=\{u\in T:|C_u|=2,\ \alpha_u=2\}.
\]

Every central row contains either exactly one singleton-`C` top
and no member of `R`, or exactly one member of `R` and no
singleton-`C` top. Therefore the `P` blocks indexed by

\[
R\ \cup\ \{u:|C_u|=1\}
\]

partition `Z`. Write their number as `ℓ=|R|+n_1`; then
`3≤ℓ≤8`. Since `Σ|C_u|=32`, (1) gives

\[
44-q=4n_1+3n_2+n_3-|R|=5h-32-n_3-|R|.
\]

Also `n_1-n_3=2h-32`, so

\[
\boxed{\ell=7h-108+q,\qquad3\le\ell\le8.}
\tag{2}
\]

With `0≤q≤11`, this excludes `h≤14` and `h≥17`; thus
`h∈{15,16}`. Apply the same argument in the opposite magma.
If `R'` denotes the tops of predecessor-block size two with exactly
two predecessors in `A`, its `C` blocks together with those of all
singleton-`P` tops form another `ℓ`-block partition of `Z`.

## 3. A mixed moment bounds the size of these partitions

Write `n_pc` for the number of tops of central type `(p,c)`, and put

\[
c=n_{11},\qquad l=n_{13},\qquad d=n_{31}.
\]

Let `x` count the type-`(1,2)` members of `R`, and `y` the
type-`(2,1)` members of `R'`. Any `ℓ`-block partition of eight
has at least `2ℓ−8` singleton parts. For the two partitions above
these counts are exactly `c+x` and `c+y`, giving

\[
c+x\ge2\ell-8,\qquad c+y\ge2\ell-8.
\]

The first partition contains the `x` specified members of `R`
and all singleton-`C` tops, including the `c` type-`(1,1)` tops,
the `y` specified type-`(2,1)` tops, and all `d` type-`(3,1)` tops.
These sets are disjoint. Hence

\[
\ell\ge x+y+c+d\ge4\ell-16-c+d,
\qquad c-d\ge3\ell-16.
\tag{3}
\]

The central incidence moments `Σ|P|=Σ|C|=32`, `Σ|P||C|=64`
give

\[
c+n_{33}-l-d=\sum(|P|-2)(|C|-2)=4h-64.
\]

Combining this with (3), and noting that each size-three part uses
two units above the minimum of one per block, gives

\[
\boxed{3\ell+48-4h\le l
\le\left\lfloor\frac{8-\ell}{2}\right\rfloor.}
\tag{4}
\]

For `h=15`, (4) excludes `ℓ≥5`; thus `ℓ∈{3,4}`.
For `h=16`, it excludes `ℓ≥6`; thus (2) leaves `q∈{0,1}`.

If `h=15,ℓ=4`, both partitions have at most two size-three
parts, so `n13,n31≤2`. The mixed moment then forces
`n13=n31=2` and `n11=n33=0`. In the first partition the two
type-`(3,1)` tops cover six labels. Its other two parts are singleton
`P` blocks, necessarily at type-`(1,2)` members of `R`.
The dual partition similarly gives two type-`(2,1)` members of `R'`.
But the first partition contains these two members of `R` and all
four specified singleton-`C` tops of types `(3,1)` and `(2,1)`:
six distinct tops in a four-block partition. This is impossible.

Thus the only cases still to check are `h=15,q=6`, from `ℓ=3`,
and `h=16,q∈{0,1}`.

## 4. Weighted top pairs exclude the last three cases

Let `F` count ordered top pairs whose product belongs to `B∪T`.
Central products account for 128 pairs, while each degree-five output
accounts for six or twelve according as its top-profile size is
three or four. Therefore

\[
F=h^2-128-12a+6q.
\tag{5}
\]

For a fixed central parameter, the four-regular auxiliary relation
has `4h` outgoing edges from `T`. Thirty-two end in `Z`, and
`3a−q` end in `A`: each size-three-profile `A` vertex has two
auxiliary top predecessors, and each size-four-profile vertex has
three. The remaining predecessors are precisely its sharp `B`
predecessors. Hence the total auxiliary edges `T→B∪T`, summed
over all eight parameters, number

\[
W=8(4h-32-3a+q).
\tag{6}
\]

Each top pair `u,v` with output in `B∪T` contributes exactly
`|C_v|` to this count, because multiplication by `u` is injective
on each central column. Consequently

\[
F\le W\le3F.
\tag{7}
\]

At `a=11,h=15,q=6`, (5)–(6) give `F=1,W=8`, contradicting
(7). At `a=11,h=16,q=0`, (5) already gives the impossible
negative count `F=-4`. At `a=11,h=16,q=1`, they give `F=2,W=0`,
again contradicting (7). This excludes `a=11` and proves `a≤10`.

The proof does not exclude the remaining degree-class counts `a≤10`.
