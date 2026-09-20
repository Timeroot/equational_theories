# Order forty-eight with five central vertices and constant top profiles

Research note, 19 September 2026. This is an analytic conditional
restriction, not an exclusion of the entire order-48 branch and
not a Lean proof.

Assume `n=48`, `min d=4`, and `|Z|=5`. Suppose additionally
that **every vertex has four top predecessors and four top
successors**. Then

\[
\boxed{9\le |A_6|\le14,\qquad |B_8|=27-|A_6|.}       \tag{1}
\]

The central-moment parameter is necessarily `N22=1`: counting
ordinary edges into the top class gives `4·48=12|T|`, hence
`|T|=16`. This is the case of the five-central moment formula
with one double/double top.

## A central-block condition implying the hypothesis

In the `N22=1` case there are exactly four tops with double
central predecessor blocks and four with double central successor
blocks. Suppose the four double predecessor blocks have a common
central vertex `p`, and the four double successor blocks have a
common central vertex `c`; the two centers need not coincide.

There are exactly four tops in `Row(p)`, already supplied by
the four double predecessor blocks. Therefore no singleton
predecessor block is `{p}`. Give `p` weight zero and each other
central vertex weight one. Every top predecessor block then has
total weight one. Since the predecessor blocks of the top
predecessors of any vertex partition the five central vertices,
that vertex has exactly four top predecessors. The dual weighting
at `c` gives four top successors.

Thus (1) applies whenever both families of double blocks are
stars, allowing repeated edges. This covers the simple product
tilings and nearby tilings, but is not asserted for arbitrary
five-central incidence.

## 1. Degree-class and sharp counts

The occurring degrees are `4,6,8,12`. Write `A,B` for the
degree-six and degree-eight classes and `a=|A|`, `b=|B|`.
Every member of `A` has exactly two sharp predecessors and
successors, all in `B`. For `x∈B`, reciprocal-neighbor balance
makes its sharp in- and out-counts equal; denote the common
count by `j_x`. Its ordinary internal `B` degree is `4−j_x`
in both directions. Thus

\[
a+b=27,\qquad 1\le j_x\le4,\qquad\sum_{x\in B}j_x=2a.
\]

The bounds `b≤2a≤4b` initially give `9≤a≤18`, hence `b≥9`.

Let `C_xy=1` mean there is a sharp two-step path `x⇒u⇒y`
through `A`. Every such path is good and has a unique middle.
The binary matrix `C` has row and column sums `2j_x`.

The [universal return matching](1485_general_return_matching.md)
applied to the independent class `A` gives

\[
x*y\in T\quad\Longrightarrow\quad j_x+j_y\le4.       \tag{2}
\]

## 2. Sharp count four and sixteen degree-six vertices are impossible

If `j_x=4`, the vertex `x` has no internal `B` successors.
Its four sharp `A` successors give at most eight two-step
endpoints in `B`. Since `b≥9`, some product `x*y` must be
top; it cannot be central, and no ordinary middle in `A∪B`
reaches this endpoint. This contradicts (2). Thus `j_x≤3`
for every `x`, so `2a≤3b=3(27−a)` and `a≤16`.

If `a=16`, then `b=11` and the sharp-count sum is 32.
Writing `n_i` for the number of vertices with `j=i`, we get
`n_3−n_1=10` and `n_1+n_2+n_3=11`. Therefore `n_1=0`,
`n_2=1`, and `n_3=10`.

A sharp-count-three vertex has three sharp `A` successors and
one internal `B` successor. Since every sharp count is at least
two, these give at most `6+2=8` two-step endpoints in `B`.
Some product is therefore top, but (2) would require its other
endpoint to have sharp count at most one. This contradiction
excludes `a=16`.

## 3. Fifteen forces an odd number of sharp edges in a double block

Suppose `a=15`, so `b=12` and the sharp-count sum is 30.
Then `n_3−n_1=6`, whence `n_1≤3`.

For a sharp-count-three vertex, its sharp `A` successors and
one internal `B` successor give at most `6+3=9` endpoints in
`B`. There are at least three top-return partners. By (2),
each has sharp count one. Consequently

\[
n_1=3,\qquad n_2=0,\qquad n_3=9.
\]

Let `L` be the three low-sharp vertices and `H` the nine
high-sharp vertices. The same argument shows that every member
of `H` has top product with every member of `L`. Its dual
gives the reverse products. Hence

\[
C_{H,L}=C_{L,H}=0.                                  \tag{3}
\]

Each `u∈A` has two sharp predecessors and two sharp successors
in `B`, producing a complete `2×2` rectangle in `C`. By (3),
this rectangle must lie entirely in `H×H` or entirely in `L×L`.
Indeed a mixed predecessor set would force all successors into
both disjoint classes, and a mixed successor set is excluded
dually.

Counting sharp edges out of `H` now gives

\[
27=9\cdot3
  =2\,\#\{u\in A:\text{its sharp rectangle lies in }H\times H\},
\]

which is impossible by parity. Thus `a=15` is excluded as well,
proving (1). No central-tiling enumeration or operation search is
used in this argument.
