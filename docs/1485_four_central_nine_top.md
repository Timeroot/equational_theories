# Four central and nine top vertices: incidence and least-degree restrictions

Research note, 18 September 2026. The proofs in this note are analytic
pen-and-paper arguments, not an exclusion of the entire nine-top
branch. No enumeration or solver result is a premise of these proofs.
The separately linked complete degree-five exclusion retains its
explicit finite incidence lemma.

Suppose a finite E1485 magma has minimum translation degree three,
four central vertices `Z`, and nine top vertices `T`. The
[central-degree reduction](1485_four_central_full_entry.md) gives
four top vertices of type `(1,1)`, two of type `(1,2)`, two of
type `(2,1)`, and one of type `(2,2)`, where the coordinates count
central predecessors and successors.

Write `P_t,C_t⊆Z` for these predecessor and successor sets.
Central endpoint uniqueness says that the nine rectangles `P_t×C_t`
partition `Z×Z`. They consist of one `2×2` rectangle, two
horizontal dominoes, two vertical dominoes, and four singletons.
Uniqueness of central middles also gives

\[
|C_u\cap P_v|\le1\qquad(u,v\in T).               \tag{1}
\]

**Theorem.** It is impossible that all three size-two predecessor
sets are one fixed pair `A` and all three size-two successor sets
are one fixed pair `B`.

These are only the two constant-pair rectangular subcases. The
other possible incidence configurations remain separate.

## 1. The resulting rectangle partition

By (1), `A≠B`, so these pairs are either disjoint or intersect
in one point. The unique `(2,2)` top supplies `A×B`.
The two horizontal dominoes are the two rows outside `A`, each
with successor pair `B`. The vertical dominoes are the two columns
outside `B`, each with predecessor pair `A`. The four remaining
tops are the singleton cells of `(Z\A)×(Z\B)`.

Thus all singleton predecessor labels lie outside `A`, and all
singleton successor labels lie outside `B`. Central rows at the
two members of `A` coincide, and central columns at the two
members of `B` coincide.

## 2. Disjoint pairs give the binary obstruction

Suppose `B=Z\A`. A successor pair `B` meets every singleton
predecessor label and avoids the predecessor pair `A`. A singleton
successor label lies in `A`, so it meets the predecessor pair and
avoids all singleton predecessor labels. Consequently the central
product matrix is a binary opposite-type matrix:

\[
u*v\in Z\quad\Longleftrightarrow\quad
(|C_u|=2)\ne(|P_v|=2).
\]

For any vertex, its top predecessor sets partition `Z` by their
`P` labels. Such a partition must use one pair `A` and the two
singleton labels outside `A`, so it has exactly three members.
The dual statement gives three top successors.

The [binary top-type theorem](1485_binary_top_types.md) therefore
forces full core, contradicting the central cardinality four.

## 3. Intersecting pairs violate the finite parameter rank bound

Suppose `|A∩B|=1`, and put `S=A∪B`, of size three. The
row-sharing edge joining the two members of `A` and the column-sharing
edge joining the two members of `B` connect all of `S`.
Consequently all auxiliary relations `B_h`, `h∈S`, coincide.

Here is a useful partial version of the
[central-parameter rank criterion](1485_central_parameter_components.md).
Whenever the parameters in a central set `S` give the same auxiliary
relation, put

\[
U=\bigcup_{h\in S}Row(h),\qquad
V=\bigcup_{h\in S}Col(h).
\]

Then

\[
\boxed{V*U\subseteq Z.}                          \tag{2}
\]

Indeed, for `c∈Col(k)` with `k∈S` and any `h∈S`, parameter
equality gives `a*c∈B_k(a)=B_h(a)` for every `a`. Therefore
`(h*a)*(a*c)=a`. The finite mixed-coordinate rank formula gives
`c*Row(h)⊆Z`. Taking the unions proves (2).

In the present incidence configuration, `|U|=|V|=6`. The common
central row at `A` has three tops; the row at the sole member of
`B\A` supplies three additional tops. Dually the common central
column at `B` and the column at `A\B` supply six distinct tops.

For every `c∈V`, (2) gives six central-valued products in row
`c` of the top-product matrix. Its complete row has exactly
`3|C_c|` central-valued entries, by central incidence. Since
`|C_c|≤2`, we must have `|C_c|=2` for all six members of `V`.
But only three top vertices have central out-degree two. This
contradiction excludes the intersecting-pair case as well.

Consequently a surviving nine-top case cannot have both a pair of
equal central rows and a pair of equal central columns. Indeed equal
rows must be the two rows of the unique `2×2` rectangle, forcing
all three double predecessor sets to coincide. Equal columns force
all three double successor sets to coincide in the same way.

## 4. A small top neighborhood requires complementary pairs

The following additional necessary conditions do not require the
constant-pair hypothesis of the theorem above.

Every top successor set partitions `Z` by the central successor
sets of its members. Since these sets have size one or two, a top
vertex has two, three, or four top successors.

If a top vertex `v` has central in-degree two, it cannot have only
two top successors. Its missing top-input column has three inputs,
whose predecessor sets partition `Z` with sizes `2,1,1`; this
follows from `BF=1(3-k⁻)ᵀ`, with `F=J-CB`. For a missing input
`u`, the E1485 witness set

\[
S_u=\{v*z:z\in P_u\}\subseteq TopSucc(v)
\]

has size `|P_u|`, and `(u*v)*b=v` throughout `S_u`.
With only two successors, the double input witnesses both of them.
Each corresponding fiber `R_b⁻¹(v)` has three elements, including
the two central predecessors of `v`, so it has only one noncentral
input. Both singleton-input products must therefore equal the
double-input product. Three equal top inputs in `R_v` are
impossible for a noncentral output, since its three-element fiber
also contains a non-top sharp predecessor.

Now suppose `v` has central in-degree one and exactly two top
successors. Its six missing inputs have predecessor sizes
`2,2,1,1,1,1`, again by the column of `BF`. Both double inputs
witness both successors. If their two products differed, they would
use up both noncentral slots in each corresponding fiber at `v`.
All four singleton-input products would have to equal one of them,
but each noncentral value admits at most two top inputs: the two
double inputs leave room for only two additional inputs, not four.
Thus the two double inputs have a common value `a`.

They give `a*b=v` for every `b∈TopSucc(v)`. Taking `b=v*z`
for each central `z`, the dual weak central law gives
`(z*a)*v=a`. Since `Z*a=TopPred(a)`, all top predecessors of
`a` lie in its fiber under `R_v`. That fiber already contains the
two double inputs and a non-top sharp predecessor. Those two inputs
are therefore exactly `TopPred(a)`, so their central predecessor
pairs partition `Z`.

We have proved that a top row of size two requires two complementary
pairs among the three double predecessor sets. In particular, if no
such complementary pair occurs, every top row has size at least
three. The weighted identity

\[
36=\sum_{t\in T}|P_t|\,|TopSucc(t)|,\qquad
\sum_{t\in T}|P_t|=12
\]

then forces every top row to have size exactly three. The dual
statement uses the double successor sets and top columns. These
conditions alone do not exclude the remaining incidence cases.

There is also a global consequence in the opposite incidence
direction. If the double predecessor pairs contain no complementary
pair, every vertex has at least three top predecessors, since their
predecessor-label sets partition `Z` and no two of them cover it.
The total number of top-to-vertex edges is
`|T|s=9s=3n`, so their average is three. Every vertex consequently
has exactly three top predecessors. Dually, absence of complementary
double successor pairs gives exactly three top successors at every
vertex. When both absences hold, the all-vertices top-neighborhood
hypothesis of the binary theorem is available, although its binary
matrix hypothesis need not hold.

## 5. No sharp-regular least-degree-five vertices

Suppose five is the least noncentral degree, and let `a` be a
degree-five vertex with sharp degree three. Its top predecessor
profile `U` and successor profile `V` each have size two. Every
top translation fiber at `a` is already filled by its three sharp
inputs, so there is no top-top product with value `a`. Minimality
of degree five then makes every pair in `U×V` have a central
good middle: its bad path through `a` must have a lower-degree
replacement. Thus `K[U,V]` is the all-one `2×2` matrix.

Both members of `U` have double predecessor sets, and both members
of `V` have double successor sets. There is only one top with both
sets double. Consequently at least one `u∈U` has singleton
successor set `C_u={z}`. But central row `z` contains exactly
one top with a double successor set: its three successor-set sizes
sum to four. At most one of the two members `v∈V` can therefore
have `z∈P_v`. The corresponding row of `K[U,V]` has at most
one entry, a contradiction.

This is an analytic exclusion independent of the total order and
number of other degree classes. More generally, no vertex with
two top neighbors in each direction can have all four endpoint
pairs centrally valued. The separate
[degree-five exclusion](1485_four_central_degree_five.md) combines
this fact with a small explicit finite profile lemma to rule out
least noncentral degree five altogether in this nine-top branch.

## 6. Least degree six is sharp-regular

Suppose instead that six is the least noncentral degree. Its sharp
count `k` and top-neighbor count `t` satisfy `t+k=6`, with
`2≤t≤4` and `1≤k≤3`. The only possibilities are `(t,k)=(3,3)`
and `(4,2)`.

The latter is impossible. Its top predecessor profile `U` has four
singleton predecessor labels, and at least two members of `U` have
singleton successor sets, since only two tops have profile `(1,2)`.
Its four top successors `V` all have singleton successor labels.
Every central row contains exactly one top with a double successor
set and two with singleton successor sets. Thus, for any central
label `z`, at most two members of `V` have `z` in their predecessor
sets. A member `u∈U` with `C_u={z}` consequently has at most
two central middles to `V`.

But a least-degree-six vertex requires its `U×V` central-middle
matrix to have constant row sum `6−3=3`: every top fiber has its
two sharp inputs and one good top input. This is a contradiction.
Thus every degree-six vertex has three top neighbors and three sharp
neighbors in both directions, and none is a top-top product.

## 7. Seven cannot be the least noncentral degree

Let `q` be the least noncentral degree. Its sharp count is at most
three and its top-neighbor count is at most four, so `q≤7`.
If `q=7`, those counts must be `k=3` and `t=4`.
The central-middle matrix on its two four-element top profiles would
therefore have every row and column sum `q−3=4`: it would be
entirely one.

But the same singleton argument from §6 applies. At least two of
the four predecessor tops have singleton central successor sets.
For each such row, at most two of the four successor tops admit a
central middle, because each central row has only two tops with
singleton successor sets. The row sum cannot be four.

Thus seven is impossible as the least noncentral degree. Combined
with the separate finite-assisted degree-five exclusion, this leaves
only least noncentral degrees four and six in the nine-top branch.
