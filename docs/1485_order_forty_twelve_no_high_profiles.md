# Order forty, twelve/eight: profile restrictions with no high-sharp partners

Research note, 20 September 2026. These analytic restrictions exclude
an empty predecessor line and all mixed-coset arrangements with predecessor
multiplicities `(4,4,3,1)`, including mixed `11+1`. **They do not exclude
the whole sharp distribution `(2^4,1^4)`.** No enumeration, SAT premise,
or affine-profile hypothesis is used. A separate
[checked finite incidence proof](1485_order_forty_twelve_thin_exclusion.md)
now excludes **all** predecessor multiplicities `(4,4,3,1)`, without
assuming a single successor coset. Its computational dependency is
separate from the analytic reductions on this page. The remaining
predecessor patterns are `(4,4,2,2)`, `(4,3,3,2)`, and `(3,3,3,3)`.
The subsequent [all-mixed exclusion](1485_order_forty_twelve_mixed_exclusion.md)
combines Sections 9–11 below with five checked refutations, proving
that both profile families must use single cosets. The analytic
sections retain their separate mathematical scope.

Let `M,L⊆B` be the four vertices of sharp degree two and the four
of sharp degree one, respectively. These names distinguish their sharp
degrees; every vertex of `B` has translation degree eight. Internal
adjacency `D` has row/column degrees two on `M` and three on `L`.
The sharp-path matrix `C` has row/column sums two on `M` and one
on `L`, and

\[
(D^2)_{bd}\ge2\quad\Longrightarrow\quad C_{bd}=1.       \tag{1}
\]

By the [large-class theorem](1485_min_four_large_five_class.md), after
taking the opposite operation if necessary, all twelve `A` predecessor
profiles are lines in one four-line partition `P`. Write `u_p` for
their multiplicities, with `0≤u_p≤4` and `Σu_p=12`. Each fixed
`P` line has all its successor-profile partners in one other coset.

## 1. At least three internal edges cross in each direction

Let `e` be the number of `D` edges from `L` to `M`. The number
from `M` to `L` is also `e`, since every vertex has equal internal
in/out degree.

Suppose `e≤2`. Some `b∈L` has no successor in `M`, because
there are four low-sharp rows. Its three successors lie in `L`.
Together they emit nine two-step paths from `b`; at most `e≤2`
of these end in `M`. Thus at least seven end in the four-element
set `L`.

By (1), only the unique endpoint in `C(b)` can be repeated. Its
multiplicity is at most three, since there are three possible middles.
Even if that endpoint lies in `L`, the four low-sharp endpoints can
accommodate at most `3+1+1+1=6` paths. This contradiction proves

\[
\boxed{|D\cap(L\times M)|=|D\cap(M\times L)|\ge3.}     \tag{2}
\]

Loops are allowed and cause no change to the count.

## 2. A non-affine sharp-degree-two successor profile has a rigid exceptional set

For `b∈M`, the product `b*a` with `a∈A` can have a non-top
middle only at the unique sharp predecessor `G(a)∈B` of `a`,
and that requires `bD G(a)`. There are two internal successors of
`b`, each with a `G`-fiber of size at most two. Thus at least
eight vertices of `A` satisfy

\[
|V_b\cap U_a|=1,\qquad V_b=\operatorname{TopSucc}(b).    \tag{3}
\]

A four-point set which is not a transversal of four disjoint lines
has exact-one intersection with at most two lines. Since each line
accounts for at most four `A` vertices, failure of `P`-transversality
forces equality throughout:

- Exactly two `P` lines have exact-one intersection with `V_b`,
  and both have multiplicity four.
- Exactly four `A` vertices fail (3).
- Both internal successors of `b` belong to `M`.
- Their two disjoint, two-element `G`-fibers are precisely those
  four exceptional vertices.

If `V_b` is a `P`-transversal, its other central-label transversality
makes the associated map a permutation of four labels. Every permutation
of `F₂²` is affine, so `V_b` is an affine plane.

In particular, if the `P` multiplicities do not contain two fours,
all four profiles `V_b`, `b∈M`, are affine transversals. This applies
to multiplicities `(3,3,3,3)` and `(4,3,3,2)`.

## 3. At most two sharp-degree-two successor profiles can fail transversality

Each non-transversal from §2 uses both of its internal outgoing edges
inside `M`. Three such vertices would use at least six of the total
eight outgoing `M` edges, leaving at most two edges from `M` to
`L`. This contradicts (2). Therefore

\[
\boxed{\#\{b\in M:V_b\text{ is not a }P\text{-transversal}\}\le2.}
\tag{4}
\]

This conclusion holds for all predecessor multiplicities and whether
the `A` successor profiles use one coset or two.

## 4. Odd mixed-coset populations force all four profiles to be affine

Suppose the `A` successor profiles use two cosets, and their population
counts are odd: `11+1`, `9+3`, or `7+5`, up to exchanging the names.
If some `b∈M` failed `P`-transversality, its eight non-exceptional
vertices from §2 would occupy two full `P` lines. Each such line
has all its successor partners in one coset, so its contribution to
each coset population is either zero or four.

The remaining four vertices are exactly two whole `G`-fibers of size
two. Profiles in one `G`-fiber are pairwise disjoint and therefore
lie in a single successor coset. Each fiber contributes zero or two
to each coset population. Both total populations would consequently
be even, a contradiction. Hence

\[
\boxed{\text{Odd mixed-coset populations force every }V_b, b\in M,
\text{ to be an affine }P\text{-transversal}.}          \tag{5}
\]

These statements leave genuine profile and incidence possibilities.
In particular they do not imply that the four sharp-degree-one profiles
are affine, or that all `A` successor profiles belong to one coset.

## 5. No predecessor line can be empty

This argument also applies to the previously excluded high-sharp
distributions, using only `1≤j_b≤3` on the eight members of `B`.
Suppose some `P` line `P_0` is not the predecessor profile of any
vertex of `A`. Put `m_b=|U_b∩P_0|`.

For `u∈U_b∩P_0` and `v∈V_b`, the path `u→b→v` has no
possible replacement in `A`: such a replacement would require
`u∈U_a`, and all `U_a` are other lines of the partition. By
strict degree descent, any bad pair must therefore have a central
replacement. Its central condition is equality of the adjacent central
labels of `u` and `v`.

The four-element fiber `L_u^{-1}(b)` already contains the `j_b`
sharp `A` successors of `b`. Thus at most `4−j_b` of the four
vertices in `V_b` can give good top pairs with `u`; at least `j_b`
give central-valued pairs. The relevant central labels of the distinct
points of `P_0` are distinct, because a `P` line is a permutation
transversal of the actual central grid. Their sets of matching vertices
in `V_b` are consequently disjoint. This proves

\[
j_bm_b\le4.                                             \tag{6}
\]

On the other hand, choose any internal edge `bDd`, which exists
because `4−j_b≥1`. The exact top return fiber

\[
T\cap R_d^{-1}(b)
=U_b\setminus\bigcup_{a:F(a)=d}U_a
\]

contains all `U_b∩P_0`. Its size is `1+η(b,d)=1+β(b,d)`,
and `β(b,d)≤j_b`, since it counts a subset of row `b` of `C`.
Hence `m_b≤1+j_b`. Together with (6),

\[
m_b\le\min(\lfloor4/j_b\rfloor,1+j_b)\le2
\qquad(1\le j_b\le3).                                  \tag{7}
\]

But each top vertex on the empty line has five `B` successors:
its other successors are four top vertices and one central vertex,
with none in `A`. Therefore

\[
20=\sum_{b\in B}|U_b\cap P_0|\le8\cdot2=16,
\]

a contradiction. Thus every `P` line is used. The predecessor
multiplicity patterns are reduced to

\[
\boxed{(4,4,3,1),\ (4,4,2,2),\ (4,3,3,2),\ (3,3,3,3).}
\]

The excluded pattern `(4,4,4,0)` does not depend on which successor
cosets occur. If all successor profiles also lie in a single coset,
the dual argument shows that none of its four lines is empty either.

## 6. Multiplicities four, four, three, one force a single successor coset

Suppose the predecessor multiplicities are `(4,4,3,1)`. Let `P_0`
be the thin line and `a_*` its sole `A` vertex. Fix `b∈M`.
At most four vertices `a∈A` can use a non-top middle in `a*b`,
because the two internal predecessors of `b` have sharp `F`-fibers
of size at most two. At least eight therefore satisfy

\[
|V_a\cap U_b|=1.                                        \tag{8}
\]

If `U_b` were a transversal of none of the used successor cosets,
it would meet at most two lines in each coset exactly once. A fixed
predecessor line contributes distinct successor profiles from one coset,
so it could account for at most `min(2,u_p)` of the incidences (8).
The total would be at most

\[
\sum_p\min(2,u_p)=2+2+2+1=7,
\]

a contradiction. Thus each `U_b`, `b∈M`, is a transversal of
at least one used successor coset and is consequently affine.

No `U_b` is a `P` line, by the
[exact top-fiber argument](1485_order_forty_twelve_high_profiles.md#1-no-partner-predecessor-profile-is-a-p-line).
An affine four-point plane different from `P_0` meets `P_0`
in at most two points. For `b∈L`, choose an internal successor
`d≠F(a_*)`; the top return fiber on `b→d` contains all
`U_b∩P_0`, and its size `1+η=1+β` is at most two. Thus
`|U_b∩P_0|≤2` for all eight vertices.

Each top vertex on `P_0` has four `B` successors, its other
successors being four top vertices, one central vertex, and `a_*`.
The marginal count forces equality:

\[
16=\sum_{b\in B}|U_b\cap P_0|,
\qquad |U_b\cap P_0|=2\quad\text{for every }b\in B.     \tag{9}
\]

Suppose now that two successor cosets `Q,R` occur. An affine
central-label transversal of both is either a `P` line or a
central-successor column, by the elementary classification used in the
[mixed high-profile argument](1485_order_forty_twelve_high_profiles.md#4-a-mixed-coset-exception-must-be-a-single-minority-vertex).
Neither meets `P_0` in two points. Hence each of the four affine
profiles `U_b`, `b∈M`, is a transversal of exactly one coset.
Its intersections with lines of the other coset are zero, two, or four,
never one. By (8), the coset to which it is transversal must have
population at least eight.

At most one of the two cosets can have population at least eight,
because their populations sum to twelve. Therefore all four profiles
`U_b`, `b∈M`, fail transversality to the same nonempty minority
coset. Choose any minority vertex `a`. Each product `a*b`, `b∈M`,
then requires a non-top middle, necessarily `F(a)`. Thus `F(a)`
would have all four members of `M` as internal successors, although
every internal outdegree is at most three. This is impossible.

Consequently all successor profiles belong to a single coset. In
particular, mixed `11+1` is excluded: its eleven majority vertices
require three predecessor lines, necessarily of sizes `4,4,3`, and
its sole minority vertex occupies the remaining line of size one.
The proof does not assume that the four low-sharp predecessor profiles
are affine.

## 7. In that single-coset case all internal bad-extension counts equal one

Continue with predecessor multiplicities `(4,4,3,1)`. Section 6 gives
one successor coset `Q`, affine `Q`-transversals `U_b` for `b∈M`,
and `|U_b∩P_0|=2` for all eight `b`. Let `f_*=F(a_*)`.

For an internal edge `bDd` with `b∈M`, the profile `U_b` has
rank-one projection to the `P` labels: it meets `P_0` twice and
cannot have rank zero or two. Removing any collection of whole `P`
lines therefore leaves an even number of its points. The top return
fiber has size `1+η(b,d)=1+β(b,d)`, which is positive and at most
three because `β(b,d)≤j_b=2`. Hence it has size two and `β=η=1`.

If `b∈L` and `d≠f_*`, the same fiber contains both points of
`U_b∩P_0`; its size is at most two because `j_b=1`. Again `β=η=1`.
If `d=f_*∈L`, its `F`-fiber consists only of `a_*`, so removing
`P_0` from `U_b` leaves exactly two points and gives the same answer.

Thus the only possible exceptions are edges from `L` into `f_*∈M`.
Their top fibers have size one or two, so their `β` values are zero
or one. These exceptions are impossible by weighted balance. Indeed,
writing

\[
\tau_b=\#\{(v,d):vDbDd,\ C_{vd}=1\},
\]

edge balance gives

\[
\sum_{d:bDd}\beta(b,d)
=\sum_{d:bDd}\eta(b,d)
=\tau_b
=\sum_{v:vDb}\beta(v,b).                               \tag{10}
\]

At `b=f_*∈M`, both outgoing weights are already one. Both incoming
weights are at most one, so neither can be zero. Therefore

\[
\boxed{\beta(b,d)=\eta(b,d)=1\quad\text{on every internal edge}.}
\tag{11}
\]

The exact good-pair formula `g_b=12−3j_b−τ_b` now yields

\[
\boxed{g_b=4\ (b\in M),\qquad g_b=6\ (b\in L).}       \tag{12}
\]

There is also an incidence simplification independent of any further
profiles. For `b∈L`, let `c` be the unique target of its `C` row.
Equation (11) says `dDc` for each of the three distinct successors
`d` of `b`. Thus `c` has internal indegree at least three and must
belong to `L`. Since every low-sharp column of `C` has sum one,
these four targets form a permutation of `L`, leaving no `C` entries
between `L` and `M` in either direction:

\[
\boxed{C_{LL}\text{ is a permutation matrix},\qquad
C_{ML}=C_{LM}=0,\qquad C_{MM}\text{ has row/column sums two}.}
\tag{13}
\]

These necessary conditions are substantially smaller than a whole-magma
search. They do not by themselves assert the impossibility of this
single-coset profile pattern.

## 8. A full predecessor line cannot contain a low-sharp target

This observation also follows from the repeated-profile capacity
argument in the eleven-vertex analysis. Suppose `u_p=4`. Each top
vertex on `P_p` has only one successor in `B`, so

\[
\sum_{b\in B}|U_b\cap P_p|=4.                         \tag{14}
\]

If some `a` on this profile had `F(a)=d\in L`, its `F`-fiber
would consist solely of `a`. For each of the three distinct internal
predecessors `b` of `d`, the exact top return fiber is
`U_b\setminus P_p` and has size `1+\eta(b,d)\le2`, because
column `d` of `C` has size one. Thus each such `b` contributes
at least two to (14), contradicting its total four.

Consequently the four vertices with predecessor profile `P_p` have
their four distinct `F`-images exactly in `M`. There can be at most
two full predecessor lines, because each medium `F`-fiber has size
two. If there are two full lines, they exhaust all eight vertices
with medium `F`-image. This argument does not require one successor
coset or affine partner profiles.

## 9. Mixed balanced profiles force an exact affine/non-affine split

Assume the predecessor multiplicities are `(3,3,3,3)` and both
successor cosets `Q,R` occur. Then exactly two of the four profiles
`U_b`, `b\in M`, are affine, and exactly two are non-affine.
More precisely:

- Each affine profile is an actual central-successor column, and
  both internal successors of its vertex belong to `M`.
- Each non-affine profile has both internal predecessors in `M`.
  Its two predecessor `F`-fibers jointly contain exactly one vertex
  from each of the four predecessor lines.

Here is a proof keeping the two orientations distinct. For any
`b\in M`, all but at most four products `a*b`, `a\in A`, need
a unique top middle. Hence at least eight incidences
`|V_a\cap U_b|=1` occur. If `U_b` is not a transversal to either
used successor coset, each of the four predecessor rows accounts
for at most two such incidences. Equality is necessary throughout:
each row supplies precisely two successful vertices and one exception.
All four exceptions must fill the two sharp `F`-fibers of the
internal predecessors of `b`, so both predecessors are medium.

A central-predecessor transversal that is also a transversal to
one of the permutation-profile cosets is affine: the corresponding
map between its two four-letter labels is a permutation, and every
permutation of `F_2^2` is affine. Thus a non-affine `U_b` is
exactly a profile of the exceptional kind just considered. Three
such vertices would receive at least six internal edges from `M`,
contradicting (2). There are therefore at most two non-affine profiles.

Conversely let `U_b` be affine. It must be transversal to at least
one used coset, since otherwise all its intersections with both
cosets would have size zero, two or four, giving no successful
incidences. If it failed transversality to the other coset, all
three vertices of a predecessor row assigned to that coset would
have to lie in the two predecessor `F`-fibers of `b`. Each such
fiber contains at most one vertex from a fixed predecessor line.
This is impossible. Hence `U_b` is transversal to both `Q,R`.
The elementary affine classification leaves a `P` line or a
central-successor column; Section 1 of the
[high-profile note](1485_order_forty_twelve_high_profiles.md)
excludes the former.

A central-successor column meets every `P` line once. On an
internal edge `bDd`, removing the `j_d` distinct predecessor lines
in its `F`-fiber leaves `4-j_d` top inputs. If `d\in L`, this
is three, whereas `1+\eta(b,d)\le2`. Thus both internal
successors of an affine medium vertex lie in `M`. Three affine
medium vertices would give at least six `M\to M` edges, again
contradicting (2). At most two are affine, proving the exact split.

In terms of the predecessor-line intersection matrix
`m_{bp}=|U_b\cap P_p|`, the affine rows are `(1,1,1,1)`.
The two non-affine rows are permutations of `(3,1,0,0)` or
`(2,1,1,0)`. For the latter assertion write the central labels
as `H,C\in F_2^2` and the `P` label as `p=C-MH`, with `M`
invertible. A central-predecessor transversal is the graph `C=f(H)`.
On four binary points `f` is affine if and only if
`\bigoplus_H f(H)=0`. Therefore the XOR of the four `P` labels
is nonzero for a non-affine profile. Among multiplicity patterns
of four labels, precisely `(3,1,0,0)` and `(2,1,1,0)` have
nonzero XOR; the patterns `(4,0,0,0)`, `(2,2,0,0)` and
`(1,1,1,1)` do not.

The same exact split holds for mixed predecessor multiplicities
`(4,3,3,2)`, except potentially for successor populations `10+2`
whose two minority vertices occupy the sole multiplicity-two row.
Indeed the bound of eight successful incidences still holds,
`\sum_p\min(2,u_p)=8`, and equality forces the exceptions in
row `p` to number `u_p-2`. An affine profile failing a used coset
can tolerate at most two vertices from each row assigned to it;
the only possible failed coset is therefore that sole thin row.
Outside this exception both affine/non-affine edge arguments above
apply unchanged. These are restrictions, not exclusions of the
remaining mixed cases.

## 10. The mixed ten-plus-two exception has a profile trichotomy

Suppose the predecessor multiplicities are `(4,3,3,2)` or `(4,4,2,2)`
and the successor coset populations are `10+2`. Normalize the sole
minority predecessor row to `p=3`; its multiplicity is two. Call
the majority successor coset `Q` and the minority one `R`. Let
`I` be the two distinct sharp `F`-images of the minority vertices.
They are distinct because two vertices in one `F`-fiber have
disjoint predecessor profiles.

For every medium vertex `b`, exactly one of the following holds,
up to permuting the entries in its predecessor-line intersection row:

1. The row is `(1,1,1,1)`. No new restriction beyond the exact
   return equations is required; those equations already force both
   internal successors to be medium.
2. The row is `(2,2,0,0)`. Its two internal predecessors are
   precisely the two vertices in `I`.
3. The row is `(3,1,0,0)` or `(2,1,1,0)`. Its two internal
   predecessors are medium. Their two whole `F`-fibers together
   contain exactly `u_p-2` vertices on each predecessor line `p`.

The row entries sum to four and none is four, by the no-`P`-line
theorem. Thus these alternatives exhaust all possibilities. The
XOR argument in Section 9 says that alternatives 1 and 2 are affine,
whereas alternative 3 is non-affine.

In alternative 2 an affine `U_b` must be transversal to `Q`:
otherwise all ten majority vertices fail exact-one intersection,
although the two internal predecessor `F`-fibers can account for
at most four failures. It cannot also be transversal to `R`,
because such an affine profile is a `P` line or a central-successor
column, neither of which has intersection row `(2,2,0,0)`.
All minority vertices therefore require their sharp `F`-images
as internal predecessors of `b`. There are exactly two such
images and exactly two internal predecessors, proving alternative 2.

In alternative 3 the non-affine profile is transversal to neither
coset. In each predecessor row it has exact-one intersection with
at most two of that row's distinct successor profiles. Since there
must be at least eight successful vertices and
`\sum_p\min(2,u_p)=8`, every row has exactly two successes.
The four failures must fill the two predecessor `F`-fibers completely.
Both predecessors are consequently medium, and the number of
their `F`-fiber vertices in row `p` is exactly `u_p-2`.

For comparison with the
[finite encoding](../scripts/1485_n40_twelve_mixed_ten_two_cnf.py),
let `c_{vp}` indicate whether the `F`-fiber at `v` contains a
vertex on predecessor line `p`. The additional necessary conditions
are exactly

\[
\begin{aligned}
\text{alternative 2: }&vDb\Longrightarrow c_{v3}=1,\\
\text{alternative 3: }&vDb\Longrightarrow v\in M,\qquad
 \sum_{v\in M}D_{vb}c_{vp}=u_p-2\quad\text{for each }p.
\end{aligned}                                            \tag{15}
\]

No predecessor labeling symmetry or unproved global affineness
assumption enters (15). The bounds are applied separately according
to each medium profile's actual intersection row. This section
establishes the mathematical reduction; a finite UNSAT result requires
its own separately checked certificate.

## 11. Other mixed four-four-two-two arrangements have the same split

For predecessor multiplicities `(4,4,2,2)`, the exact two-affine,
two-non-affine conclusion of Section 9 holds unless the successor
populations are `10+2`.

If the two full predecessor rows are assigned to different successor
cosets, an affine medium profile failing either coset would force all
four vertices of that full row into two predecessor `F`-fibers. Each
fiber can contain at most one vertex from the row, a contradiction.

If both full rows are assigned to the same successor coset, the
other coset has population two or four. The former is precisely
the exception. In the latter, Section 8 says the two full rows
exhaust all medium `F`-fibers. Thus all four minority vertices
have low `F`-images. Each low `F`-fiber contains only one vertex,
so they cannot all be covered by the two predecessor fibers of a
medium vertex. Hence an affine medium profile cannot fail this
minority coset either. Failure of the majority coset is already
impossible because it has at least eight vertices.

In all these nonexceptional cases every affine medium predecessor
profile is therefore a central-successor column, with both internal
successors medium. A non-affine medium profile still has at most
eight successful exact-one incidences, and saturation again gives
two medium predecessors. The cross-edge count (2) forces exactly
two of each kind, with the same row shapes and edge directions
as in Section 9.
