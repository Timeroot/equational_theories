# Order forty: profile and incidence reductions for the thirteen-vertex exclusion

Research note, 19–20 September 2026. The thirteen/seven branch at
order forty is excluded by the reductions on this page and the
[final analytic profile obstruction](1485_order_forty_thirteen_directions.md).
Sections 1–6 below are analytic. Section 7 is a transparent finite
incidence classification, with a standard-Python checker and explicit
counts; it is not a SAT or whole-magma search. The other sharp-degree
distributions have their separately linked proofs below. No Lean
theorem is asserted.

Write `Z,A,B,T` for the degree classes `4,5,8,10`, with sizes
`4,13,7,16`. For `b∈B`, let `j_b` denote its balanced sharp
in/out degree. Let `D` be ordinary adjacency within `B`, and let
`C_bd=1` mean that a sharp path `b⇒a⇒d` passes through `A`.
Thus `D` has row/column sums `4−j_b`, and `C` has row/column
sums `j_b`.

As in the [fourteen-vertex exclusion](1485_order_forty_fourteen_exclusion.md),
`j_b=4` would leave at most four non-top two-step endpoints among
seven possible `B` targets. A top return contradicts the
[universal return-matching bound](1485_general_return_matching.md).
Hence `1≤j_b≤3`. If `k` is the number with `j_b=3`, the sharp
degree distribution is

\[
\#\{j=1\}=k+1,\qquad \#\{j=2\}=6-2k,
\qquad \#\{j=3\}=k,\qquad 0\le k\le3.                 \tag{1}
\]

The [three-high-sharp exclusion](1485_order_forty_thirteen_three_high.md)
excludes `k=3` analytically. The
[two-high-sharp exclusion](1485_order_forty_thirteen_two_high.md)
excludes `k=2` by a complete finite incidence check. The case
`k=1` is likewise excluded by the
[one-high-sharp finite check](1485_order_forty_thirteen_one_high.md).
Thus this page treats `k=0`, with sharp distribution
`(1,2,2,2,2,2,2)`, completing its exclusion in the linked
analytic continuation.

The same matching bound forces `C_bd=1` whenever both endpoints
have sharp degree three.

## 1. The six sharp-degree-two successor profiles are affine in the remaining case

For this section, restrict to the remaining distribution
`(1,2,2,2,2,2,2)`. In particular, every sharp `G`-fiber has
at most two members. The excluded distributions were handled
independently of any affine-profile claim.

By the [large-class profile theorem](1485_min_four_large_five_class.md),
after replacing the operation by its opposite if necessary, all top
predecessor profiles of `A` belong to one Klein-four coset
`P={P_p:p∈F₂²}`. Let `u_p` be their multiplicities. A fixed
predecessor profile has distinct partners in one successor coset,
so

\[
1\le u_p\le4,\qquad \sum_pu_p=13.                         \tag{2}
\]

Fix `b∈B` with `j_b=2`. It has two successors inside `B`.
At most four members `a∈A` have `G(a)∈D(b)`, because each
of these two possible `G`-values has a fiber of size at most two.
For every other `a`, the product `b*a` has no non-top middle:
its only possible internal middle would be the sharp predecessor
`G(a)`. Thus it is top-valued with a unique ordinary top middle,
and `|TopSucc(b)∩U_a|=1`.

A four-point set which is not a transversal of a four-block
partition has exact-one intersection with at most two blocks.
If `TopSucc(b)` were not a `P`-transversal, at most `2·4=8`
of the thirteen `A` vertices could have the required exact-one
intersection, by (2). At least five would require their internal
middle `G(a)`, exceeding the bound of four. Therefore

\[
\boxed{|\operatorname{TopSucc}(b)\cap P_p|=1
\quad\text{for all }p\text{ whenever }j_b=2.}              \tag{3}
\]

The profile is also a transversal of the four central successor
labels. Its central label is therefore a permutation of the four
`P` labels. Every permutation of `F₂²` is affine. Thus (3)
gives an affine description of every such successor profile.
The unique vertex with sharp degree one is the only possible exception.

If the successor profiles of `A` also belong to a single coset,
the dual argument gives an affine description of the predecessor
profile of every `b` with `j_b=2` as well.

## 2. No B predecessor profile is a P line

Continue with the remaining sharp distribution, so every `j_b`
is one or two. Fix an ordinary internal edge `b→d`. Its
top return-fiber members are exactly

\[
T\cap R_d^{-1}(b)
=\operatorname{TopPred}(b)\setminus
  \bigcup_{a:F(a)=d}U_a.                                \tag{4a}
\]

Indeed a top path `t→b→d` can only have a lower replacement
in `A`; such a replacement has sharp successor `F(a)=d` and
contains `t` in its predecessor profile. If `TopPred(b)` were
a `P` line, (4a) would have size zero or four, since all `U_a`
are lines of the same partition. But the exact fiber count below
gives size `1+η(b,d)`, where `η` counts a subset of column
`d` of `C`. Thus its size lies between one and `1+j_d≤3`.
This is a contradiction. Every `b` has an internal successor,
so none of the seven predecessor profiles is a `P` line.

We also retain the useful exact count of good top pairs.

Let `g_b` count good ordered top pairs with product `b`. Write

\[
\tau_b=\#\{(v,d)\in B^2:v\mathrel D b\mathrel D d, C_{vd}=1\}.
\]

Then

\[
\boxed{g_b=12-3j_b-\tau_b.}                               \tag{4}
\]

To verify (4), fix a top predecessor `t` of `b`. The four-element
fiber `L_t^{-1}(b)` contains all `j_b` sharp `A` successors.
Besides its top members, its other possible members lie among the
`4−j_b` ordinary `B` successors of `b`. For each such successor
`d`, the fiber `R_d^{-1}(b)` has five members. Its non-top
members are the `j_b` sharp predecessors of `b`, together with
the internal predecessors `v` for which `C_{vd}=0`. Thus it has
exactly

\[
1+\#\{v:v\mathrel D b, C_{vd}=1\}
\]

top members. Summing these occurrences over `d` and subtracting
them from `4(4−j_b)` gives (4).

The rectangle defining `τ_b` has `(4−j_b)²` cells. Therefore

\[
g_b\ge12-3j_b-(4-j_b)^2=(j_b-1)(4-j_b).                  \tag{5}
\]

In particular `g_b≥2` for `j_b=2` or `3`. Each individual
row or column of this good-pair set has at most `4−j_b≤2`
members, by the same four-element fiber count.

The stronger fiber argument at the start of this section gives

\[
\boxed{\operatorname{TopPred}(b)\notin P
\quad\text{for every }b\in B.}                          \tag{6}
\]

There is a dual statement when the successor profiles of `A`
belong to one coset. These restrictions reduce the affine-profile
problem; the subsequent sections and linked continuation supply the
full exclusion.

## 3. In the remaining sharp distribution, all B successor profiles are affine transversals

The other exclusions now leave exactly one vertex `l∈B` with
sharp degree one and six with sharp degree two. Section 1 makes
the successor profiles of those six vertices `P`-transversals.
At each top vertex `t`, the number of `B` predecessors is

\[
5-\#\{a\in A:t\in\operatorname{TopSucc}(a)\}:
\]

its other predecessors comprise four top vertices, one central
vertex, and the indicated `A` vertices. Every successor profile
of `A` belongs to a coset different from `P`, and therefore
meets each `P` line exactly once. Summing the displayed count
over any fixed four-point line `P_p` gives

\[
\sum_{b\in B}|\operatorname{TopSucc}(b)\cap P_p|
=4\cdot5-13=7.
\]

The six sharp-degree-two vertices each contribute one. The
remaining profile contributes one as well, so it too is a
`P`-transversal. Together with central-label transversality this
makes its coordinate permutation affine, exactly as in §1. Thus

\[
\boxed{\operatorname{TopSucc}(b)\text{ is an affine }P
\text{-transversal for every }b\in B.}                    \tag{7}
\]

This argument does not assume that the successor profiles of `A`
use one coset. If they do use one coset `Q`, its dual proves
that every `B` predecessor profile is an affine `Q`-transversal.
These are intermediate restrictions used in the exclusion below.

## 4. Mixed successor cosets have only one or two minority vertices

Continue with the sole remaining sharp distribution. Suppose the
successor profiles of `A` use both other cosets `Q,R`. A fixed
predecessor line has partners in only one successor coset. Assign
`p` of the four `P` lines to `Q` and the other `4−p` to `R`.
Each `Q` line then has multiplicity at most `p`, and each `R`
line has multiplicity at most `4−p`.

Fix a sharp-degree-two vertex `b∈B`. At most four members of
`A` have their sharp successor `F(a)` in the two-element
internal predecessor set of `b`. For every other `a`, the
product `a*b` has a unique top middle, so

\[
|V_a\cap\operatorname{TopPred}(b)|=1.                    \tag{8}
\]

If this four-point predecessor profile were a transversal of
neither `Q` nor `R`, it would meet at most two lines of each
partition exactly once. At most

\[
2p+2(4-p)=8
\]

members of `A` could then satisfy (8). The other five or more
would exceed the four possible exceptions. Hence the profile is
a transversal of at least one of `Q,R`. Together with its
central-predecessor-label transversality, this makes it affine.
An affine plane which is not a transversal of the other coset
has no exact-one intersections with its lines: its nonempty
intersection sizes are two or four. Consequently all `A`
vertices from that other coset must be among the four exceptions.

### A two-versus-two assignment of P lines is impossible

If `p=2`, each successor coset has at least five of the thirteen
vertices, because the other can have at most eight. Therefore
every sharp-degree-two predecessor profile must be a transversal
of both `Q` and `R`.

The elementary affine classification already used in the
[fourteen-vertex profile analysis](1485_order_forty_near_saturation.md#affine-profiles-of-the-remaining-sharp-degree-three-b-vertices)
says that a central-label transversal of both other cosets is
either a `P` line or a central-successor column. Section 2 excludes
the `P` line. The six profiles would therefore be six central
columns. There are only four such columns, and they must be
distinct: a fully occupied `P` line exists by (2), and each top
point on it has exactly one `B` successor. Two coincident
columns would give it two. This is a contradiction.

### In a three-versus-one assignment, the minority has size at most two

Relabel the cosets so three `P` lines are assigned to `Q` and
one to `R`. At least nine `A` vertices belong to `Q`, so
every sharp-degree-two predecessor profile is a `Q`-transversal.
At most four of the six are also `R`-transversals, by the same
central-column argument. Choose one which is not.

All minority `A` vertices have the same `P` predecessor line,
so their `F` values are distinct: equal `F` would require
disjoint predecessor profiles. By (8), all these distinct `F`
values lie in the chosen vertex's two-element internal predecessor
set. Thus

\[
\boxed{|\{a:V_a\in R\}|\le2.}                            \tag{9}
\]

The majority therefore has eleven or twelve vertices. A `G`
fiber has distinct successor profiles from one coset. If the
minority has one vertex, it is the entire `G` fiber of the
unique sharp-degree-one partner. If it has two vertices, they
form the entire `G` fiber of one sharp-degree-two partner: there
are not two sharp-degree-one partners available.

Finally all seven predecessor profiles, including the remaining
sharp-degree-one profile, are `Q`-transversals. Indeed every
`A` predecessor profile lies in `P` and meets each `Q` line
once. The dual of the marginal count in §3 gives total incidence
seven on each `Q` line. The six sharp-degree-two profiles
contribute six, so the remaining profile contributes one.

Thus in every still possible case, all seven `B` successor
profiles are affine `P`-transversals and all seven predecessor
profiles are affine transversals of a single majority coset `Q`.
The `A` profiles either all lie in `P×Q`, or have just one or
two minority vertices on the fourth predecessor line. These
restrictions suffice to exclude the mixed arrangements next.

## 5. Both minority possibilities are impossible

Every `B` predecessor profile is now an affine `Q`-transversal,
and none is a `P` line. Its projection to the `P` label has
rank one or two. Consequently its intersection with any `P`
line has at most two points.

If the minority has one vertex, its predecessor line `P_0` has
multiplicity one. Each point on `P_0` therefore has four `B`
successors. The total predecessor-profile incidence on `P_0` is
sixteen, exceeding the maximum `7·2=14`. This excludes minority one.

Suppose instead there are two minority vertices `a_1,a_2`, with
distinct sharp successors `f_1,f_2`. Any sharp-degree-two
predecessor profile which is not an `R`-transversal requires
both `f_1,f_2` as internal predecessors, by (8). At least one
of these two distinct vertices has sharp degree two and hence
only two internal successors. Thus there are at most two such
nontransversal profiles. Section 4 showed there are at least two,
so there are exactly two. The other four high-sharp profiles are
four distinct central-successor columns and partition the top grid.

The minority predecessor line `P_0` has multiplicity two. Its
total `B` predecessor-profile incidence is `4·3=12`. The four
central columns contribute four; the two other high-sharp profiles
contribute at most four; and the remaining low-sharp profile also
contributes at most two, by (6) and affine transversality. Their
total is at most ten, a contradiction.

Thus there is no minority. Both profile families of the thirteen
degree-five vertices belong to single distinct cosets:

\[
\boxed{(U_a,V_a)\in P\times Q\quad\text{for every }a\in A.}
                                                               \tag{10}
\]

The thirteen distinct profile pairs leave exactly three holes in
the four-by-four `P×Q` grid. All seven `B` predecessor profiles
are affine `Q`-transversals and all seven successor profiles are
affine `P`-transversals. None is a line of the opposite partition,
by (6) and its dual. This analytic reduction feeds the incidence
classification and final profile obstruction.

## 6. Every internal edge has two top return inputs

In the single-coset situation, the union removed in (4a) consists
of `j_d` distinct `P` lines. An affine `Q`-transversal which
is not itself a `P` line has `P` intersection pattern either
`(1,1,1,1)` or a permutation of `(2,2,0,0)`.

The [edge-balance theorem](1485_general_return_matching.md#5-bad-extension-balance-on-every-internal-edge)
gives, on an internal edge `b→d`,

\[
|T\cap R_d^{-1}(b)|=1+\eta(b,d)=1+\beta(b,d),
\qquad 0\le\beta=\eta\le\min(j_b,j_d).
\]

If `j_d=2`, the removed union in (4a) has even intersection
size. The remaining top fiber is therefore even and lies between
one and three, forcing size two. If `j_d=1`, the removed line
has at most two points of the profile. The remaining fiber has
at least two points and at most `1+j_d=2`, with the same result.
Hence

\[
\boxed{\beta(b,d)=\eta(b,d)=1\quad(b\mathrel D d).}        \tag{11}
\]

Equation (4) now gives `g_b=8−2j_b`: six good top pairs for
the unique low-sharp vertex and four for each of the other six.
Since central outputs account for 64 top pairs and `A` outputs
for `13·12=156`, exactly

\[
256-64-156-(6+6\cdot4)=6
\]

ordered top pairs have a top-valued product.

Let `l` be the unique sharp-degree-one vertex and let `f` be
its unique sharp two-step successor, so `C_{lf}=1`. Every one
of the three internal successors `d` of `l` satisfies
`β(l,d)=D_{df}=1`. Thus `f` has at least three internal
predecessors. Only `l` has that internal degree, so `f=l`.
The row and column sums of `C` therefore isolate a sharp loop
at `l`; its other block is a two-regular binary matrix on the
six high-sharp vertices. Moreover

\[
\boxed{D(l)=D^{-1}(l),\qquad |D(l)|=3.}                   \tag{12}
\]

Indeed the three successors of `l` all point back to `l`,
and its internal in-degree is three.

There is no ordinary loop at `l`. Otherwise choose another
neighbor `h`, and let `a_l` be the sharp-loop `A` vertex at
`l`. There are no cross-block `C` entries, so
`l*h=h*l=l`, while `l*l=a_l` and `h*a_l=l`. E1485 with
`x=h,y=l,z=l` would then give

\[
h=(l*h)*(h*(l*l))=l*l=a_l,
\]

contradicting their different degrees. Thus after labeling `l=0`
we can normalize its three neighbors as `S={1,2,3}`; the other
high vertices are `R={4,5,6}`. The high-to-high part of `D`
has row and column degree one on `S` and two on `R`.
The assertions in this section are analytic necessary conditions;
no incidence enumeration is used in proving them.

## 7. A finite incidence reduction leaves one internal type

The analytic constraints of §6 make the remaining incidence
enumeration small. The separate standard-Python checker

```sh
python3 scripts/1485_n40_thirteen_low_sharp_check.py
```

enumerates all high-to-high binary `D` matrices with row and
column degrees `(1,1,1,2,2,2)`, then adds the prescribed edges
to and from the low vertex. It completes all high-to-high binary
`C` matrices with row and column degree two, keeping the isolated
low loop. Multiple internal middles force `C` entries, and (11)
constrains each proposed `C` row and column. The checker then
uses the one-`A` five-walk and general return-path conditions
proved in the [two-high-sharp note](1485_order_forty_thirteen_two_high.md),
and the universal prohibition on a single isolated bad position
in a closed five-walk.

The [checker](../scripts/1485_n40_thirteen_low_sharp_check.py)
asserts these counts:

| Stage | Number remaining |
| --- | ---: |
| Normalized internal `D` matrices | 4,383 |
| Internal matrices admitting all row choices for `C` | 2,628 |
| Completed `C` matrices with row-side bad-extension count one | 23,040 |
| After the column-side count one | 4,752 |
| After one-`A` five-walk closure | 84 |
| After return-path budgets | 12 |
| After the remaining universal five-walk test | 12 |

The twelve labeled pairs form one isomorphism type under permutations
of `S` and `R`. Write their vertices as `l,S_i,R_i`, with
`i∈ℤ/3ℤ`. Its complete internal and sharp-path successor sets are

| Vertex | Ordinary internal successors `D` | Sharp two-step successors `C` |
| --- | --- | --- |
| `l` | `S_0,S_1,S_2` | `l` |
| `S_i` | `l,R_i` | `S_{i+1},R_i` |
| `R_i` | `S_{i+1},R_{i−1}` | `S_{i+1},R_{i+1}` |

The run takes approximately **2.6 seconds**. This section is a
finite-assisted classification of **necessary incidence data**, not
a construction of a magma. In particular the one surviving type
must not be mistaken for evidence that order forty exists.

The [analytic direction continuation](1485_order_forty_thirteen_directions.md)
proves that this last incidence type is incompatible with the affine
profiles. The attached directions split two plus one; marginal counts
and the three-hole geometry then exclude both possible ranks for the
low profiles. Thus the thirteen/seven branch is excluded. Its final
profile obstruction is analytic, while this necessary-incidence
classification and the earlier `k=1,2` exclusions retain their stated
finite-check dependencies.
