# Order forty, fourteen degree-five vertices: both profile families are single cosets

Research note, 19 September 2026. Continue with the three surviving
aligned internal incidence types in
[the near-saturation note](1485_order_forty_near_saturation.md).
This note proves a further **analytic necessary condition**: all fourteen
degree-five vertices have their top-predecessor profiles in one `V₄`
coset and their top-successor profiles in another single coset. The
[subsequent geometric exclusion](1485_order_forty_fourteen_exclusion.md)
now rules out this remaining case. This page records the reduction
used in that proof; it does not prove the general spectrum conjecture.

Write `Z,A,B,T` for the degree classes `4,5,8,10`. There are two
low-sharp vertices `l_0,l_1∈B`, each of sharp degree one, and four
high-sharp vertices in `B`, each of sharp degree three. Each high-sharp
vertex `b` has one ordinary internal neighbor in each direction, the
same attached low-sharp vertex `l`. Each low-sharp vertex is attached
to two high-sharp vertices. The sharp-path matrix on the four
high-sharp vertices is `J₄` minus a permutation matrix. The remaining
two vertices of `A` lie on sharp loops at `l_0,l_1`.

Reverse the operation if necessary so that all top-predecessor profiles
of `A` belong to one coset `P={P_p:p∈F₂²}`. Write their multiplicities
as `u_p`. Equal predecessor profiles can have at most four different
successor profiles, and they all belong to one common successor coset.
These facts were proved in the
[large-class analysis](1485_min_four_large_five_class.md). In particular

\[
u_p\le4,\qquad\sum_pu_p=14,\qquad
e_p:=4-u_p\ge0,\qquad\sum_pe_p=2. \tag{1}
\]

At least two predecessor profiles are therefore fully occupied.

## 1. Every high-sharp B vertex has exactly two good top pairs

Fix a high-sharp `b∈B`, and let `l` be its attached low-sharp vertex.
Consider `R_l⁻¹(b)`. It has size `40/8=5`. Its non-top members
are precisely the three sharp `A` predecessors of `b`:

* Each such predecessor `a` satisfies `a*l=b` because
  `a⇒b→l` is a good path.
* A non-top input `x` must be an ordinary predecessor of `b`.
  Besides those three `A` vertices, the only candidate in `B` is
  `l`, but `l*l` is its sharp-loop `A` vertex, not `b`.
* A central input always gives a top product.

Exactly two top vertices `t` therefore satisfy `t*l=b`.

For each `t∈TopPred(b)`, the fiber `L_t⁻¹(b)` has four members.
It contains the three sharp `A` successors of `b`; the fourth
member must be either `l` or top, since it lies in `Row(b)`.
Exactly two of the four top predecessors use `l`, by the preceding
count. The other two have one top member each. Consequently

\[
\boxed{|\{(t,v)\in T^2:t*v=b\}|=2.} \tag{2}
\]

These two pairs have different first coordinates. The dual fiber
argument shows they have different second coordinates as well.
More generally, the three sharp `A` neighbors leave room for at
most one top element in each participating top-translation fiber.

## 2. No high-sharp B predecessor profile is a P line

Suppose `TopPred(b)=P_p`. Fix `v∈TopSucc(b)`. All four members
of `P_p` are ordinary middles' first endpoints for the product with
second endpoint `v`.

There is exactly one central-good pair among them, because `P_p`
is a transversal of central successor labels. Every possible `A`
replacement must have predecessor profile `P_p`. All such `A`
vertices have their successor profiles in one coset; its lines
partition `T`.

If the line containing `v` occurs among those `A` profiles, all
three noncentral pairs have that `A` vertex as good middle.
Otherwise none has a central or `A` replacement. Their ordinary
middle `b` has degree eight, so strict degree descent leaves no
other possible lower-degree replacement: all three products must
then equal `b`.

The latter alternative would put three good top pairs in one column,
contrary to the one-per-column fiber bound. The former alternative
gives none. Thus every column would give zero, contradicting (2).
Therefore

\[
\boxed{\operatorname{TopPred}(b)\ne P_p
\quad\text{for every high-sharp }b\text{ and every }p.} \tag{3}
\]

## 3. Suppose both successor cosets occur among the twelve high A vertices

By the [affine high-profile lemma](1485_order_forty_near_saturation.md#affine-profiles-of-the-remaining-sharp-degree-three-b-vertices),
each high-sharp `B` predecessor profile is then a `P` line or an
entire central-successor column. Equation (3) excludes the former.

These four central columns are distinct. To see this, take a fully
occupied `P_p`, whose existence follows from (1). Each top point
on it has four `A` successors, four top successors and one central
successor. Its degree ten leaves exactly one `B` successor. Two
identical high-sharp predecessor columns would contradict this,
since every central column meets `P_p`. Thus the four high-sharp
predecessor profiles partition `T` into the four central columns.

A top point on `P_p` has exactly `5-u_p=1+e_p` successors in `B`.
After accounting for the one high-sharp successor, its number of
low-sharp successors is exactly `e_p`. Therefore the two low-sharp
predecessor profiles have pointwise sum

\[
\mathbf1_{\operatorname{TopPred}(l_0)}+
\mathbf1_{\operatorname{TopPred}(l_1)}=e_p
\quad\text{on }P_p. \tag{4}
\]

If the deficit in (1) were two on a single line, both low-sharp
predecessor profiles would equal that entire `P` line. This is
impossible by the two-point intersection theorem: each must meet
the missing `P` line at each attached high-sharp vertex in exactly
two points, whereas two `P` lines meet in zero or four points.

Hence the deficits are one on each of two different `P` lines.
Equation (4) says the low-sharp predecessor sets partition their
union. Each low-sharp set meets one missing `P` line in two points;
that line must be one of these two. Its other two points therefore
lie on the other line. Both low-sharp predecessor profiles split
two-and-two between the same two `P` lines.

## 4. The low-sharp profiles would have contradictory affine ranks

Use the common central alphabet `F₂²`, and write `P_p:C=M H+p`.
By centrality, a low-sharp predecessor set is a graph `C=f(H)`.
Its `P` parameter

\[
p(H)=f(H)+M H
\]

takes exactly two values, each twice. Every two-element subset of
`F₂²` is an affine line; hence a balanced two-valued function on
`F₂²` is affine of rank one. Thus `p(H)` is affine of rank one,
and consequently `f(H)=D H+c` is affine, with

\[
\operatorname{rank}(D+M)=1. \tag{5}
\]

Fix either low-sharp vertex `l`. For each high-sharp row `i` of the
sharp-path matrix, at least one of its three `A` vertices has target
column `j` attached to the other low-sharp vertex: there are two
such columns, while the row omits only one of the four columns.
For that vertex `a_ij`, the product `a_ij*l` has a unique top
middle. Indeed its only possible `B` middle is the sharp successor
`b_j`, and there is no internal edge `b_j→l`; no `A` or central
middle is possible either.

Therefore `TopPred(l)` meets the successor line of `a_ij` in
exactly one point. We obtain such a line from **every** successor
coset occurring among the high-sharp rows, including both assumed
cosets.

For an affine graph `C=D H+c`, its parameter on a line of slope
`N` is `(D+N)H+c`. A nonempty fiber of this affine map can have
size one only if `D+N` is invertible. Thus a single exact-one
intersection implies transversality to the entire slope-`N` coset.

Write the two other slopes as `MΩ,MΩ²`, with `Ω` of order three.
Both `D+MΩ` and `D+MΩ²` must be invertible. As proved in the
affine high-profile lemma, this forces `D=0` or `D=M`. Neither
option satisfies (5). This contradiction proves that the twelve
high-sharp `A` vertices use only one successor coset.

It remains to show that the two low-sharp-loop `A` vertices use
that same coset. This is established next. A single successor coset
is not itself claimed to be impossible.

## 5. Any remaining mixed case has a rectangular set of twelve profiles

Denote the common high successor coset by `Q`. If all four `P`
labels occur among the twelve high-sharp `A` vertices, the
partner-coset rule already forces both other `A` vertices to have
successor profiles in `Q` as well.

Otherwise precisely three `P` labels occur, each four times, because
the twelve high vertices have distinct profile pairs and a fixed
`P` label has at most four partners. Their profiles fill the entire
`3×4` rectangle of those three `P` lines and all four `Q` lines.
The two other `A` vertices must share the fourth `P` label, and
their successor profiles belong to the same coset. Only the case
where this is not `Q` remains to exclude.

Normalize the two full cosets `P,Q` as in the
[saturated proof](1485_order_forty_single_coset.md#2-affine-normalization-uses-one-common-central-alphabet).
Translate both profile labels by the missing `P` label, so it becomes
zero while `C=p+q` is preserved. Allowing the resulting constant
term in `H`, the formulas are

\[
C(p,q)=p+q,\qquad H(p,q)=L p+Wq+\delta, \tag{6}
\]

where `L,W` are invertible binary matrices. The high `A` profiles
are exactly `(V\setminus\{0\})×V`, with `V=F₂²`.

Label the four high-sharp `B` vertices by `i,j∈V`. There is a
high `A` vertex `a_ij` at all but one position in each row and
column of their sharp-path matrix. The four missing positions
form a permutation matrix. Write its actual profile coordinates
as `p_ij,q_ij`.

Each column has three distinct `p` labels, so they are precisely
the three nonzero labels. **Complete the `p` array** at its four
missing positions by putting zero there. Every completed column
is a permutation. Each actual row of the `q` array contains
three distinct values. At this stage its fourth value has not
yet been specified.

## 6. The first identity fills the missing linear equations

Every high-sharp `B` successor profile is a `P` transversal. Write
its central successor parameter as the affine permutation

\[
\phi_k(p)=C\bigl(\operatorname{TopSucc}(b_k)\cap P_p\bigr).
\]

Likewise every high-sharp predecessor profile is a `Q` transversal,
so

\[
\psi_k(q)=H\bigl(\operatorname{TopPred}(b_k)\cap Q_q\bigr)
\]

is an affine permutation. These facts follow from the affine
high-profile lemma; they do not assume the four sets are disjoint.

Apply E1485 with `x=a_ij,y=b_k,z=b_ell`, whenever `a_ell,k`
exists and `ell≠j`. Both relevant intermediates are top, since
there are no internal edges between high-sharp `B` vertices.
Avoidance of a central final product gives

\[
\phi_k(p_{ij})\not=H(p_{\ell k},q_{ij}).
\]

The three actual values in column `k` are all nonzero. Therefore,
using the completed `p_jk`, the only remaining possibilities are

\[
\phi_k(p_{ij})+H(0,q_{ij})\in\{0,Lp_{jk}\}. \tag{7}
\]

Fix `k` and a nonzero profile label `p`. There is exactly one actual
cell with this predecessor label in each column `j`. Its four
successor labels, as `j` varies, are all different because the high
profiles fill the rectangle. Thus the left side of (7) runs over
all four values. On the right, `Lp_jk` also runs over all four
values. At the unique `j` with `p_jk=0`, the left side must be zero;
none of the other three positions can therefore use zero. This
forces, at every actual cell,

\[
\phi_k(p_{ij})=H(p_{jk},q_{ij})\qquad\text{for all }k. \tag{8}
\]

Subtract (8) for `k,k′`. For each fixed `j`, the affine function
`φ_k(p)+φ_k′(p)` is constant on the three distinct nonzero `p`
values. An affine map on `F₂²` constant on three points is constant
everywhere, because a nonzero linear map has fibers of size at most
two. The constant is independent of `j`. Hence

\[
p_{jk}+p_{jk'}\text{ is independent of }j,
\qquad p_{ij}=d_i+e_j. \tag{9}
\]

The four `d_i` are different by the column-permutation property.
The four `e_j` are different too: the unique zero of column `j`
occurs where `d_i=e_j`, and the zero positions occupy different
rows. Thus both arrays label permutations of `V`.

Relabel the four high-sharp vertices simultaneously so that `d_i=i`.
Then `e_j=E j+e_0` for an invertible binary matrix `E`, since every
permutation of four points is affine. The functions `φ_k` have one
common invertible linear part `J`, by the same three-point argument.
Their offset differences are `L(e_k+e_k′)`.

Equation (8), for one fixed `k`, now expresses the actual values as

\[
q_{ij}=M i+N j+q_0, \tag{10}
\]

where `M=W⁻¹J` is invertible. Define the missing four `q` entries
by this formula. Each actual row has three different values, so `N`
is invertible as well. The completed `q` array is therefore Latin
in both directions.

The completed map `(i,j)↦(p_ij,q_ij)` is affine on `F₂⁴`. Its
twelve actual values are distinct, so its image cannot have size
at most eight. It is a bijection onto all sixteen profile pairs.
In particular the four newly supplied `q` entries are exactly the
missing values of their respective rows.

## 7. The dual identity fills the remaining equations

Fix `k`, and let `i_0` be the missing column of row `k`. Put
`v_k=q_k,i_0`, the missing value just supplied by (10).

Apply the dual identity with `x=a_ij,y=b_k,z=b_ell`, using the
three actual cells in row `k` and omitting `ell=i` when present.
The same central-label exclusion gives

\[
\psi_k(q_{ij})+p_{ij}\in\{q_{ki},v_k\} \tag{11}
\]

at every actual cell. In particular at `i=i_0` both alternatives
are equal. Define the affine error function on all completed cells

\[
\mathcal E_k(i,j)=\psi_k(q_{ij})+p_{ij}+q_{ki}.
\]

At `i=i_0`, this vanishes at three distinct `j` values. Its linear
coefficient in `j` is therefore zero. The error is an affine
function of `i` alone and vanishes at `i_0`.

As `i` varies, `w_i=q_ki+v_k` is an invertible affine coordinate
vanishing at `i_0`, because the completed row `q_k,*` is a
permutation. Thus `E_k(i,j)=F w_i` for a binary linear map `F`.
Equation (11), valid in three actual cells of each row, gives

\[
Fw\in\{0,w\}\quad\text{for every }w\in F_2^2.
\]

Such a map is either zero or the identity. Indeed if it kills a
nonzero `u` and fixes a different nonzero `v`, it sends `u+v` to
`v`, neither zero nor `u+v`.

The identity alternative would give
`ψ_k(q_ij)+p_ij=v_k` at all actual cells. For a fixed `q`, the
rectangle has three actual cells with three distinct `p` values,
which makes that equation impossible. Therefore `F=0`, proving

\[
\psi_k(q_{ij})=p_{ij}+q_{ki} \tag{12}
\]

on all completed cells, including the four virtual ones.

Subtract (12) for `k,k′`. Since a completed row of `q` runs over
all four values, the affine permutations `ψ_k` have one common
linear part. Their offsets are different: for a fixed `i`, the
four values `q_ki` are different by the column-permutation property.

Write the high-sharp predecessor profiles in the form
`{t_(R_k(q),q):q∈V}`. From (6),

\[
\psi_k(q)=L R_k(q)+Wq+\delta.
\]

Consequently the four functions `R_k` have a common linear part
and four distinct offsets. For each `q` their four values cover
all `p`, so the four high-sharp predecessor profiles partition `T`.

## 8. The partition contradicts the two-point intersections

In the rectangular mixed case the `P` multiplicities are `4,4,4,2`.
If the high-sharp predecessor profiles partition `T`, equation (4)
applies again: both low-sharp predecessor profiles must equal the
entire deficient line `P_0`.

But each high-sharp sharp-predecessor triple is missing precisely
`P_0`. The two-point intersection theorem requires its attached
low-sharp predecessor profile to meet `P_0` in exactly two points,
not four. This contradiction excludes the last mixed possibility.

We conclude that **all fourteen `A` successor profiles lie in one
coset**, in addition to the single predecessor coset obtained after
possibly reversing the operation. The three internal incidence types
are then excluded by the
[rank-one rectangle argument](1485_order_forty_fourteen_exclusion.md).
