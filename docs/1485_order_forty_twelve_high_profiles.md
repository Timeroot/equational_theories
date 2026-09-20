# Order forty with twelve degree-five vertices: restrictions on high-sharp partners

Research note, 20 September 2026. These are analytic necessary
conditions for the twelve/eight branch. **They do not exclude it.**
No enumeration or affine-profile hypothesis for all eight partners
is used.

The degree classes `Z,A,B,T` have degrees `4,5,8,10` and sizes
`4,12,8,16`. Write `j_b` for the balanced sharp degree of
`b∈B`, `D` for its ordinary internal adjacency, and `C` for
the binary sharp-path matrix through `A`. Then `D` has in/out
degree `4−j_b`, while `C` has row/column sums `j_b`.

Sharp degree four is impossible: it leaves at most four non-top
two-step endpoints among eight targets in `B`, whereas a top
return would violate the
[return-matching bound](1485_general_return_matching.md). Hence
the distributions are exactly among

\[
(1^6,3^2),\qquad(1^5,2^2,3),\qquad(1^4,2^4).
\]

The first distribution is now
[excluded analytically](1485_order_forty_twelve_two_high_exclusion.md),
without affine-profile assumptions or a finite check. Its internal
two-step endpoint counts force four distinct sharp targets into a
two-element set. The other two distributions remain open here.

By the [large-class theorem](1485_min_four_large_five_class.md),
after taking the opposite operation if necessary, the predecessor
profiles `U_a` of all `a∈A` belong to one four-line coset
`P`. Their multiplicities `u_p` satisfy `0≤u_p≤4` and
`Σu_p=12`. A fixed predecessor line has all its successor
partners in one of the other two cosets, called `Q,R`.

## 1. No partner predecessor profile is a P line

For any ordinary internal edge `b→d`, strict descent and the
sharp edges out of `A` give the exact top-fiber identity

\[
T\cap R_d^{-1}(b)
=U_b\setminus\bigcup_{a:F(a)=d}U_a.                    \tag{1}
\]

Here `F(a)` is the unique sharp successor of `a`. A bad
middle of degree eight can only be replaced by a degree-five
middle, and the displayed union lists precisely those replacements.

If `U_b` were a `P` line, the right side would have zero
or four members. On the other hand, counting the non-top
members of this five-element fiber gives

\[
|T\cap R_d^{-1}(b)|=1+\eta(b,d),
\qquad
\eta(b,d)=\#\{v:vDb, C_{vd}=1\}.                       \tag{2}
\]

If `j_b≥2`, then `η≤4−j_b≤2`, contradicting zero or four.
If `j_b=1`, equation (2) must equal four, so `η=3` and
the column sum of `C` forces `j_d=3`. This would hold for
all three internal successors of `b`. There are at most two
sharp-degree-three vertices, again a contradiction. Thus

\[
\boxed{U_b\notin P\quad\text{for every }b\in B.}        \tag{3}
\]

This includes the sharp-degree-one vertices and does not assert
that their profiles are affine.

## 2. Every sharp-degree-three partner has affine profiles

Let `h` have sharp degree three. Its unique internal successor
has at most three sharp `A` successors. Thus at most three
members of `A` can have a non-top middle in the product `h*a`.
For at least nine of the twelve vertices,

\[
|V_h\cap U_a|=1.                                      \tag{4}
\]

A four-point set which is not a transversal of four disjoint
lines has exact-one intersection with at most two of them.
Those two `P` lines account for at most eight vertices of `A`.
Consequently `V_h` is a `P`-transversal. It is also a
central-successor-label transversal, so the induced permutation
of four labels is affine. Hence `V_h` is an affine plane.

Dually at most three `A` vertices can have a non-top middle
in `a*h`, using the unique internal predecessor of `h`.
If all successor profiles use one coset, this immediately makes
`U_h` a transversal of that coset. In the mixed case, assign
`p` predecessor lines to `Q` and the other `4−p` to `R`;
empty lines may be assigned arbitrarily. Each `Q` line has
multiplicity at most `p`, and each `R` line at most `4−p`.
A profile transversal to neither coset accounts for at most

\[
2p+2(4-p)=8
\]

exact-one intersections, again insufficient. Thus `U_h` is a
transversal of at least one successor coset, and its central-label
transversality makes it affine as well.

## 3. High-sharp good pairs and return partners are tightly counted

Let `p,h,s` be the unique internal predecessor, the high-sharp
vertex, and its unique internal successor. The sole internal
two-edge path with middle `h` is bad exactly when `C_ps=1`.
The [edge-balance and good-pair formulas](1485_general_return_matching.md#5-bad-extension-balance-on-every-internal-edge)
therefore give

\[
\boxed{g_h=3-C_{ps}\in\{2,3\}.}                        \tag{5}
\]

Every top translation fiber participating in this profile already
contains the three sharp `A` neighbors of `h`. It has room
for at most one top input. The good top pairs with product `h`
therefore form a matching in both directions.

There is also an exact top-return count:

\[
\boxed{\#\{d\in B:h*d\in T\}=1+j_s+C_{ps}.}           \tag{6}
\]

Indeed the non-top two-step endpoint set is `C(h)∪D(s)`.
Its two parts have sizes three and `4−j_s`; their intersection
has size `β(h,s)=η(h,s)=C_ps`. Subtracting from eight gives
(6). Every endpoint counted in (6) has sharp degree one by
return matching. The dual count is `1+j_p+C_ps`.

## 4. A mixed-coset exception must be a single minority vertex

Suppose both successor cosets occur and some high-sharp `U_h`
is a transversal of `Q` but not `R`. Since this profile is
affine, its intersections with `R` lines are zero, two or four,
never one. Every `A` vertex using `R` must therefore have
its sharp successor equal to the unique internal predecessor
of `h`.

Vertices with the same sharp successor have disjoint predecessor
profiles. Since those profiles are `P` lines, the number of
minority vertices is at most the number `q` of predecessor
lines assigned to `R`. If `p` lines are assigned to `Q`,
the majority has at most `4p` vertices. Thus

\[
12\le4p+q,\qquad p+q\le4,\qquad q\ge1.
\]

It follows that `p=3`, `q=1`, and there is exactly one
minority vertex, with eleven majority vertices. In particular,
unless this `11+1` arrangement occurs, every high-sharp profile
`U_h` is a transversal of both successor cosets. The elementary
affine classification then makes it either a `P` line or a
central-successor column; (3) excludes the former. Hence

\[
\boxed{\text{In every other mixed arrangement, each high-sharp }
U_h\text{ is a central-successor column.}}               \tag{7}
\]

These restrictions reduce the high-sharp cases without requiring
the low-sharp or sharp-degree-two profiles to be affine. The
compatibility of the remaining profiles and internal incidence
is still unresolved here.

## 5. Conditional on single successor cosets, every high-sharp partner has two good pairs

For this section only, suppose that all degree-five profiles
belong to `P×Q`, with one successor coset `Q`. This has not
been proved for every twelve-vertex case. The thirteen-vertex
single-coset theorem must not be used at this smaller cardinality.

There are four holes in the `P×Q` grid. Both profiles of a
high-sharp vertex `h` are affine transversals by §2. Applying
§1 to the opposite operation also excludes a successor profile
which is itself a `Q` line. Thus the projections of `U_h`
to the `P` coordinate and `V_h` to the `Q` coordinate have
rank one or two.

### Three good pairs would require both projection ranks to be two

If both ranks are one, each active hole in their support rectangle
has two possible first and two possible second endpoints. Each
of these pairs has two distinct central labels, independent of
the particular support line. If their central-label images intersect
in `c` labels, the hole contributes `4−c` good pairs.
The matching property requires at most two of its four pairs to
be good. Hence `c=2` and every active hole contributes two.
Since `g_h∈{2,3}`, necessarily `g_h=2`.

Now let `U_h` have rank two and `V_h` rank one. Each active
hole has one first endpoint and two second endpoints. Matching
requires exactly one of these two pairs to be central-valued.
Thus the central label of its first endpoint must lie in the
fixed two-element central-label image of `V_h`.

The central-successor-label map on the rank-two profile `U_h`
is either constant or bijective. One quick verification uses
coordinates `C=p+q`, `H=L(p+Ωq)+δ`. If `p=Bq+r`, then
`B` and `B+Ω` are invertible. Hence `Ω⁻¹B` is one of
the two order-three matrices, so `B=I` or `B=Ω²`.
The map `C` on this profile is consequently constant or
bijective, respectively.

In the bijective case only two first endpoints have a label
in the successor image, so the matching has size at most two.
In the constant case, on each of the two successor support lines
only one second endpoint has a different central label and can
participate in a good pair. Again there are at most two good
pairs. The dual argument treats rank one/rank two. Therefore

\[
g_h=3\quad\Longrightarrow\quad
\text{both profile projection ranks are two}.             \tag{8}
\]

### Return fibers rule out those three good pairs

Continue to denote the unique internal predecessor and successor
of `h` by `p,s`. If `g_h=3`, equation (5) gives `C_ps=0`.
On the internal edge `h→s`, equations (1), (2) and edge balance
then give a top return fiber of size one. But the rank-two
predecessor profile meets every `P` line once, and the union
removed in (1) consists of `j_s` distinct `P` lines. Thus

\[
1=4-j_s.
\]

Dually `1=4-j_p`, so both `p,s` have sharp degree three.
Universal return matching forces the product of any such two
vertices into `A`, since their sharp counts sum to six, exceeding
the return-fiber sizes five and four for products in `B,T`.
Thus `C_ps=1`, a contradiction. We conclude

\[
\boxed{g_h=2,\qquad C_{ps}=1}
\quad\text{for every high-sharp }h
\text{ in the single-coset case}.                         \tag{9}
\]

The same fiber calculation, now with top fiber size two, also
gives the separate implications

\[
\boxed{\operatorname{rank}U_h=2\Rightarrow j_s=2,
\qquad \operatorname{rank}V_h=2\Rightarrow j_p=2.}         \tag{10}
\]

Consequently, in the distribution `(1^6,3^2)`, every high-sharp
vertex has **two rank-one profiles**. Their support rectangle
contains exactly one hole, contributing the two good pairs;
their central-label images coincide, so their support directions
satisfy the usual relation `Δp=ΩLΔq`. In the distribution
`(1^5,2^2,3)`, two rank-two profiles are not excluded by this
argument; they require both internal neighbors to be among the
two sharp-degree-two vertices. No unconditional single-coset
claim or exclusion of either distribution is being made.
