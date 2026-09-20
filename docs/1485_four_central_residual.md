# Four central vertices: additional ten-top reductions

Research note, 18 September 2026. These are analytic necessary
conditions for the remaining minimum-degree-three, four-central,
ten-top case. They do **not** exclude that case. No solver search,
finite incidence enumeration, or Lean declaration is a premise.

The [full-entry exclusion](1485_four_central_full_entry.md) leaves
eight tops with central profile `(1,1)` and two with profile `(2,2)`.
Call the latter the **mids** and the former the **lows**.

## 1. The central incidence has canonical binary coordinates

Every central row has three top entries whose central successor
sets partition the four central points. Thus each central row
contains exactly one mid and two lows. Dually every central column
contains exactly one mid and two lows. The predecessor pairs of
the two mids partition the central set, as do their successor pairs.
Uniqueness of central middles forces every pair from the first
partition to meet every pair from the second exactly once.

Label the central points `(i,j)`, with `i,j∈{0,1}`, and the
mids `M_0,M_1`, so that

\[
P_{M_i}=\{(i,0),(i,1)\},\qquad
C_{M_i}=\{(0,i),(1,i)\}.
\]

The two lows in central row `(i,j)` must have successor labels
`(0,1−i)` and `(1,1−i)`. They are therefore uniquely labeled

\[
L_{ijk},\qquad P_{L_{ijk}}=\{(i,j)\},\qquad
C_{L_{ijk}}=\{(k,1-i)\}.
\]

Consequently the central-middle matrix `K` is given by

\[
\begin{aligned}
K(M_a,M_b)&=1,\\
K(M_a,L_{ijk})&=\mathbf1_{j=a},\\
K(L_{ijk},M_b)&=\mathbf1_{k=b},\\
K(L_{ijk},L_{\ell mn})&=\mathbf1_{(\ell,m)=(k,1-i)}.
\end{aligned}                                      \tag{1}
\]

These formulas do not specify the ordinary top adjacency.

## 2. The least noncentral degree is five or six

Let `q` be the least noncentral degree. A degree-`q` vertex has
only sharp non-top neighbors. Its sharp in/out counts agree, say
`k`, and its top predecessor and successor counts both equal
`t=q−k`. Here `1≤k≤3`.

Both top neighborhoods partition the four central points by their
central sets, so `t∈{2,3,4}`. Their `t×t` central-middle matrix
is `(q−3)`-regular: each top translation fiber contains the `k`
sharp inputs and `3−k` top inputs, and every bad path has a
central good replacement by minimality of `q`.

### Two top neighbors

Both top neighborhoods are exactly `{M_0,M_1}`. Their matrix is
all ones by (1), so `q−3=2`, hence `q=5` and `k=3`.

### Three top neighbors

The predecessor profile has the form

\[
U=\{M_a,L_{1-a,0,k_0},L_{1-a,1,k_1}\},
\]

and the successor profile has the form

\[
V=\{M_b,L_{b,j_0,0},L_{b,j_1,1}\}.
\]

Put `e=q−3=k`. The mid row and column each already contain
their common mid-to-mid entry. If `e=1`, both `k_i` must be
`1−b`, so each low row has no entry in the mid column or in
either low column, contradicting regularity. If `e=2`, one
`k_i=1−b`, and that low row again has no entries. Thus `e=3`.
All `k_i=b` and all `j_i=a`, making the whole matrix one.
We obtain `q=6`, `k=3`.

### Four top neighbors

Both profiles consist entirely of lows:

\[
U=\{L_{ij,k_{ij}}:i,j<2\},\qquad
V=\{L_{i,j'_{ik},k}:i,k<2\}.
\]

By (1), each row has at most two entries, because its target's
first index is fixed. But its required row sum is
`q−3=t+k−3=1+k≥2`. Thus `k=1`, `q=5`, and every row
has exactly two entries. For each occurring value `k_{ij}`, both
successor vertices with that first index must have second index
`1−i`. The same value cannot occur with both values of `i`.
Consequently, for one bit `ε`,

\[
k_{ij}=i\mathbin\oplus\varepsilon,\qquad
j'_{ik}=1-(i\mathbin\oplus\varepsilon).
\]

Define

\[
U_\varepsilon=\{L_{ij,i\oplus\varepsilon}:i,j<2\},
\qquad
V_\varepsilon=\{L_{i,1-(i\oplus\varepsilon),k}:i,k<2\}.
                                                        \tag{2}
\]

These are exactly the two possible profiles in the four-neighbor
case. Each such vertex is the good middle of eight ordered top
endpoint pairs, namely `t(3−k)=4·2`.

Thus

\[
\boxed{q\in\{5,6\}.}
\]

Degree-six vertices at the least noncentral degree are sharp-regular.
Degree-five vertices are either sharp-regular with two top neighbors,
or have sharp degree one and the four-low profiles (2).

## 3. An irregular degree-five vertex makes both reciprocal classes singletons

Suppose degree five is the least noncentral degree and some degree-five
vertex `a` has sharp degree one. Its ordinary row and column each
consist of four lows and one non-top sharp neighbor. Its top profiles
are `U_ε,V_ε` from (2).

Directly from their definitions,

\[
|V_\varepsilon\cap U_\eta|=2
\qquad(\varepsilon,\eta\in\{0,1\}).             \tag{3}
\]

For example, the first index `i` is free, while (2) uniquely fixes
the other two indices. Both profiles are disjoint from the two mids.

Consider the product `a*a`. Its top common middles number two,
by (3), so neither can be good: a good top middle has maximum degree,
and every other middle of the same maximum degree would contradict
strict degree descent. Its good middle must therefore be non-top.
The unique non-top successor and predecessor of `a` coincide; call
this vertex `b`. Both edges are sharp, and

\[
a*a=b,\qquad b*b=a.
\]

Now let `c` be any degree-five vertex. If it has two top neighbors,
the top common middles from `a` to `c` and from `c` to `a` are
absent. If it has four, each common-middle set has size two, by
(3). In either case no top middle can be good. The only non-top
successor or predecessor of `a` is `b`, so `a*c=c*a=b`.
In particular `b→c→b` is a path. Both edges are sharp because
`d(c)=5` and `d(b)=n/5`. Hence `b*b=c`. Since `b*b=a`, we
get `c=a`.

Every vertex of complementary degree `n/5` has a sharp neighbor of
degree five, now necessarily `a`. But `a` has only one sharp
neighbor in either direction. Thus that degree class is `{b}` as well:

\[
\boxed{\{x:d(x)=5\}=\{a\},\qquad
\{x:d(x)=n/5\}=\{b\}.}
\]

This conclusion applies only when an irregular degree-five vertex
exists. It does not exclude the alternative in which all degree-five
vertices have two top neighbors and sharp degree three.

In that remaining alternative the two degree-class sizes are also
determined. Let `A={x:d(x)=5}` and `B={x:d(x)=n/5}`. Every
member of `A` has exactly the two mids as its top predecessors
and successors, and three sharp neighbors in each direction.
No member of `B` can have two sharp predecessors in `A`: those
predecessors would have disjoint ordinary columns, but both columns
contain the two mids. The dual argument applies to sharp successors.
Thus each member of `B` has exactly one sharp neighbor in `A`
in each direction, and sharp-edge counting gives `|B|=3|A|`.

For any two endpoints in `A`, the two mids are ordinary common
middles, so neither can be good by strict degree descent. All other
possible middles are in `B` and both edges are sharp. There must
therefore be exactly one sharp `A⇒B⇒A` path for each ordered
pair of `A` endpoints. Each `B` supplies exactly one such path.
Consequently `|B|=|A|²`, and positivity gives

\[
\boxed{|A|=3,\qquad |B|=9.}
\]

Together with the irregular alternative, the degree-five and
reciprocal-degree class sizes are exactly `(1,1)` or `(3,9)`.
This does not assert that either configuration exists.

## 4. A saturation restriction on the ordinary top adjacency

The [degree-saturation argument](1485_five_central_binary_blocks.md#7-equality-in-the-product-degree-bound-forces-a-matching)
has a useful refinement. If `a=u*v` with both endpoints top and
`d(a)=9`, then

\[
Row(v)=F_u(a),\qquad
F_u(a)=\{h:u*(a*h)=a\}.
\]

The fixed-parameter equivalence says membership of `h` in this
set depends only on `h*u`, because it is equivalent to
`(h*u)*a=u`. Restricted to central `h`, the fibers of the map
`h↦h*u` are precisely the predecessor blocks `P_t`, where
`t` runs through the ordinary top predecessors of `u`.
Therefore

> The central successor set `C_v` is a union of the blocks `P_t`
> on the ordinary top predecessors of `u`.

In particular, if a mid `u` has exactly the two mids as ordinary
top predecessors, all these blocks have size two. No saturated
degree-nine product `u*v` can then have `v` low, whose `C_v`
is a singleton. The dual statement excludes low-by-mid saturated
products when the relevant mid's top successors are the two mids.

This restricts the proposed ordinary-top-adjacency pattern in which
the two mids form an isolated complete block. It is not by itself
an exclusion of that pattern or of the ten-top case.

## 5. Possible profiles of a first noncentral top output

Let `a` have the smallest degree `p` among noncentral top-top
products. Write `U=TopPred(a)`, `V=TopSucc(a)`, and let
`I=|U|`, `O=|V|`. Every bad path in `U×V` has a smaller-degree
top-product replacement, necessarily central. Its good-pair matrix
is therefore `J−K[U,V]`. Each row and each column of this matrix
has at most two entries: a top translation fiber has three slots
and includes a non-top sharp input.

Up to reversing predecessor and successor directions, the only
possibilities with a positive number `g` of good pairs are

| `I,O` | `g` | Good row counts | Sharp out-degree |
| --- | ---: | --- | --- |
| `2,3` | 2 | `2,0` or `1,1` | at most 2 |
| `2,4` | 4 | `2,2` | 1 |
| `3,4` | 4 | `0,2,2` | 1 |
| `4,4` | 8 | `2,2,2,2` | 1 |

Here are direct checks of the table from (1), not an enumeration
premise. A two-element profile consists of both mids. Against a
three-element profile, the mid column contributes no good entry
and each of its two low columns contributes exactly one. Against
four lows, every column contributes one; the bound of two per row
forces row counts `2,2`. Two two-element profiles have no good pair.

For two three-element profiles, write

\[
U=\{M_a,L_{1-a,0,k_0},L_{1-a,1,k_1}\},\quad
V=\{M_b,L_{b,j_0,0},L_{b,j_1,1}\}.
\]

If some `k_i≠b`, that low row of `K` is zero and its good row
has three entries, impossible. Thus both `k_i=b`. Dually both
`j_i=a`. The whole submatrix is then one, giving no good pair.

Against a four-low successor profile, a low predecessor row has
at most two central entries, so must have exactly two; its good
row has two. Any successor low with second index different from
`a` would have a zero central column and three good predecessors,
again impossible. All four second indices are consequently `a`.
The mid row is then entirely central, giving good row counts
`0,2,2`. Finally, with four lows on each side every central row
and column has at most two entries. The good-pair bound forces
exactly two of each, giving `g=8` and sharp degrees one.

## 6. Least degree six forces saturation, and is now excluded

The [variable-neighborhood slot bound](1485_three_central_minimum_top_output.md#a-general-top-fiber-slot-bound)
gives, for least noncentral degree `q` and sharp degrees `k⁺,k⁻`,

\[
\begin{aligned}
g&\le I(3-k^+)-(p-O-k^+)\max(0,q-p+I),\\
g&\le O(3-k^-)-(p-I-k^-)\max(0,q-p+O).
\end{aligned}                                      \tag{4}
\]

Suppose first `q=6`. Degree-six vertices are sharp-regular and
cannot be top products, so `p∈{7,8,9}`. For the four profiles
in the table, (4) gives the following upper bounds, using the
dual bound in the first three rows and `k⁺=1` in the last:

| `I,O` | Required `g` | Upper bound at `p=7` | Upper bound at `p=8` |
| --- | ---: | ---: | ---: |
| `2,3` | 2 | −2 | 1 |
| `2,4` | 4 | −4 | −2 |
| `3,4` | 4 | −1 | 0 |
| `4,4` | 8 | 2 | 2 |

Every row is impossible at seven and eight. At `p=9`, the
[saturation matching theorem](1485_top_output_saturation.md) excludes
every row except `2,3`, where the two good pairs must use different
mid predecessors. Thus, up to duality,

\[
\boxed{p=9,\qquad TopPred(a)=\{M_0,M_1\},\qquad
|TopSucc(a)|=3,\qquad g=2.}
\]

The two good pairs are mid-by-low products. Section 4 therefore
rules out the ordinary adjacency pattern where the two mids form
an isolated complete block. More decisively, the subsequent
[strict top-product gap](1485_strict_top_product_gap.md) now excludes
the entire degree-six branch: the smallest noncentral top-product
degree is nine and every top product has degree at most nine, so
all noncentral top products would attain the bound. That theorem
forces full core, contrary to four central vertices.

Consequently the least noncentral degree in the ten-top branch
is **five**, and the class-size alternatives `(1,1)` and `(3,9)`
from §3 apply unconditionally in this branch.

Finally suppose `q=5` and all degree-five vertices are sharp-regular.
Then `p>5`. At `p=6`, the same four rows of (4), now with `q=5`,
give upper bounds `0,−1,2,5`, respectively. These are all too small.
Consequently the first noncentral top product has degree seven
or eight: the strict top-product gap excludes nine as its minimum.
This is another necessary condition, not an
exclusion of the regular degree-five branch.
