# The first noncentral top output has regular top profiles

Research note, 19 September 2026. These are unconditional finite
E1485 theorems, not Lean declarations. They concern the least degree
among noncentral **products of top vertices**, without assuming that
this is the least noncentral degree in the whole magma.

Write `n=rs`, with minimum translation degree `r` and maximum `s`.
Let `T` be the top class and `Z` the central class. Assume some top
product is noncentral, and let `p` be the least degree of such a
product. Fix `a=u*w` of degree `p`, with `u,w∈T`.

**Theorem.** The vertex `a` has equally many top predecessors and
successors, say `t`. It has exactly `p−t` non-top neighbors in each
direction, with

\[
1\le p-t\le r-1.
\]

Every top translation fiber at `a` contains **all** the non-top
neighbors on the opposite side. Consequently the central-middle
matrix on `TopPred(a)×TopSucc(a)` is `(p−r)`-regular, and each
row and column has `r+t−p>0` good endpoint pairs with middle `a`.

The theorem does not assert that these non-top neighbors are sharp.

## 1. A fixed-parameter set is partitioned into top-product fibers

Choose a central successor `z` of `w` and put `t_0=z*u`, which
is top. For every `v∈Col(z)`, E1485 gives

\[
t_0*(u*v)=u.
\]

The map `v↦u*v` is injective on `Col(z)`. Indeed, if two such
inputs have the same product `b`, both are middles of paths
`b→v→z`; their central endpoint makes both paths good and hence
forces the inputs equal. Since `Col(z)` has size `r`, its image

\[
S=\{u*v:v\in Col(z)\}
\]

has size `r` and consists entirely of top-top products. It is
contained in the fiber `L_{t_0}^{-1}(u)`, which also has size `r`.
Thus these sets are equal. In particular the fixed-parameter set is

\[
F_{t_0}(u)
=\{x:t_0*(u*x)=u\}
=L_u^{-1}(S).
\]

Absorption applied to `t_0*a=u` gives `Row(a)⊆F_{t_0}(u)`.
Therefore, for every `x∈Row(a)`, its product `u*x` belongs to
`S` and is itself a top-top output.

## 2. Every non-top neighbor occupies the chosen top fiber

Let `x∈Row(a)` be non-top. The path `u→a→x` shows that
`u*x=a` or `d(u*x)<p`. The product cannot be central: every
input to a central output is top. Since `u*x` belongs to the
top-product set `S`, minimality of `p` excludes the lower-degree
alternative. Hence

\[
Row(a)\setminus T\subseteq L_u^{-1}(a).
\]

This fiber has size `r` and also contains the top input `w`.
It follows that `a` has at most `r−1` non-top successors. The
dual argument gives the same bound for non-top predecessors.

Now let `u'` be any top predecessor of `a`. Its nonempty fiber
`L_{u'}^{-1}(a)` has `r` elements, all ordinary successors of
`a`. Since there are at most `r−1` non-top successors in total,
this fiber contains some top input `w'`. Repeating the preceding
argument with `a=u'*w'` proves that the fiber contains **every**
non-top successor of `a`. The dual assertion holds at every top
successor of `a`.

## 3. Equal top-neighbor counts and a regular central matrix

Write `I=|TopPred(a)|`, `O=|TopSucc(a)|`. The non-top neighbor
counts are `p−I` and `p−O`. Thus each top left fiber at `a`
has exactly `r−(p−O)` top inputs, and each top right fiber has
exactly `r−(p−I)` top inputs. Both numbers are positive.

Any bad path from a top predecessor through `a` to a top successor
has a lower-degree top-product replacement, necessarily central.
Hence the central-middle matrix on this rectangle has constant row
sum

\[
O-\bigl(r-(p-O)\bigr)=p-r
\]

and the same constant column sum. Since `p−r>0`, counting its
entries gives `I=O=t`. The remaining assertions follow. Positivity
of the non-top neighbor count follows from existence of sharp
neighbors: a sharp neighbor of a noncentral vertex is not top.

## 4. The smallest central class forces a proper divisor

Suppose `|Z|=r>1`. The
[minimal-central-count structure theorem](1485_minimal_central_count.md)
gives exactly `r` top neighbors at every vertex and labels the tops
`t_{ij}`, with a central product precisely when the adjacent labels
agree. Thus the theorem above gives

\[
p\le2r-1.
\]

Its regular central-middle matrix is an equality matrix
`H_{ij}=1_{f(i)=g(j)}`, where both lists have length `r`.
Put `e=p−r`. Every occurring value of one list occurs exactly
`e` times in the other; positivity gives common support. Therefore
`e` divides `r`. The strict upper bound makes it a proper divisor:

\[
\boxed{p=r+e,\qquad e\mid r,\qquad 1\le e<r.}
\]

In fact this is also the least noncentral degree of the whole magma.
The earlier least-degree theorem writes that degree as `q=r+k`
with `k|r`. The alternative `k=r`, namely `q=2r`, is impossible
because `p≤2r−1` and `q≤p`. For `k<r`, every degree-`q`
vertex has `r(r−k)>0` top representations, so minimality gives
`p=q`.

Consequently the `q=2r` branch is excluded for **every** minimum
degree, not only degree three. If `r` is prime, the next degree
is necessarily `r+1`, all its vertices have sharp degree one, and
there are at most `r²` such vertices by the existing class count.
This does not exclude the smallest central class completely.

## 5. A row-local degree bound

The fiber argument also gives a bound without choosing a globally
least output. Fix a top `u` with `k=|C_u|<r`, choose any central
`z`, and put `S=u*Col(z)` as in §1. Exactly `k` members of
`S` are central, and they are precisely `C_u`: central endpoint
uniqueness supplies one input in `Col(z)` for each `c∈C_u`.
Choose a noncentral `a∈S` of minimum degree among the noncentral
members of this particular set.

The same absorption and descent argument shows

\[
Row(a)\subseteq
L_u^{-1}(a)\ \cup\!\bigcup_{c\in C_u}L_u^{-1}(c).
\]

These `k+1` fibers are disjoint and each has size `r`. Each meets
`Col(z)` in exactly one point, by injectivity from §1, but `Row(a)`
meets that central column at only its own input. At least `k`
points of the displayed union are therefore excluded from `Row(a)`.
Consequently

\[
\boxed{
\exists w\in T,\qquad
r<d(u*w)\le r+(r-1)|C_u|
\quad\text{whenever }|C_u|<r.
}                                                     \tag{4}
\]

This is an existence bound in every deficient top row, not a bound
on every individual product in that row. In particular a top row
with one central successor always has a noncentral output of degree
at most `2r−1`. There is an analogous column statement.

More generally, if a member `a∈S` has exactly `j` members of
`S` of strictly smaller degree, the same proof gives

\[
d(a)\le r+(r-1)j.
\]

Only those lower-degree fibers and its own fiber can meet `Row(a)`.
This local ordered-degree bound recovers `r²−r+1` when `j=r−1`.

## 6. A central-cardinality bound for the first top output

Let `m=|Z|<r²`. The central incidence moments give

\[
\sum_{u\in T}k^+_u k^-_u=m^2,
\qquad \sum_{u\in T}k^-_u=rm.
\]

Thus the weighted average of `k⁺` is `m/r`, so some top `u`
has `k⁺_u≤⌊m/r⌋<r`. Applying (4) gives

\[
\boxed{p\le r+(r-1)\left\lfloor\frac mr\right\rfloor.}
\]

For a non-full core, the
[central-defect gap](1485_boundary_central_defect.md) gives
`m≤r²−r−1`, and hence `⌊m/r⌋≤r−2`. Therefore

\[
\boxed{r<p\le r^2-2r+2.}
\]

At minimum degree three, the first noncentral top output is thus
at most five for **every** non-full central core. At minimum degree
four it is at most ten. More generally, if no divisor of the order
lies strictly above `r` and at most `r²−2r+2`, full core follows,
and the already established quotient theorem gives order `r²·2^j`.

This final use of the central-defect gap is not an independent new
proof of that gap or of the minimum-degree-two full-core theorem.
