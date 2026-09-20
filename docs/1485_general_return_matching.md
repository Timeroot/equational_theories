# Return matching for arbitrary products

Research note, 19 September 2026. This is an unconditional finite
E1485 theorem. It strengthens the earlier applications restricted to
top-valued products. No enumeration, SAT premise, full-core hypothesis,
or Lean formalization is involved in the theorem itself.

## 1. The matching does not require a top product

Let `b*d=e` in a finite model of order `n`. Set

\[
X=L_e^{-1}(d),\qquad Y=R_e^{-1}(b).
\]

The good path `b→e→d` makes both fibers nonempty. Uniform
translation fibers give

\[
|X|=|Y|=n/d(e).
\]

There is an ordinary-edge perfect matching between them:

\[
\boxed{X\longrightarrow Y,\quad x\longmapsto x*b,
\qquad y\longmapsto d*y\text{ is its inverse}.}             \tag{1}
\]

Indeed, if `e*x=d`, E1485 gives

\[
(x*b)*(b*(e*x))=b,
\]

so `(x*b)*e=b`. Its dual gives

\[
((b*d)*x)*(x*b)=x,
\]

so `d*(x*b)=x`. Thus the displayed map is injective from `X`
to `Y`; their equal finite cardinalities make it bijective with
the stated inverse. Each pair `x,x*b` is an ordinary edge by
definition. Alternatively the symmetric identities verify the inverse
directly, without finiteness.

## 2. An independent-set bound, including the equality case

Let `I` be any set with no ordinary edge from a member of `I`
to a member of `I`, including no loops. A matched pair cannot
have both endpoints in `I`. Consequently

\[
\boxed{|X\cap I|+|Y\cap I|\le n/d(e).}                     \tag{2}
\]

In particular let `j_d^+` count the sharp successors of `d` in
`I`, and let `j_b^-` count the sharp predecessors of `b` in
`I`. The paths `e→d⇒x` and `y⇒b→e` are good, so all these
vertices belong to the respective fibers. Therefore

\[
\boxed{j_b^-+j_d^+\le n/d(b*d).}                           \tag{3}
\]

The set of all vertices of degree strictly below `√n` is always
an eligible `I`, by the ordinary-edge bound `d(x)d(y)≥n`.

If equality holds in (3), every matched edge has exactly one
endpoint in `I`, and there are no additional `I` vertices in
the fibers beyond the counted sharp neighbors. In particular there
can be no ordinary three-edge path

\[
d\longrightarrow x\longrightarrow y\longrightarrow b
\]

whose two successive two-edge paths are good and with `x,y∉I`.
Indeed goodness says `d*y=x` and `x*b=y`. Choose `z` with
`z*b=y`, which exists since `y→b`. E1485 gives
`(b*d)*(d*(z*b))=d`, hence `e*x=d`. Thus `x∈X` and
`y=x*b` is its matched point, contrary to equality in (3).

## 3. Arbitrary subsets give a boundary-capacity identity

For any subset `U` of the carrier, let `g_U(d,b)` count the
ordinary three-edge paths `d→x→y→b` whose two successive
two-edge paths are good and whose two internal vertices lie in
`U`. The matching (1) parametrizes exactly these paths when its
matched endpoints are restricted to `U`: its inverse says `d*y=x`,
and the direct argument above proves the converse fiber membership.

Inclusion-exclusion on the matched edges therefore gives the exact
identity

\[
\boxed{g_{M\setminus U}(d,b)
=\frac n{d(b*d)}-|X\cap U|-|Y\cap U|+g_U(d,b).}             \tag{4}
\]

In particular the right side is nonnegative. This can impose stronger
restrictions than the independent-set bound when the ordinary and
good paths in a large non-independent subset are already known.

For example, at order forty with degrees `4,5,8,10` and four
central vertices, take `U=A∪B` and suppose `b,d,e=b*d∈B`.
Each member of `B` has four non-top neighbors on either side.
Let `β(e,d)` be the number of bad internal `B` extensions of
`e→d`, and let `η(b,e)` be the number of bad internal `B`
predecessors of `b→e`. All paths involving `A` are sharp and
good. Thus

\[
|X\cap U|=4-\beta(e,d),\qquad
|Y\cap U|=4-\eta(b,e),
\]

and (4) gives

\[
\boxed{g_{A\cup B}(d,b)\ge3-\beta(e,d)-\eta(b,e).}         \tag{5}
\]

The analogous lower bound at order 48 with degrees `4,6,8,12`
and four central vertices has constant **two**, since its
degree-eight return fiber has size six instead of five.
These are necessary constraints, not exclusions by themselves.

## 4. Four-degree consequences

In the minimal-central-count family with degrees
`r,q=r+k,2r,2q` and order `2rq`, the degree-`q` class `A`
is independent. Write `j_b` for the balanced sharp degree of
`b` in the degree-`2r` class `B`. Then (3) gives both

\[
\begin{aligned}
b*d\in T&\Longrightarrow j_b+j_d\le r,\\
b*d\in B&\Longrightarrow j_b+j_d\le q.
\end{aligned}                                             \tag{6}
\]

Thus if `j_b+j_d>q`, the product must lie in `A`: a central
middle is impossible for these endpoints. Let `C` be the binary
matrix of sharp two-step paths `B→A→B`. It has row sum
`k j_b`, so

\[
\boxed{\#\{d\in B:j_d>q-j_b\}\le k j_b.}                 \tag{7}
\]

This is a new distributional restriction, independent of the earlier
top-return path budget. It also applies to diagonal endpoint pairs.

At order forty, `r=4,q=5,k=1`. Any two sharp-degree-three
members of `B` must have their product in `A`. Each such row
of `C` has just three entries, so there can be **at most three**
sharp-degree-three members of `B`.

In particular, this immediately excludes all three residual
fourteen/six incidence types, each of which has four such members.
It replaces the long affine-profile argument in
[the fourteen/six exclusion](1485_order_forty_fourteen_exclusion.md)
once the earlier incidence reduction is available. More strongly,
the same bound forces the sharp paths to split into two sectors
in the other possible distribution `(1,2,2,3,3,3)`. A short
internal-degree count then excludes that distribution too; the linked
note gives the argument. Thus the fourteen/six exclusion can now be
proved entirely analytically, without the incidence enumeration.

## 5. Bad-extension balance on every internal edge

Continue in the minimal-central-count four-degree family of §4.
For an ordinary internal edge `b→d` in `B`, let `β(b,d)`
count its bad internal extensions `b→d→x`, and let `η(b,d)`
count its bad internal predecessors `y→b→d`. Then

\[
\boxed{\beta(b,d)=\eta(b,d).}                              \tag{8}
\]

Indeed `L_b^{-1}(d)` has `q=r+k` elements. Its non-top
members consist of all `j_d` sharp `A` successors of `d`
and its `r-j_d-β(b,d)` good internal successors. Its number
of top members is therefore `k+β(b,d)`. Dually the number
of top members of `R_d^{-1}(b)` is `k+η(b,d)`.

Both top counts equal the number of central parameters `z` for
which `b B_z d`. The two-sided auxiliary-fiber formulas say

\[
b\mathrel{B_z}d
\quad\Longleftrightarrow\quad (z*b)*d=b
\quad\Longleftrightarrow\quad b*(d*z)=d.
\]

As `z` ranges over the `r` central vertices, `z*b` ranges
bijectively over the `r` top predecessors of `b`, while `d*z`
ranges bijectively over the `r` top successors of `d`. This proves
(8), and also the exact auxiliary multiplicity

\[
\#\{z:b\mathrel{B_z}d\}=k+\beta(b,d)=k+\eta(b,d).          \tag{9}
\]

In particular `β(b,d)≤r-k`. Summing (8) over the edges at
one vertex shows that the numbers of bad internal two-edge paths
**starting, passing through, and ending at that vertex are equal**.
Denote their common value by `ε_b`.

The exact number of ordered top pairs whose product is `b` is

\[
\boxed{g_b=(r-k)(r-j_b)-\varepsilon_b.}                     \tag{10}
\]

To see this, the `r` fibers `L_t^{-1}(b)`, for top predecessors
`t` of `b`, each have size `r`. Together they contain `r j_b`
sharp-successor occurrences in `A` and
`k(r-j_b)+ε_b` internal-successor occurrences in `B`, by (9).
The remaining occurrences are exactly the good top pairs.

There are at most `(r-j_b)²` internal paths with middle `b`,
so (10) gives `g_b≥(r-j_b)(j_b-k)`. A second bound follows
from the sharp-path matrix `C`: since its row at `b` has
`k j_b` ones, each outgoing internal edge has at most `k j_b`
bad extensions. Hence

\[
\boxed{g_b\ge(r-j_b)\max\{j_b-k,\ r-k-kj_b\}.}            \tag{11}
\]

At order forty, a vertex with sharp degree one has at least six
good top pairs; sharp degrees two and three each give at least two.
The edgewise equality (8), not just the total bad-path count, is
important when testing possible internal incidence patterns.

Finally, if `f=|A|` and `ε=Σ_b ε_b`, counting all top pairs
by their output class gives the exact number with a top output:

\[
\boxed{\#\{(u,v)\in T^2:u*v\in T\}
=k\bigl((r-k)f-r^2(r-2k+1)\bigr)+\varepsilon.}             \tag{12}
\]

Here each central output has `r²` good top pairs, each member
of `A` has `r(r-k)`, and (10) supplies the remaining non-top
outputs. Thus at order forty with `f=13` the count is `ε-9`,
whereas at order forty-eight with `f=14` it is `ε+24`.

## 6. A weighted version beyond the smallest central class

There is an unconditional version of the auxiliary counting step.
For any ordinary edge `b→d`, write `P_t,C_t` for the central
predecessor and successor blocks of a top vertex. Counting the
central parameters for which the edge belongs to `B_z` gives

\[
\boxed{
\sum_{t\in T\cap R_d^{-1}(b)}|P_t|
=\sum_{v\in T\cap L_b^{-1}(d)}|C_v|.}                     \tag{13}
\]

Indeed the left side counts the parameters through
`(z*b)*d=b`, and the right through `b*(d*z)=d`.
For a fixed top predecessor `t` of `b`, the central solutions
of `z*b=t` are exactly `P_t`, since all paths with a central
endpoint are good. The successor statement is dual.

More generally one may assign weights `w_z` to the central
parameters, replacing the two block sizes by their weight sums.
In particular, suppose there is one common assignment satisfying

\[
\sum_{z\in P_t}w_z=\sum_{z\in C_t}w_z=1
\quad\text{for every }t\in T.                              \tag{14}
\]

The central blocks in each central row partition `Z` into `r`
pieces, so `Σ_z w_z=r`. The top predecessor and successor
blocks of every vertex also partition `Z`. Consequently (14)
forces **exactly `r` top neighbors on both sides at every vertex**.
The weighted form of (13) further gives

\[
\boxed{|T\cap R_d^{-1}(b)|=|T\cap L_b^{-1}(d)|.}            \tag{15}
\]

In a four-degree model `r,q,b,s` with `qb=n`, `r<q<√n<b<s`,
the only non-top neighbors of a degree-`b` vertex are sharp
degree-`q` neighbors and internal degree-`b` neighbors. Its
non-top neighbor count is `b-r`. Thus (15), together with
the equal full fiber sizes `q`, gives the same edgewise
bad-extension balance `β=η`. This conclusion does not require
the central class to have size `r`.

For example, at `r=4,|Z|=5`, if all double predecessor blocks
and all double successor blocks have a **common** central label
`c`, assign `w_c=0` and weight one to the other four labels.
No singleton block can equal `{c}`: any four-block partition of
five labels has one double block, and that block already contains
`c`. A singleton `{c}` in the same partition would overlap it.
Every top block occurs in such a partition, so every block has
weight one. Thus (14) holds and the edgewise balance applies.
This common-center hypothesis is stronger than the separate-star
hypothesis in [the constant-top note](1485_order_forty_eight_constant_top_profiles.md).
Neither hypothesis is asserted for every five-central model.
