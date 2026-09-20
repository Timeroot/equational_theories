# When central parameters give the same auxiliary relation

Research note, 18 September 2026. This is a pen-and-paper equivalence
with full core, not a proof that the equivalent conditions always hold.

Let `M` be a finite E1485 magma with minimum translation degree `r`,
central set `Z`, and top set `T`. For central `h`, recall the
[two-sided auxiliary relation](1485_unrestricted_central_incidence.md)

\[
B_h(a)=a*Col(h),\qquad B_h^-(b)=Row(h)*b.
\]

It has exactly `r` predecessors and successors at every vertex.

**Criterion.** The relations `B_h`, `h∈Z`, all coincide if and
only if the central core is full: `|Z|=r²`. No assumption about
the number of top vertices is needed.

Full core implies that every `B_h` is sharp adjacency, by the
[sharp-regularity theorem](1485_full_core_sharp_regularity.md). For
the converse we use the following mixed-coordinate rank calculation.

## A mixed-coordinate retraction

For central `h` and arbitrary `c`, put

\[
\lambda_{h,c}(a)=(h*a)*(a*c).
\]

The path identities give

\[
h*\lambda_{h,c}(a)=h*a,\qquad
\lambda_{h,c}(a)*c=a*c.
\]

Consequently `λ` is an idempotent, and its image is in bijection
with the joint support of the two coordinates `(h*a,a*c)`.
For each `u∈Row(h)`, centrality identifies `L_h⁻¹(u)` with
`Row(u)`. The possible second coordinates on this fiber therefore
form `im(R_c L_u)`. The
[mixed-translation rank formula](1485_graph_research.md) gives

\[
\boxed{\operatorname{rank}\lambda_{h,c}
=\sum_{u\in Row(h)}\operatorname{rank}(R_cL_u)
=\sum_{u\in Row(h)}\frac n{d(c*u)}.}              \tag{1}
\]

In particular, since every degree is at least `r`, the right side
is at most `r(n/r)=n`, with equality exactly when every `c*u`
in the sum is central. Since `λ` is an idempotent on a finite set,
rank `n` is equivalent to `λ=id`. Thus, for fixed central `h`,

\[
\boxed{(\forall a,\ (h*a)*(a*c)=a)
\quad\Longleftrightarrow\quad c*Row(h)\subseteq Z.} \tag{2}
\]

The forward implication here genuinely uses finite rank; the path
identities defining the retraction alone do not imply it.

There is also an exact aggregate defect. The ordinary edge
`c→c*u` implies `d(c)d(c*u)≥n`, so (1) gives

\[
\varepsilon_h(c):=r\,d(c)-\operatorname{rank}\lambda_{h,c}
=\sum_{u\in Row(h)}\left(d(c)-\frac n{d(c*u)}\right)
\ge0.                                                    \tag{3}
\]

To sum the ranks over `c`, count their fixed points. For fixed `a`,
the condition `λ_{h,c}(a)=a` says `a*c∈B_h(a)`. There are
`r` such output values, each with `n/d(a)` inputs. Hence

\[
\sum_c\operatorname{rank}\lambda_{h,c}
=rn\sum_a\frac1{d(a)},\qquad
\boxed{\sum_c\varepsilon_h(c)=r\Delta,}           \tag{4}
\]

where `Δ=Σ_a d(a)−nΣ_a 1/d(a)` is the
[sharp-degree defect](1485_sharp_degree_defect.md). For top `c`,
`r d(c)=n`, so `ε_h(c)` is exactly the number of points moved
by `λ_{h,c}`. Every moved point strictly decreases degree: the
ordinary path `(h*a)→a→(a*c)` has good replacement `λ_{h,c}(a)`.
These formulas do not yet force the nonnegative defect to vanish.

## A global regular band with common fixed set exactly `Z`

The following addition, 20 September 2026, gives a global version of
the remaining minimum-rank problem. It is a reduction, not an exclusion
of any further spectrum value. Keep `h` central and abbreviate
`λ_c=λ_{h,c}`. Then

\[
\boxed{\lambda_c^2=\lambda_c,\qquad
\lambda_b\lambda_c\lambda_b=\lambda_c\lambda_b,\qquad
\bigcap_c\operatorname{Fix}(\lambda_c)=Z.}             \tag{5}
\]

Indeed, all these transformations preserve each fiber
`F_u=L_h⁻¹(u)`, for `u∈Row(h)`. On that fiber,
`λ_c(a)=u*(a*c)`, so the fixed-left mixed-projection band identities
apply with the same `u`. Their common fixed points are precisely the
sharp successors of `u`. Since `u` is top, these have degree `r`.
Conversely every central `a` satisfies
`(h*a)*(a*c)=a`, directly by centrality at `a`.

Formula (1) gives

\[
\boxed{\operatorname{rank}\lambda_c\ge r^2
\quad\text{for every }c,\qquad
\operatorname{rank}\lambda_c=r^2\quad(c\in Z).}          \tag{6}
\]

There are `r` summands in (1), each at least `n/s=r`.
If `c` is central, every `c*u` is top, so all summands equal
`r`. On the other hand, applying one copy of every `λ_c` in
any order gives a retraction onto `Z`: each new application fixes
its own image and preserves the fixed points already obtained.
Every generated transformation fixes `Z` pointwise. Consequently

\[
\min\{\operatorname{rank}F:F\text{ is a nonempty word in the }
\lambda_c\}=|Z|.
\]

Thus full core is exactly the assertion that this global band has
no rank drop below the minimum generator rank `r²`.

A sufficient condition is closure of the **generator images** under
binary intersections. The band identities give
`im(λ_bλ_c)=im(λ_b)∩im(λ_c)`; if that intersection is always
another generator image, their finite total intersection has size at
least `r²`, and hence is all of a full core. This image-closure
condition is not proved here. Establishing it separately inside each
`F_u` would not suffice without a single parameter realizing the
intersection simultaneously in all `r` fibers.

The central generators need not have uniform fibers. Their fibers
are joint-coordinate cells of `(L_h,R_c)`, and the
[documented three/one example](1485_image_research.md#central-joint-coordinates-also-have-nonuniform-fibers)
already rules out that shortcut.

## The exact uniform-marginal test for two central parameters

For central `h,k`, consider the `nr` auxiliary edges
`E_h={(a,b):a B_h b}` and the map

\[
D_k(a,b)=(a,a*(b*k)).
\]

Replacement closure keeps the image in `E_h`. If `D_k` moves
an edge, its second coordinate strictly decreases degree.
Let `N_u` count edges mapped to a second coordinate `u`.
Then the following are equivalent:

1. `N_u=r` for every `u`.
2. `D_k` fixes every edge in `E_h`.
3. `B_h=B_k`.

For 1 implies 2, sum any strictly increasing function of the
second-coordinate degree over the edges. Both the original and
the proposed image marginal are uniform with multiplicity `r`,
so the total is unchanged. Each moved edge would strictly lower
it. For 2 implies 3, fixedness means `b=a*(b*k)` for every
`b∈B_h(a)`, hence `B_h(a)⊆im(L_aR_k)=B_k(a)`. Both sets
have size `r`. The converse is immediate from idempotence.
Thus even preservation of one strictly increasing degree moment is
equivalent to parameter equality, not an independently established fact.

There is an exact expression for the proposed marginal. The central
gate

\[
(a,d)\longmapsto(h*a,a*d),\qquad
M\times Col(h)\longrightarrow Row(h)\times M
\]

is a bijection, with inverse `(t,b)↦(t*b,b*h)`. The inverse
identities are centrality and the weak central laws. Therefore

\[
\boxed{N_u=\sum_{t\in Row(h)}
\#\{b:(t*b)*(b*k)=u\}.}                              \tag{7}
\]

The maps `b↦(t*b)*(b*k)` form the column-dual version of
the band in (5). Their being degree-decreasing does **not** show
that the sum in (7) is `r`. That missing cross-parameter count is
exactly the equality `B_h=B_k` above. Proving it for all central
pairs would finish full core by the next criterion.

## Parameter independence forces full core

Assume every central parameter gives the same relation `B`.
Every top vertex `c` has a central sharp successor `k`, so
`c∈Col(k)`. Hence, for every central `h` and every `a`,

\[
a*c\in B_k(a)=B_h(a).
\]

The successor-fiber characterization of `B_h` says precisely that
`(h*a)*(a*c)=a`. Equation (2) therefore makes `c*u` central for
every `u∈Row(h)`. Every top vertex also has a central sharp
predecessor, so the rows of the central vertices cover `T`.
We conclude `T*T⊆Z`, which is
[equivalent to full core](1485_full_core_equivalences.md).

Equivalently, parameter independence says that every central left
translation and every top right translation have orthogonal fiber
partitions: each of the `r` fibers of the former meets each of the
`s=n/r` fibers of the latter in exactly one element. Indeed this
is exactly injectivity of the joint-coordinate map above.

## A sufficient connectivity condition

Put an undirected graph on the central vertices: join `h,h'` if
their ordinary rows are equal or their ordinary columns are equal.
If the columns are equal, the successor formula above gives
`B_h=B_h'`. If the rows are equal, the predecessor formula gives
the same conclusion. Thus `B_h` is constant on every connected
component of this graph.

In particular, connectedness of this graph proves full core by the
criterion, with no restriction on `|T|`. Every non-full finite model
must have at least two components. This does not assert that the graph
is connected in general, or that disconnectedness alone implies a
non-full core.

The rank argument also applies to one component, without connectivity
of the whole graph. If all parameters in `S⊆Z` give the same
auxiliary relation, let `U=⋃_{h∈S}Row(h)` and
`V=⋃_{h∈S}Col(h)`. Then

\[
\boxed{V*U\subseteq Z.}                          \tag{8}
\]

For `c∈Col(k)`, `k∈S`, parameter equality makes
`λ_{h,c}=id` for every `h∈S`; equation (2) gives
`c*Row(h)⊆Z`, and taking unions proves (8).
In particular, if `k⁺_v,k⁻_u` are the central out/in degrees,
central incidence supplies the useful capacity bounds

\[
|U|\le r k^+_v\quad(v\in V),\qquad
|V|\le r k^-_u\quad(u\in U).
\]

The [nine-top, four-central reduction](1485_four_central_nine_top.md)
uses this component version to exclude a three-central sharing
component even though the entire sharing graph is disconnected.

## An exact overlap Gram matrix

The following finite counting identity, added 20 September 2026, records
the interaction between two central parameters without assuming their
auxiliary relations coincide. Write `n=rs`, and let
`E_h={(a,b):a B_h b}`. Then

\[
\boxed{
 |E_h\cap E_k|
 =\sum_{t\in Row(h)}\operatorname{rank}\lambda_{t,k}
 =\sum_{\substack{t\in Row(h)\\v\in Col(k)}}\frac n{d(v*t)}.
}                                                        \tag{9}
\]

Indeed, the central gate parametrizes `E_h` bijectively by
`(t,b)∈Row(h)×M`, with `a=t*b`. Such an edge also belongs to
`E_k` exactly when

\[
 a*(b*k)=b,
 \quad\text{equivalently}\quad
 \lambda_{t,k}(b)=(t*b)*(b*k)=b.
\]

Every `λ_{t,k}` is idempotent, so its fixed-point count is its
rank. Applying (1) to the opposite magma gives
`rank λ_{t,k}=Σ_{v∈Col(k)}n/d(v*t)`, proving (9).

Consequently the matrix

\[
 H_{hk}:=\sum_{\substack{t\in Row(h)\\v\in Col(k)}}\frac n{d(v*t)}
\]

is symmetric and positive semidefinite, with every diagonal entry
`nr`. This is an ordinary real Gram matrix: its vectors are the
indicators `1_{E_h}` in `R^{M×M}`. In particular, for any real
coefficients `α_h`,

\[
 \sum_{h,k}\alpha_h\alpha_k H_{hk}
 =\sum_{(a,b)\in M^2}
       \left(\sum_{h:(a,b)\in E_h}\alpha_h\right)^2\ge0.
                                                               \tag{10}
\]

The nonnegative defect has two exact descriptions:

\[
\boxed{
 \delta(h,k):=nr-H_{hk}
 =\sum_{\substack{t\in Row(h)\\v\in Col(k)}}
       \left(s-\frac n{d(v*t)}\right)
 =\frac12|E_h\mathbin\triangle E_k|.
}                                                        \tag{11}
\]

Thus `δ` is a pseudometric on the central parameters. Its zero classes
are exactly the classes with equal auxiliary relations. Equivalently,
`δ(h,k)=0` if and only if every product in `Col(k)*Row(h)` is
central. Neither the symmetry nor positive semidefiniteness proves that
the defect vanishes: that remains the full-core problem.

There is also a quantitative restriction when the noncentral top-top
product degrees lie in an interval `[p,q]`, with `r<p≤q`. Let
`N_{hk}` count the noncentral products in `Col(k)*Row(h)`. Then

\[
 (s-n/p)N_{hk}\le\delta(h,k)\le(s-n/q)N_{hk}.       \tag{12}
\]

Symmetry therefore gives
`(s-n/p)N_{hk}≤(s-n/q)N_{kh}` in both directions. The
three-degree product bound permits `q≤min(s,r²)`. For example, if
the least noncentral top-top degree is `p=2r−1`, one obtains the
pure incidence restriction

\[
 \boxed{r N_{hk}\le(2r-1)N_{kh}\quad(h,k\in Z).}    \tag{13}
\]

This follows by using the possibly weaker upper bound `q=r²` in
(12). In particular a one-sided vanishing count is impossible.

### A conditional incidence commutation identity

Let `B` and `C` be the central-to-top and top-to-central adjacency
matrices, as in the
[unrestricted incidence note](1485_unrestricted_central_incidence.md).
Define the central overlap matrices

\[
 U=BB^T,\qquad V=C^TC.
\]

Suppose **every noncentral top-top product has the same degree `p>r`**,
and put `w=n/p`. This is an additional hypothesis; it need not hold in
a prospective counterexample. Then (9) becomes

\[
\boxed{H=w r^2J+(s-w)UV,\qquad UV=VU.}                    \tag{14}
\]

For the first identity, `CB` is the zero-one indicator that a top-top
endpoint pair has a central middle. Such a middle, when present, is
necessarily the product. Therefore the number of central products in
`Col(k)*Row(h)` is

\[
 \sum_{\substack{t\in Row(h)\\v\in Col(k)}}(CB)_{vt}
 =\bigl(B(CB)^TC\bigr)_{hk}
 =(UV)_{hk}.
\]

There are `r²` pairs altogether. Their contributions to (9) are `s`
for a central product and `w` otherwise, proving the formula for `H`.
Both `U,V` are symmetric; symmetry of `H` and `s-w>0` now give
`UV=(UV)^T=VU`. This conclusion uses only the symmetry part of the
Gram theorem. Once commutation holds, `UV` is itself positive
semidefinite, so the positive-semidefinite part of (14) imposes no
additional condition in this single-noncentral-degree case.

For clarity, commutation does not follow from the bare equations
`BC=J`, `CB≤J`, `BD=J`, `DC=J`, even with the standard
central incidence sizes and a regular `D`. Here is an abstract system
with `r=3`, five central labels `0,…,4`, and nine top labels
`0,…,8`. Each line gives `P_t`, `C_t`, and the row support of `D`:

```text
0: {0}   {0}     {0,1,2}
1: {0}   {1,3}   {3,5,6}
2: {0}   {2,4}   {4,7,8}
3: {1,2} {0}     {0,1,6}
4: {3,4} {1}     {0,1,6}
5: {1,2} {1,3}   {3,5,8}
6: {1,2} {2,4}   {2,4,7}
7: {3,4} {0,3}   {3,5,8}
8: {3,4} {2,4}   {2,4,7}
```

The rectangles partition the central square; each central label belongs
to three `P_t` and three `C_t`; every `C_t∩P_u` has size at
most one. The displayed rows of `D` select partitions by `C_t`,
and its columns select partitions by `P_t`. Also every row and
column of `D` has size three. These facts directly verify the stated
matrix conditions. But `U_{00}=3`, all other entries of row zero of
`U` vanish, and `V_{04}=0`, so `(UV)_{04}=0`. In the reverse
direction `U_{43}=3` and `V_{30}=1`, giving `(UV)_{40}=3`.
Thus `UV` is not symmetric. This is **not a magma** or a spectrum
counterexample; it only separates the new necessary condition under
its additional degree hypothesis from the elementary matrix equations.

These are necessary finite constraints, not a new spectrum exclusion.
In particular, they do not establish a uniform marginal for `D_k`,
injectivity of `R_hL_a` on `Col(k)`, or a lower bound on intersections
of the rank-`r²` central retraction images.

## A membership-space criterion for full core

There is a separate sufficient condition involving only the central
incidence matrices. Regard `B` and `C^T` as maps `R^T→R^Z`, and put

\[
 \mathcal W=\operatorname{im}B\cap\operatorname{im}C^T.
\]

For every ordered pair `(a,b)`, its binary parameter-membership vector

\[
 e(a,b)_h=\mathbf1_{a\,B_h\,b}
\]

belongs to `𝒲`. Indeed, the two auxiliary descriptions give the exact
coordinate identities

\[
 e(a,b)_h
 =\sum_{t\in T}B_{ht}\,\mathbf1_{t*b=a}
 =\sum_{v\in T}C_{vh}\,\mathbf1_{a*v=b}.             \tag{15}
\]

Each sum is zero or one: the maps `t↦t*b` on `Row(h)` and
`v↦a*v` on `Col(h)` are injective by centrality. Therefore

\[
 \boxed{\mathcal W\cap\{0,1\}^Z=\{\mathbf0,\mathbf1\}
 \quad\Longrightarrow\quad |Z|=r^2.}                 \tag{16}
\]

Under the hypothesis every edge belongs to all or none of the `B_h`,
so the auxiliary relations coincide, and the proved criterion gives
full core. It suffices, more strongly, that `𝒲=R·1`; the constant
vector belongs to both images because all central row and column
degrees are `r`.

The actual membership patterns satisfy more than real linear
membership. Their support is a disjoint union of blocks `P_t` with
`t*b=a`, and also a disjoint union of blocks `C_v` with `a*v=b`.
Consequently it also suffices that the only subsets of `Z` admitting
both kinds of disjoint-block tiling are `∅` and `Z`. Arbitrary subsets
admitting those tilings are not asserted to be realizable as edge
membership patterns. Neither sufficient condition is proved to hold
for every finite magma; they do not resolve the global rank problem.

## Auxiliary-edge transport and a paired-top target

For central `h,k`, the map

\[
 J_{h,k}:E_h\longrightarrow E_k,\qquad
 (a,b)\longmapsto\bigl(b,\ b*((h*a)*k)\bigr)          \tag{17}
\]

is a bijection, with inverse
`(b,d)↦((h*(d*k))*b,b)`. To see this, parametrize `E_h` by
`(t,b)∈Row(h)×M`, with `a=t*b`. The central transport
`t↦t*k` is a bijection `Row(h)→Col(k)`, with inverse `s↦h*s`.
Finally `(b,s)↦(b,b*s)` parametrizes `E_k`. This proves the
formula and inverse without any degree monotonicity assumption.

The shifted pair supplies a mixed marked path
`a B_h b B_k (b*((h*a)*k))`. Its good replacement retains the
two indicated markings by replacement closure. The bijection does not
establish that this path is already good, or that either original
coordinate decreases degree under an iteration.

One precise **unproved target** is

\[
 s*t\in Z\quad\Longrightarrow\quad
 \lambda_{t,s}(x)=(t*x)*(x*s)=x\quad\text{for every }x. \tag{18}
\]

This is equivalent to every two-edge path in every `B_h` being good.
In one direction, for `a B_h b B_h c`, put `t=h*a` and `s=c*h`.
Then `s*t=h`, `a=t*b`, and `c=b*s`, so (18) gives `a*c=b`.
Conversely, if `s*t=h` is central, then `t∈Row(h)` and
`s∈Col(h)`. For every `x` there is a path
`(t*x) B_h x B_h (x*s)`, and its goodness is (18).

By replacement closure, this is also equivalent to every adjacency
square `B_h²` being zero-one: every existing marked two-edge path has
a good replacement within `B_h`, so uniqueness of the marked middle
is equivalent to its goodness. In that case `B_h²` is `r²`-regular.
The general proof of (18) is missing. It has not been proved here that
the resulting two-edge-path condition alone implies full core.
The known full-core theorem does imply (18), since it makes every
`B_h` sharp adjacency. Knowing only that `s*t` is central gives
the generalized-inverse identities for `L_t,R_s`; these do not by
themselves establish injectivity of their joint-coordinate map.

The [first-output consequence](1485_good_auxiliary_first_output.md)
only assumes this goodness at one least-degree noncentral top output.
It then decomposes that output's good top-pair graph into complete
bipartite blocks and its central parameters into matching classes.
In particular, for `r≥3` a first output of degree `r+1` must have
some bad `B_h` path through it. This identifies a smaller local target;
it does not establish the missing goodness premise.

### Regression checks, separate from proofs

The standalone standard-library script
[1485_central_parameter_check.py](../scripts/1485_central_parameter_check.py)
first verifies E1485 on every supplied table, then checks the two
membership formulas, the overlap/rank identity (9), and the transport
(17) with its explicit inverse. On 20 September 2026 it passed all
394 available models: the 390 public models linked in the
[finite-structure note](1485_graph_research.md#reproducible-finite-table-checks)
and four built-in rectangle/Boolean examples. This checked 19,404
central parameter pairs in 7.402 seconds total on the current machine.
An independent root-agent replay, after reading the checker source,
passed the same 394 models and 19,404 pairs in 7.133 seconds.

The script separately labels (18) as an empirical test. All 19,404
applicable top pairs passed, but all those models already have full
core. Thus this supplies no independent evidence beyond those examples
for the unproved implication. No archive is an exhaustive model search.

```sh
python3 scripts/1485_central_parameter_check.py n8_unique.txt n16-models.txt n18-models.txt
```

## Global coordinate involutions need not commute

The involutions
`F_h(a,b)=((h*a)*b,a*(b*h))` do not furnish a commuting
family on all of `M²`, even in finite full-core models. In zero-based
table 79 of the [public order-sixteen archive](https://leanprover.zulipchat.com/user_uploads/3121/yhypw8DyvXPuEzeZlCVfcgXT/Mace4-1485-size-16-181-models-isofilter-portable.txt),
the central parameters `h=1` and `k=7` give the four-cycle

\[
(8,11)\longmapsto(14,14)\longmapsto(13,11)
\longmapsto(11,14)\longmapsto(8,11)
\]

under `F_1∘F_7`, by direct substitution in that table.
In particular `F_1(F_7(8,11))=(14,14)`, whereas
`F_7(F_1(8,11))=(11,14)`. Both parameters have the minimum
degree two. This rules out a general proof by
commutation of the global involutions; it does not refute their
proposed preservation of the auxiliary relations in finite models.
