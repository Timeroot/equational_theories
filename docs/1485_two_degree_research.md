# Finite E1485 models with two translation degrees

Research note, 18 September 2026. This note assumes the finite-structure
theorems proved in [the graph research note](1485_graph_research.md). It
proves a sharper two-degree bound, settles the two-degree case with minimum
degree two, and excludes every order `2p` and `3p` with `p>3` prime
(as well as order six), and every odd prime cube. It does not classify
all two-degree multiplication tables. The cardinality question is now
settled for all two-degree models by the subsequent proof linked below.

For the strongest subsequent results, see the
[mixed-five-cycle bound](1485_two_degree_lower_bound.md): it proves
`s=2r` for every two-degree model, and classifies the stronger structural
parameters for every minimum degree `r≤9`;
the [small-degree completion](1485_small_degree_completion.md) extends
the classification through `r=11`.
The [constant-sharp-degree theorem](1485_constant_sharp_degree.md)
handles every `r` under the indicated constancy hypothesis. The
[sharp-degree-one exclusion](1485_k1_exclusion.md) supplies another
ingredient in the improved bounds. All these additions are pen-and-paper
proofs, not new Lean declarations.

Write `d(a)=|Row(a)|=|Col(a)|`, and let `n` be the order. Recall that every
nonempty translation fiber at `a` has size `n/d(a)`, and that
`P_b(t)=a*(t*b)` is idempotent with rank `n/d(b*a)`.

## A weighted balance identity

In every finite E1485 model, for each vertex `a`,

\[
 \sum_{u\in\operatorname{Row}(a)}\frac1{d(u)}
 =\sum_{v\in\operatorname{Col}(a)}\frac1{d(v)}. \tag{1}
\]

Count solutions of `x*y=a`. For fixed `x`, a solution exists precisely
when `x∈Col(a)`, by the equivalence of the two descriptions of the operation
graph; there are then `n/d(x)` choices of `y`. Counting instead with `y`
fixed gives `n/d(y)` choices of `x` for each `y∈Row(a)`. Thus

\[
 \#\{(x,y):x*y=a\}
 =n\sum_{x\in\operatorname{Col}(a)}\frac1{d(x)}
 =n\sum_{y\in\operatorname{Row}(a)}\frac1{d(y)}. \tag{2}
\]

Cancel the positive factor `n` to obtain (1).

## Two-degree moment equations

Suppose the two distinct degrees are `r<s`. Then `n=rs`. Let `Z` be the
central set, of size `m`, and put `H=M\Z`, of size `h=rs-m`. The vertices
of `Z` have degree `r`; those of `H` have degree `s`. Every edge incident
with `Z` goes between `Z` and `H`, and is sharp. Edges within `H` are not
sharp. Every vertex has sharp neighbors.

Equation (1), together with ordinary in/out-degree equality, shows that
each high vertex has equally many central predecessors and central
successors. Denote this number by `k_v`; then `1≤k_v≤r`.

In the ordering `Z,H`, write ordinary adjacency as

\[
 A=\begin{pmatrix}0&B\\ C&D\end{pmatrix}.
\]

Every path containing a central vertex is good. Therefore uniqueness of
good paths gives

\[
 BC=J_{m,m},\qquad BD=J_{m,h},\qquad DC=J_{h,m}. \tag{3}
\]

All rows of `B` and all columns of `C` sum to `r`; column `v` of `B`
and row `v` of `C` both sum to `k_v`. Counting edges and then summing all
entries of `BC` gives the exact moment equations

\[
 \boxed{\sum_{v\in H}k_v=mr,\qquad
        \sum_{v\in H}k_v^2=m^2.} \tag{4}
\]

In particular `r≤m≤r²`, and Cauchy--Schwarz gives `h≥r²`.
The integrality relation `k_v²≡k_v (mod 2)` also gives
`m(m-r)≡0 (mod 2)`; if `r` is even, `m` is even.

Since `(k_v-1)(k_v-r)≤0`, equations (4) imply

\[
 m^2\le(r+1)mr-r(rs-m)
       =r(r+2)m-r^2s.
\]

Thus

\[
 \boxed{m^2-r(r+2)m+r^2s\le0,
        \qquad s\le\left\lfloor\frac{(r+2)^2}{4}\right\rfloor.} \tag{5}
\]

For `r=2`, the moment inequality is an equality, since `k_v∈{1,2}`:

\[
 (m-4)^2=4(4-s). \tag{6}
\]

Since `s>2`, this leaves only `(s,m)=(3,2)` or `(4,4)`.
The next argument rules out the first case without a SAT computation.

## Excluding the degree pair `(2,3)`

Suppose `r=2,s=3`. Equation (6) gives `m=2`, `h=4`, and (4) implies
`k_v=1` for every high vertex. Label the central vertices by `0,1`.
Each high vertex has one central predecessor and one central successor.
The identity `BC=J₂` says that there is exactly one high vertex with
any prescribed pair `(i,j)` of these labels. Thus identify

\[
 H=\{(i,j):i,j\in\{0,1\}\},\qquad i\to(i,j)\to j.
\]

Each high vertex has two high successors. The identity `DC=J₄,₂` says
that, for each target second coordinate `l`, exactly one target first
coordinate `k` is a successor. Similarly `BD=J₂,₄` says that, for each
source first coordinate `i`, exactly one source second coordinate `j`
is a predecessor. For each fixed `i,l`, the map between `j` and `k` is
therefore a permutation of two labels. There are bits `t_{il}` such that

\[
 (i,j)\to(k,l)\quad\Longleftrightarrow\quad
 j=k\mathbin\oplus t_{il}, \tag{7}
\]

where `⊕` is addition modulo two. Centrality and unique goodness then
determine the products involving a central element:

\[
 i*j=(i,j),\qquad
 i*(k,l)=(i,k\oplus t_{il}),\qquad
 (i,j)*l=(j\oplus t_{il},l). \tag{8}
\]

The product of `(i,j)` and `(k,l)` is central if and only if `j=k`;
in that case it equals `j`. Indeed any central middle vertex must be
both the unique central successor of `(i,j)` and the unique central
predecessor of `(k,l)`, and any such path is good.

Apply

\[
 (y*x)*(x*(z*y))=x
\]

with `x=(i,j)`, `y=a`, and `z=1⊕j`, where `y,z` are central. By (8),
`z*y=(1⊕j,a)`. Since `j≠1⊕j`, write the high product

\[
 x*(z*y)=(p,q).
\]

The left factor `y*x` is `(a,i⊕t_{aj})`. Its product with `(p,q)`
equals the high vertex `x`, so the central-product criterion gives
`p≠i⊕t_{aj}`. The good path from `x` through `(p,q)` to `z*y`, and
(7), now give three necessary bit equations:

\[
 p=1\oplus i\oplus t_{aj},\qquad
 q=1\oplus j\oplus t_{pa},\qquad
 p=j\oplus t_{iq}. \tag{9}
\]

First take `i=j=a=0`. If `t₀₀=1`, the first two equations give
`p=q=0`, contradicting the third equation. Hence `t₀₀=0` and `p=1`.
If `t₁₀=1`, the second equation gives `q=0`, again contradicting
the third. Therefore

\[
 t_{00}=t_{10}=0,\qquad t_{01}=1. \tag{10}
\]

Next take `i=j=a=1`. If `t₁₁=1`, then `p=q=1`, contradicting the
third equation. Thus `t₁₁=0` and `p=0`. If `t₀₁=1`, then `q=1`,
again contradicting the third equation. Hence `t₀₁=0`, contradicting
(10). This excludes the degree pair `(2,3)`.

Consequently **every finite E1485 model with exactly two translation
degrees and minimum degree two has order eight and degree pair `(2,4)`**.

## A five-cycle restriction on the remaining good paths

If `e→a→b` is a good path entirely inside `H`, then

\[
 \boxed{k_e+k_b\le r.} \tag{11}
\]

For each central predecessor `z` of `e`, put `c=b*z`. This lies in `H`,
and `b→c→z` is good. The five-cycle

\[
 e\to a\to b\to c\to z\to e
\]

therefore makes `a→b→c` good. Distinct `z` give distinct `c`: otherwise
`c→z→e` and `c→z'→e` would be two good paths with the same endpoints,
since their middle vertices are central. We have produced `k_e` distinct
high extensions of the edge `a→b`.

The fiber `{c:a*c=b}` has size `r`. Its central elements are exactly the
`k_b` central successors of `b`, because every path ending at a central
vertex is good. Hence there are precisely `r-k_b` high extensions,
proving (11).

Put `E=J_{h,h}-CB`. The matrix `CB` is zero-one: its entries count paths
with a central middle vertex, all of which are good. Thus `E` is the
zero-one relation of pairs whose unique good middle vertex lies in `H`.
Writing `k` as a column vector, the block identities give

\[
 E\mathbf1=E^T\mathbf1=h\mathbf1-rk,
\]
\[
 \boxed{E^2=hJ-r(\mathbf1k^T+k\mathbf1^T)+kk^T.} \tag{12}
\]

Indeed `(CB)²=C(BC)B=CJB=kkᵀ`, while the row and column sums of
`CB` are `rk`. By (11), `E_{uv}=1` is possible only when `k_u+k_v≤r`.

### A bound on large sharp degrees

If some vertex has sharp degree `k`, then

\[
 \boxed{\#\{v\in H:k_v>r-k\}\le k^2.} \tag{13}
\]

Fix that vertex `u`. Its out- and in-neighbor sets for `E` both have
size `h-rk`, and both lie in the set of vertices of sharp degree at most
`r-k`. If the excluded set has size `N`, their intersection therefore
has size at least `h-2rk+N`. On the other hand, (12) identifies that
intersection size with `(E²)_{uu}=h-2rk+k²`. This proves (13).

If **any** high vertex has sharp degree `r`, (13) gives `h≤r²`.
Cauchy--Schwarz already gives `h≥r²`, so equality holds. Equality in
Cauchy--Schwarz in (4) makes all `k_v` equal; the specified vertex makes
their common value `r`. Consequently

\[
 m=h=r^2,\qquad s=2r. \tag{14}
\]

In particular every path between high vertices then has its good middle
vertex in `Z`: `CB` has row sum `r²=h`, so `CB=J`.

## Excluding order fifteen

At order fifteen there can be no constant row, since the constant-row
classification gives power-of-two order. Degree divisibility and
`d_min*d_max=15` therefore force precisely the degrees `r=3,s=5`.

No high vertex can have sharp degree three: (14) would force `s=6`.
Thus all sharp degrees on `H` are one or two. For such integers,
`k²=3k-2`, so the moments give

\[
 m^2=3(3m)-2(15-m),\qquad (m-5)(m-6)=0.
\]

If `m=5`, then `h=10`; the first moment forces five sharp degrees to
be two and five to be one. If `m=6`, then `h=9` and all sharp degrees
are two. But applying (13) with `r=3,k=2` permits **at most four**
vertices of sharp degree greater than one. Both possibilities contradict
this. Hence **order fifteen is excluded** without SAT.

## Spectrum consequences

Let `p<q` be distinct primes. If a model has order `pq`, constant rows
are impossible by the power-of-two classification. Degree divisibility
and `d_min*d_max=pq` therefore leave exactly the degrees `p,q`.
The bound (5) gives the necessary condition

\[
 \boxed{q\le\left\lfloor\frac{(p+2)^2}{4}\right\rfloor.} \tag{15}
\]

This improves the earlier elementary bound `q≤p(p+1)`, which follows
by counting sharp neighbors of the at most `p²` central vertices.

For `p=2`, the classification above permits only degree pair `(2,4)`,
inconsistent with `q` prime. Thus **every order `2q` with `q` an odd
prime is excluded**. For `p=3`, (15) leaves only `q=5`; the preceding
argument excludes fifteen. Thus **every order `3q` with prime `q>3`
is excluded** too. Together with the order-six proof, the first two
prime factors are now handled completely for nonsquare semiprimes.

There is also an exclusion not restricted to semiprimes. If `n=p³` for
an odd prime `p`, constant rows are again impossible. Degree divisibility
and the extremal product force precisely `r=p,s=p²`. But (5) would give
`4p²≤(p+2)²`, or `(3p+2)(p-2)≤0`, impossible for `p≥3`.
Thus **every odd prime cube is absent from the spectrum**. The exception
`p=2` gives order eight, which does occur.

These are pen-and-paper consequences of the finite-structure theorems.
This note does not introduce Lean declarations or use reported SAT runs.

## Remaining obstruction

The moment equations and bound do not force `s=2r` for general `r`.
For example, `r=3,s=4,m=3` satisfies the moment equations with nine
high vertices all having sharp degree one, and is not eliminated by
(11)--(13) alone. The subsequent five-cycle arguments linked at the top
**do exclude it**, and now force standard parameters for every `r≤11`.
Any remaining structurally nonstandard two-degree model must have
`r≥12` and nonconstant sharp degrees. Its order is already known to
be `2r²`, so it is not a remaining spectrum obstruction. See the
[general degree-pattern reduction](1485_spectrum_reduction.md) for the
remaining spectrum problem.

A general proof still has to use additional multiplication or good-path
constraints. In particular this note does not show that every good path
between two high vertices has a central middle vertex. That stronger
property would give `CB=J_{h,h}`, yielding `h=m=r²` and `s=2r` by the
standard two-fiber matrix argument.

## Reproduction and status

[1485_structure_check.py](../scripts/1485_structure_check.py) checks the
weighted balance, the two-degree moment equations, the endpoint inequality,
the exact `E²` entries, and the tail bound on supplied tables. The 390
archived tables and twisted order-32 model pass; 209 of those tables have
exactly two degrees. The script also checks all 16 possible bit patterns
in the order-six reduction and both feasible moment patterns at order
fifteen. These are regression checks of the displayed arguments, not
exhaustive searches at the excluded orders and not Lean verification.

The model-bank links and invocation are in the
[graph note](1485_graph_research.md#reproducible-finite-table-checks).
