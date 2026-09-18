# A regular subgraph and a scalar test for sharp-degree regularity

Research note, 18 September 2026. These are pen-and-paper consequences of
the [finite structure theorems](1485_graph_research.md). They isolate a
remaining structural question; they do **not** prove the complete spectrum
conjecture. Put `n=|M|`, `r=min d`, and `s=max d`, so `rs=n`.

## A regular spanning subgraph attached to a central vertex

Fix a central vertex `h`, and put `C=Col(h)`. It has size `r`, and
every `c∈C` has degree `s`. Define a directed relation

\[
 a\mathrel{B_h}u\quad\Longleftrightarrow\quad
 u=a*c\text{ for some }c\in C.
\]

This is a subrelation of ordinary adjacency. It has **exactly `r`
successors and `r` predecessors at every vertex**.

For the out-degree, centrality gives `(a*c)*h=c` for `c∈C`.
Thus `c↦a*c` is injective on `C`. For the in-degree, the sets
`Col(c)`, for `c∈C`, partition `M`: they are exactly the nonempty
fibers of `R_h`, since `c⇒h`. An output `u` can therefore occur as
`a*c` for exactly one parameter `c`, namely `c=u*h`. For this
parameter, the uniform-fiber theorem gives exactly `n/d(c)=r`
choices of `a`.

The successors of `a` in this relation are also

\[
 B_h(a)=\operatorname{im}(L_aR_h)
       =L_{h*a}^{-1}(a).
 \tag{1}
\]

In particular they contain every sharp successor of `a`: sharp
successors are fixed by every mixed projection. Thus, writing `S`
for sharp adjacency and `A` for ordinary adjacency,

\[
 S\subseteq B_h\subseteq A,
 \qquad B_h\mathbf1=B_h^T\mathbf1=r\mathbf1.
 \tag{2}
\]

It is not yet proved that the first inclusion is an equality.

## A nonnegative scalar defect

Define

\[
 \Delta=\sum_{x\in M}d(x)-n\sum_{x\in M}\frac1{d(x)}.
\]

Every ordinary edge `a→u` satisfies `d(a)d(u)≥n`. Sum its
nonnegative reciprocal-degree slack over the edges of `B_h`. Using
both regularity statements in (2) gives the exact identity

\[
 \boxed{
 \sum_{a\,B_h\,u}
 \left(\frac{d(a)}n-\frac1{d(u)}\right)
 =\frac rn\Delta\ge0.
 }
 \tag{3}
\]

In particular `Δ≥0`. Moreover, equality holds precisely when every
edge of `B_h` is sharp, by the tight-edge characterization. As `S`
is contained in `B_h`, this is equivalent to `S=B_h`.

Consequently the following are equivalent:

1. `Δ=0`.
2. Every vertex has exactly `r` sharp successors.
3. Every vertex has exactly `r` sharp predecessors.
4. Sharp adjacency is `r`-regular in both directions.
5. For one central `h`, `B_h=S`.
6. For every central `h`, `B_h=S`.

Indeed, equality in (3) proves the implications from 1. Conversely,
if every sharp out-degree is `r`, inclusion in the `r`-element sets
`B_h(a)` gives equality of relations, and hence regularity in both
directions and `Δ=0`. The same argument with in-degrees proves the
remaining implications.

Thus a reverse inequality `Δ≤0` would settle sharp-degree regularity.
It is a proposed target, not an inequality established here. The later
[equivalence theorem](1485_full_core_equivalences.md) identifies sharp
regularity with full core; the
[full-core quotient theorem](1485_full_core_quotient.md) now establishes
the goodness-reflecting Boolean quotient under this one hypothesis.
Thus there is no longer a separate open quotient requirement.

## Equivalent behavior of maximum-degree translations

There is a further equivalent formulation:

\[
 \boxed{d(t*x)=d(x*t)=n/d(x)
 \quad\text{for every maximum-degree }t\text{ and every }x.}
 \tag{4}
\]

To see this from regularity, choose a central sharp successor `h` of
`t`; then `t∈Col(h)`, so `x*t∈B_h(x)=S(x)` and has degree
`n/d(x)`. Apply the dual argument to `t*x`. Conversely, (4) makes
every edge of every `B_h` sharp and therefore gives (3) with equality.

In particular, (4) says that a maximum-degree translation has constant
ordinary degree on each of its fibers. This also suffices for (4):
if `t*x=u`, its nonempty fiber contains a sharp successor `v` of
`u`. Indeed `t→u⇒v` is good, so `t*v=u`. Such a `v` has degree
`n/d(u)`; constancy on the fiber gives `d(x)=n/d(u)`. The dual
argument treats right translations. Thus degree preservation by the
kernel-mate involutions at `r=2` is another form of the same target,
not a consequence of uniform fiber cardinalities alone.

## Degree-distribution inequalities

More generally, for any nondecreasing real-valued function `φ` on the
positive degrees and their complements, each edge of `B_h` satisfies
`φ(d(u))≥φ(n/d(a))`. Regularity gives

\[
 \boxed{\sum_x\varphi(d(x))\ge
             \sum_x\varphi(n/d(x)).}
 \tag{5}
\]

For example, taking `φ=log` shows

\[
 \prod_x d(x)\ge n^{n/2}.
\]

Taking the indicator of an upper interval gives the corresponding
inequalities for the counts in the degree classes. In particular, if
`r<s`, the maximum-degree class has at least as many elements as the
central class. These are necessary conditions only. They allow a
strict excess of high-degree vertices and do not prove that opposite
degree classes have equal cardinalities.
