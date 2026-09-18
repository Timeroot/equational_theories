# A gap below the full central-core size

Research note, 18 September 2026. This is a pen-and-paper theorem,
not a Lean declaration.

Let `M` be a nonempty finite E1485 magma. Write `r=min d`,
`s=max d`, `n=rs`, and let `Z,T` be its central and top classes.
The known upper bound is `|Z|≤r²`. Define the central defect

\[
\delta=r^2-|Z|.
\]

**Theorem.** If the central core is not full, then

\[
\boxed{\delta\ge r.}                            \tag{1}
\]

Thus no central cardinality lies strictly between `r²−r` and
`r²`. For example, defect two is excluded when `r≥3`, and
defect three when `r≥4`. This
generalizes the [single-defect exclusion](1485_near_full_core.md).
The boundary `δ=r` is subsequently excluded by the
[packing and divisibility argument](1485_boundary_central_defect.md).
Larger defects remain open; neither theorem proves the full-core conjecture.

The proof uses only the established finite degree and uniform-fiber
theorems, existence of sharp neighbors, central incidence, and E1485
itself. In particular it does not assume the full-core quotient theorem.

## 1. A defect smaller than `r` forces exactly `r²` top vertices

Assume for contradiction that

\[
0<\delta<r.
\]

Put `m=|Z|=r²−δ`, `h=|T|`. Let
`B:Z→T`, `C:T→Z` be ordinary incidence and `K=CB`. The
[central incidence identities](1485_unrestricted_central_incidence.md)
give

\[
BC=J_m,\qquad K\le J_T.
\]

Set `k⁺=C1`, `k⁻=Bᵀ1`. These are the central out-degrees and
in-degrees of top vertices, lying in `[1,r]`. Their moments are
`Σk⁺=Σk⁻=rm` and `Σk⁺k⁻=m²`.

Some top vertex `j` must have `k⁻_j=r`. Otherwise integrality
gives `k⁻≤r−1`, and the moments give

\[
m^2=\sum_u k^+_uk^-_u\le(r-1)\sum_u k^+_u=r(r-1)m,
\]

contrary to `m=r²−δ>r(r−1)`.

Put `F=J−K`, a nonnegative zero-one matrix. Since every row of
`B` has sum `r` and `BC=J_m`,

\[
BF=BJ-BCB=\mathbf1(r\mathbf1-k^-)^T.            \tag{2}
\]

The column indexed by `j` is zero. Every top vertex occurs in a
row of `B`, because it has a central predecessor. Nonnegativity
therefore makes the entire column `F_{\cdot j}` zero. The column
`K_{\cdot j}` is all ones, and its sum is `rk⁻_j=r²`. Hence
`h=r²`.

Define the nonnegative integer defects `ε⁺=r1−k⁺`,
`ε⁻=r1−k⁻`, and put `E=Σε⁺=Σε⁻`, `I=Σε⁺ε⁻`.
Expanding the same moments now gives

\[
\boxed{|T|=r^2,\qquad E=r\delta,\qquad I=\delta^2.} \tag{3}
\]

## 2. Every vertex has exactly `r` top neighbors

Because `Σε⁺=rδ<r²=|T|`, some top vertex has full central
out-degree `r`. Its row in the zero-one matrix `K` has sum
`r·r=|T|`, and hence is all ones. Dually `K` has an all-one
column corresponding to a top vertex of central in-degree `r`.

For arbitrary `x∈M`, let `p` indicate its top predecessors.
Unique goodness from central endpoints gives `Bp=1_Z`, and hence
`Kp=k⁺`. Reading this identity in the all-one row gives `Σp=r`.
The dual argument using the all-one column gives

\[
\boxed{|\operatorname{TopPred}(x)|
=|\operatorname{TopSucc}(x)|=r\quad(x\in M).}    \tag{4}
\]

## 3. Full central in-degree and out-degree must coincide

Fix `u∈T` with `k⁻_u=r`. We show that every product `u*v`,
`v∈T`, is central. Suppose instead that `a=u*v` is noncentral.

The central predecessor set `P=Z∩Col(u)` has size `r`. For
each `c∈P`, choose `z` with `z*u=c`. Because the output is
central, `z` is top. Put `b=v*c`, also top. The central path
`b→c→u` gives `b*u=c`, so the map `c↦v*c` is injective.
By (4), its `r` values exhaust `TopSucc(v)`. E1485 gives

\[
(u*v)*(v*(z*u))=v,
\]

and therefore

\[
a*b=v\qquad(b\in\operatorname{TopSucc}(v)).    \tag{5}
\]

For any central `h`, the top vertex `v*h` belongs to this
successor set, so `a*(v*h)=v`. In terms of the
[regular auxiliary relation](1485_sharp_degree_defect.md), this says
`v∈a*Col(h)=B_h(a)`. Its fiber identity yields

\[
(h*a)*v=a\qquad(h\in Z).                       \tag{6}
\]

Unconditionally `Z*a=TopPred(a)`. The forward inclusion follows
from centrality. Conversely, a top predecessor `t→a` has a
central sharp predecessor `h→t`, and the central path `h→t→a`
gives `h*a=t`. By (4), this central shadow has `r` elements.
Equation (6) therefore puts `r` distinct top inputs into
`R_v⁻¹(a)`, a size-`r` fiber.

There is one more input. Choose a sharp predecessor `f` of `a`.
Since `a` is noncentral, `d(f)=n/d(a)<s`, so `f` is not top.
The path `f⇒a→v` is good, giving `f*v=a`. This contradicts the
fiber size and proves that every `u*v`, `v∈T`, is central.

The row of `K` indexed by `u` is consequently all ones; its row
sum `rk⁺_u=|T|=r²` gives `k⁺_u=r`. Applying the dual proof
gives the converse. We have proved

\[
\boxed{k^-_u=r\quad\Longleftrightarrow\quad k^+_u=r
\quad(u\in T).}                               \tag{7}
\]

This step only requires `|T|=r²` and (4), not the numerical
small-defect bound used to establish them.

## 4. The two defect moments contradict each other

Equation (7) says that the nonnegative integer vectors `ε⁺,ε⁻`
have the same positive support. Thus `ε⁻_u≥1` whenever
`ε⁺_u>0`, and

\[
\delta^2=\sum_u\varepsilon^+_u\varepsilon^-_u
\ge\sum_u\varepsilon^+_u=r\delta,
\]

using (3). Since `δ>0`, this gives `δ≥r`, contradicting
`δ<r`. The contradiction proves (1).

In particular, whenever `|T|=r²` and every vertex has `r` top
predecessors and successors, either the core is full or its defect
is at least `r`. The first two sections force precisely these
structural hypotheses whenever `0<δ<r`.
