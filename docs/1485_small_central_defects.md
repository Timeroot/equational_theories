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
\boxed{\delta(\delta+1)>r.}                    \tag{1}
\]

Thus `0<δ` and `r≥δ(δ+1)` cannot occur. For example, defect two
is excluded when `r≥6`, and defect three when `r≥12`. This
generalizes the [single-defect exclusion](1485_near_full_core.md).
It does not exclude larger defects or finish the full-core conjecture.

The proof uses only the established finite degree and uniform-fiber
theorems, existence of sharp neighbors, central incidence, and E1485
itself. In particular it does not assume the full-core quotient theorem.

## 1. A sufficiently small defect forces exactly `r²` top vertices

Assume for contradiction that

\[
0<\delta,\qquad r\ge\delta(\delta+1).
\]

In particular `δ<r`. Put `m=|Z|=r²−δ`, `h=|T|`. Let
`B:Z→T`, `C:T→Z` be ordinary incidence and `K=CB`. The
[central incidence identities](1485_unrestricted_central_incidence.md)
give

\[
BC=J_m,\qquad K\le J_T.
\]

Set `k⁺=C1`, `k⁻=Bᵀ1`. These are the central out-degrees and
in-degrees of top vertices, lying in `[1,r]`. Each central vertex
has `r` top successors, whose `k⁺` sum to `m=r²−δ`. Hence
each of those entries is at least `r−δ`. Every top vertex has a
central predecessor, so the bound holds everywhere. Its dual gives

\[
k^+=r\mathbf1-\varepsilon^+,
\qquad k^-=r\mathbf1-\varepsilon^-,
\qquad 0\le\varepsilon^\pm\le\delta.
\]

Let `E=Σε⁺=Σε⁻` and `I=Σε⁺ε⁻`. The first and second
central-incidence moments give

\[
E=r(h-m),\qquad I=r^2(h-r^2)+\delta^2.           \tag{2}
\]

Write `a=h−r²`. Since `I≥0` and `δ<r`, integrality forces
`a≥0`. Also `I≤δE`, so

\[
r(r-\delta)a\le\delta^2(r-1).
\]

Under `r≥δ(δ+1)`, the coefficient on the left strictly exceeds
the right-hand bound:

\[
r(r-\delta)-\delta^2(r-1)
=r\bigl(r-\delta(\delta+1)\bigr)+\delta^2>0.
\]

Thus `a<1`, and therefore

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
structural hypotheses for the smaller defects covered by the theorem.
