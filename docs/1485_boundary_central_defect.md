# The boundary central defect is impossible

Research note, 18 September 2026. This is a pen-and-paper proof, not a
Lean declaration. Write `n=rs` for the order of a finite E1485 magma,
where `r=min d` and `s=max d`. Let `Z,T` be the central and top
classes, and put `m=|Z|`, `h=|T|`.

**Theorem.** The central cardinality `m=r²−r` is impossible.
Together with the [strict-gap theorem](1485_small_central_defects.md),
this gives, for `r≥2`,

\[
\boxed{|Z|=r^2\quad\text{or}\quad |Z|\le r^2-r-1.} \tag{1}
\]

The full-core conjecture remains open: this theorem excludes the
boundary of the previously established gap, not every smaller core.
The [quantitative extension](1485_second_central_defect_gap.md) rules
out some further defects by measuring the slack in the same count.
The proof below establishes the new boundary exclusion for `r≥3`.
For `r=1`, the proposed boundary would have no central vertex; for
`r=2`, the already proved [full-core theorem](1485_two_central_exclusion.md)
excludes it.

## 1. A general packing bound for missing top products

Let `B:Z→T` and `C:T→Z` be ordinary adjacency, and set

\[
K=CB,\qquad F=J-K,\qquad
k^-=B^T\mathbf1,\qquad k^+=C\mathbf1.
\]

The [central-incidence identities](1485_unrestricted_central_incidence.md)
give `BC=J_m`, `K≤J`, and `Σk⁻=Σk⁺=rm`.
Thus `F` is zero-one and `F_uv=1` exactly when `u*v` is
noncentral. All entries of `k⁻,k⁺` lie in `[1,r]`.

For a top vertex `v`, write `ε_v=r−k⁻_v`, and let
`Q_v=TopSucc(v)`. We prove the packing inequality

\[
\boxed{m\le(r-1)|Q_v|\qquad\text{whenever }\varepsilon_v>0.}
                                                        \tag{2}
\]

Fix `u∈T` with `F_uv=1`. For each central predecessor
`c∈Z∩Col(u)`, choose `z` with `z*u=c`; the input `z`
is top because its output is central. Put `b=v*c`, also top.
The central path `b→c→u` gives `b*u=c`, so `c↦v*c`
is injective. Its image `S_{u,v}` lies in `Q_v` and has exactly
`k⁻_u` elements. E1485 gives

\[
(u*v)*b=(u*v)*(v*(z*u))=v
\qquad(b\in S_{u,v}).                           \tag{3}
\]

Count the pairs `(u,b)` with `F_uv=1` and `b∈S_{u,v}`.
Their number is

\[
\sum_{u:F_{uv}=1}k^-_u=m\varepsilon_v.           \tag{4}
\]

Indeed `k⁻ᵀC=1ᵀBC=m1ᵀ`, so

\[
(k^-)^TF=rm\mathbf1^T-m(k^-)^T
=m(r\mathbf1-k^-)^T.
\]

For a fixed `b∈Q_v`, equation (3) places the noncentral value
`a=u*v` in the size-`r` fiber `R_b⁻¹(v)`. Exactly `k⁻_v`
inputs in that fiber are central: they are the central predecessors
of `v`, since `v→b` and central-endpoint paths are good. Hence
at most `ε_v` distinct noncentral values `a` can occur for this
fixed `b`.

Each such value `a` has at most `r−1` top preimages under `R_v`.
To see this, choose a sharp predecessor `f⇒a`. The path
`f⇒a→v` is good, giving `f*v=a`. Moreover `f` is not top,
because `d(f)d(a)=n` and `a` is noncentral. Thus the size-`r`
fiber `R_v⁻¹(a)` already has a non-top input.

There are consequently at most `ε_v(r−1)` counted pairs for
each `b`. Summing over `Q_v` and using (4) proves (2).

## 2. Equality forces top fibers of size `r−1`

Suppose equality holds in (2). Then (4) attains the sum of all
the per-`b` upper bounds. Every bound is therefore an equality.
In particular, for every noncentral value `a` contributing at a
given `b`, all `r−1` possible top preimages of `a` under `R_v`
must contribute at that `b`.

Every noncentral top-input output class participates at some `b`:
choose any `u∈T` with `u*v=a`; its set `S_{u,v}` is nonempty
because `k⁻_u≥1`. Thus every noncentral output of `R_v` on
top inputs has **exactly `r−1` top preimages**. These classes
partition the missing column of `F`, so

\[
\boxed{r-1\mid h-rk^-_v}
\quad\text{whenever equality holds in (2).}      \tag{5}
\]

This saturation argument counts the entire top fiber, not just a
chosen subset: the participating subset has size `r−1`, and the
whole top fiber has already been bounded above by `r−1`.

## 3. The boundary reduces to equality in the packing bound

Assume now `r≥3` and `m=r(r−1)`. We show, possibly after
passing to the dual magma, that

\[
h=r^2,\qquad |TopSucc(x)|=r\quad(x\in M).        \tag{6}
\]

First suppose some top `j` has `k⁻_j=r`. The identity

\[
BF=\mathbf1(r\mathbf1-k^-)^T
\]

makes column `j` of `BF` zero. Every top vertex occurs in
some row of `B`, since every top vertex has a central predecessor.
Nonnegativity forces column `j` of `F` to be zero. Thus that
column of `K` is all ones; its sum is `rk⁻_j=r²`, proving
`h=r²`.

For arbitrary `x`, let `q` indicate `TopSucc(x)`. Central-endpoint
uniqueness gives `qᵀC=1ᵀ`, hence `qᵀK=(k⁻)ᵀ`. Reading
this in the all-one column `j` gives `|TopSucc(x)|=r`.
This proves (6) in this case.

Otherwise every `k⁻≤r−1`. The incidence moments give

\[
m^2=\sum_u k^+_uk^-_u
\le(r-1)\sum_u k^+_u=r(r-1)m=m^2.
\]

Equality and `k⁺_u>0` force `k⁻_u=r−1` for every top vertex.
Then `h(r−1)=rm`, so again `h=r²`. For the indicator `p`
of `TopPred(x)`, the identity `Bp=1` gives

\[
(r-1)|TopPred(x)|=m=r(r-1).
\]

Thus every vertex has `r` top predecessors. Passing to the dual
magma proves (6), with no need to assume the other central-degree
vector is constant.

## 4. The final divisibility contradiction

Work in the orientation (6). For every top `v` with `ε_v>0`,
the packing bound is an equality:

\[
m=r(r-1)=(r-1)|Q_v|.
\]

Equation (5) now says `r−1` divides
`r²−rk⁻_v=rε_v`. Since `gcd(r,r−1)=1`,

\[
r-1\mid\varepsilon_v.
\]

The same divisibility is automatic when `ε_v=0`. Because
`1≤k⁻_v≤r`, all deficits lie in `[0,r−1]`; they are therefore
either zero or `r−1`. But their sum is

\[
\sum_{v\in T}\varepsilon_v
=rh-rm=r\bigl(r^2-r(r-1)\bigr)=r^2.
\]

It follows that `r−1` divides `r²`, hence divides one. This is
impossible for `r≥3`, completing the boundary exclusion and (1).
