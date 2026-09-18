# Extending the forbidden interval of central defects

Research note, 18 September 2026. This is a pen-and-paper theorem,
not a Lean declaration.

Let `M` be a nonempty finite E1485 magma, with minimum and maximum
translation degrees `r,s`, order `n=rs`, central class `Z`, and top
class `T`. Write `m=|Z|`, `h=|T|`.

**Theorem.** If `η≥1` and `r≥η(η+1)+2`, then

\[
\boxed{|Z|\ne r(r-1)-\eta.}                    \tag{1}
\]

Equivalently, a central defect `δ=r²−|Z|` cannot equal `r+η`
under this bound. Thus defect `r+1` is excluded for `r≥4`,
defect `r+2` for `r≥8`, and defect `r+3` for `r≥14`.
This extends the [first gap](1485_small_central_defects.md) and
the [boundary exclusion](1485_boundary_central_defect.md), but does
not exclude every smaller-than-full central core.

The proof uses finite uniform fibers, existence of sharp neighbors,
central incidence, and the original E1485 identity. It does not
presuppose the full-core quotient theorem.

## 1. A quantitative packing inequality

Assume temporarily that

\[
h=r^2,\qquad m=r(r-1)-\eta,
\]

and fix `v∈T` having exactly `r` top successors. Let
`k⁻_v=|Z∩Col(v)|`, and suppose

\[
\varepsilon=r-k^-_v>0.
\]

We prove

\[
\boxed{(\eta+1)\varepsilon\ge r-1.}            \tag{2}
\]

Use the central incidence matrices `B:Z→T`, `C:T→Z`, and put
`K=CB`, `F=J−K`. Thus `K` detects central-valued top products
and `F` detects noncentral-valued ones. Central endpoint uniqueness
gives `BC=J_m`, and hence

\[
BF=\mathbf1(r\mathbf1-k^-)^T.
\]

Let `S={u∈T:u*v∉Z}`. The column sum of `F` at `v` gives
`|S|=rε`. Summing the displayed identity down the same column
counts the pairs

\[
(u,c),\qquad u\in S,\quad c\in Z\cap\operatorname{Col}(u):
\qquad \#\{(u,c)\}=m\varepsilon.               \tag{3}
\]

For each such pair choose top `z` with `z*u=c`, and put `b=v*c`.
The value `b` is a top successor of `v`. The central path
`b→c→u` gives `b*u=c`, so for fixed `u` the map `c↦b` is
injective. E1485 gives

\[
(u*v)*b=(u*v)*(v*(z*u))=v.
\]

For each distinct noncentral output `a∈S*v`, define

\[
p_a=\#\{u\in T:u*v=a\},\qquad
t_a=\#\{b\in\operatorname{TopSucc}(v):a*b=v\}.
\]

Here `t_a≥1`, since every top vertex has a central predecessor.
The injection just described and (3) give

\[
m\varepsilon\le\sum_a p_at_a.                 \tag{4}
\]

For fixed `b∈TopSucc(v)`, the size-`r` fiber `R_b⁻¹(v)`
contains exactly the `k⁻_v=r−ε` central predecessors of `v`.
Therefore it has exactly `ε` noncentral inputs. There are `r`
choices of `b`, so

\[
\sum_a t_a\le r\varepsilon.                    \tag{5}
\]

Also `Σ_a p_a=rε`, and each `p_a≤r−1`. Indeed the fiber
`R_v⁻¹(a)` has size `r`, and it contains a non-top sharp
predecessor of the noncentral vertex `a`, in addition to its top
inputs. Thus there are at least `ε+1` distinct outputs `a`.
Combining (4), (5), and `t_a≥1`,

\[
\begin{aligned}
\eta\varepsilon
&=r(r-1)\varepsilon-m\varepsilon\\
&\ge\sum_a(r-1-p_a)t_a\\
&\ge\sum_a(r-1-p_a)\\
&\ge(r-1)(\varepsilon+1)-r\varepsilon
=r-1-\varepsilon.
\end{aligned}
\]

This proves (2). The exceptional inputs in (5) need only be
noncentral; they are allowed to be top.

## 2. The branch with a full central degree

Now assume the hypotheses of the theorem and suppose, by duality,
that some top vertex has full central in-degree `r`.

The [incidence argument in the first gap](1485_small_central_defects.md)
applies without a small-defect assumption: if `k⁻_j=r`, the
column `j` of `BF` is zero; because every top index occurs in
`B`, the column `F_{\cdot j}` is zero. Its complementary column
of `K` is all ones and has sum `rk⁻_j=r²`. Thus `h=r²`.
Reading arbitrary central endpoint incidence against this column
also gives

\[
|\operatorname{TopSucc}(x)|=r\qquad(x\in M).   \tag{6}
\]

Consequently (2) applies to every positive central in-degree defect
`ε⁻_v=r−k⁻_v`. Our numerical hypothesis implies

\[
\varepsilon^-_v>0\quad\Longrightarrow\quad
\varepsilon^-_v\ge\left\lceil\frac{r-1}{\eta+1}\right\rceil
>\eta.                                        \tag{7}
\]

We claim that full central in-degree forces full central out-degree.
Fix top `u` with `k⁻_u=r`, and suppose `a=u*v` is noncentral
for some top `v`. As in the first-gap proof, the `r` central
predecessors `c` of `u` give distinct values `v*c` exhausting
`TopSucc(v)`. E1485 therefore gives

\[
a*b=v\qquad(b\in\operatorname{TopSucc}(v)).
\]

In particular `a*(v*z)=v` for every central `z`. The
auxiliary-relation fiber identity yields `(z*a)*v=a`. Thus
`Z*a=TopPred(a)` lies in the top-input part of the size-`r`
fiber `R_v⁻¹(a)`. That fiber also contains a non-top sharp
predecessor of `a`, so `|TopPred(a)|≤r−1`.

Central shadow counting gives

\[
m=\sum_{t\in\operatorname{TopPred}(a)}k^-_t
\le r|\operatorname{TopPred}(a)|.
\]

Since `0<η<r`, this forces `|TopPred(a)|=r−1`. But then

\[
\sum_{t\in\operatorname{TopPred}(a)}\varepsilon^-_t
=r(r-1)-m=\eta,
\]

which is impossible by (7): a sum of nonnegative integers, each
either zero or greater than `η`, cannot equal the positive number
`η`. Hence every product `u*v`, `v∈T`, is central. The row
of `K` at `u` is all ones, so `k⁺_u=r` as claimed.

Put `δ=r+η`. Since `h=r²`, the central defect moments are

\[
\sum_u\varepsilon^+_u=r\delta,
\qquad\sum_u\varepsilon^+_u\varepsilon^-_u=\delta^2.
\]

The claim says `supp ε⁺⊆supp ε⁻`. Every positive `ε⁻` is at
least two by (7), so

\[
\delta^2\ge2\sum_u\varepsilon^+_u=2r\delta.
\]

This gives `δ≥2r`, contrary to `δ=r+η<2r`. The branch with a
full central degree is excluded. A full out-degree entry instead
of an in-degree entry is handled by the dual argument.

## 3. The branch with no full central degrees

Suppose now that all central in-degrees and out-degrees are at most
`q=r−1`. Each central vertex has `r` top neighbors, whose
appropriate central degrees sum to `m=rq−η`. Thus every such
degree is at least `q−η`; coverage by central neighbors makes
this bound global. Define

\[
d^+=q\mathbf1-k^+,\qquad d^-=q\mathbf1-k^-,
\qquad 0\le d^\pm\le\eta.
\]

Write `h=r²+a`. Expanding the central incidence moments gives

\[
\sum d^+=\sum d^-=qa+r\eta,
\qquad\sum d^+d^-=q^2a+\eta^2.
\]

Since `η<q`, nonnegativity of the second sum and integrality give
`a≥0`. On the other hand, `d⁻≤η` gives

\[
q^2a+\eta^2\le\eta(qa+r\eta),
\qquad a\le\frac{\eta^2}{q-\eta}<1,
\]

where the strict inequality is exactly a consequence of
`r≥η(η+1)+2`. Hence `a=0` and `h=r²`.

For any vertex `x`, central shadow counting and `k⁻≤q` give
`|TopPred(x)|≥ceil(m/q)=r`; dually `|TopSucc(x)|≥r`.
Let `D` be ordinary adjacency on `T`. The central endpoint
identity `BD=J_{m,h}` says that, for each central vertex, the sum
of the top out-degrees of its `r` successors is `h=r²`. Each
of these degrees is at least `r`, so every one is exactly `r`.
Every top vertex occurs in such a row. Thus every top vertex has
exactly `r` top successors; the column-dual argument gives exactly
`r` top predecessors as well.

Finally `Σd⁻=rη<r²=h`, so some top vertex has `d⁻=0` and
therefore `k⁻=r−1`. Its ordinary central defect is `ε=1`.
Applying (2) yields `η+1≥r−1`, or `r≤η+2`. This contradicts
`r≥η²+η+2` because `η≥1`.

Both branches are impossible, proving (1).
