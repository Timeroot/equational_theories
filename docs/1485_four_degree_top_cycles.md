# Exact mixed-cycle counts with top returns

Research note, 18 September 2026. This is a continuation of the
[full-core four-degree Top-return identities](1485_four_degree_top_return_bounds.md).
All hypotheses and notation of that note remain in force:

\[
d\in\{r,2r,b,2b\},\quad n=2rb,\quad |Z|=r^2,
\quad |A|=m,\quad |H|=h.
\]

These are pen-and-paper necessary conditions, not a proof of sharp
regularity in the remaining all-irregular case. In particular, mixed
high three-edge paths can have a top good return; overlooking those
paths would give an incorrect stronger conclusion.

Put

\[
t=b-3r,\qquad d_0=b-2r=r+t,\qquad
L_1=\sum_a\ell_a,\qquad L_2=\sum_a\ell_a^2,
\qquad V=\sum_a k_a\ell_a=rL_1-L_2.
\]

The high adjacency `D` has row and column sums `d₀+ℓ`, while
the canonical internal relation `R` has both sums `ℓ`.

## Total bad-good and bad-bad high paths

Let `N` count high paths `a→b→c→d` whose first two-edge path is
bad and second is good. For a fixed shared edge `b→c`, there are
`t+rR_bc` bad high predecessors and `2r-k_c-rR_bc` good high
extensions. Hence

\[
\begin{aligned}
N&=\sum_{D_{bc}=1}(t+rR_{bc})(2r-k_c-rR_{bc})\\
 &=t\sum_c(d_0+\ell_c)(r+\ell_c)
      +r\sum_c\ell_c(\ell_c-t)\\
 &=\boxed{d_0\bigl(trh+tL_1+L_2\bigr).}
\end{aligned} \tag{1}
\]

Let `B` count the high three-edge paths with both two-edge paths
bad. The bad predecessor and extension counts agree on each shared
edge, so

\[
\begin{aligned}
B&=\sum_{D_{bc}=1}(t+rR_{bc})^2\\
 &=t^2(d_0h+L_1)+(2tr+r^2)L_1\\
 &=\boxed{d_0\bigl(t^2h+d_0L_1\bigr).}
\end{aligned} \tag{2}
\]

Write `N_T` and `B_T` for the subcounts having top good return
`d*a∈T`. A mixed path cannot have its good return in `A`, because
the three sharp closure paths in the resulting five-cycle force the
other two statuses to agree. A bad-bad path with good return in `A`
would contribute to `tr(DFK)`, which is zero by the preceding note.
Therefore `N-N_T` and `B-B_T` count exactly the respective paths
whose good return lies in `H`.

The [high-only five-cycle lemma](1485_four_degree_regular_gap.md)
allows only zero, two consecutive, or five bad positions. The mixed
cycles contribute equally, over rotation, to a bad-good adjacent
pair and to a bad-bad adjacent pair with opposite good return.
Consequently `N-N_T=B-B_T`. Subtracting (1) from (2) proves

\[
\boxed{B_T-N_T=d_0\bigl(t(t-r)h+V\bigr).} \tag{3}
\]

It is the **difference** `B_T-N_T`, not `B_T` alone, that is
given by (3). Its sign has not been determined here.

## The two boundary edges locate the top-return statuses

Fix a high path `a→b→c→d` whose good return `e=d*a` is top.
If its first two-edge path is bad, its good replacement is some
`α=a*c∈A`. The path `a→α→c→d` is good-good, because its
two paths each contain a sharp edge. The good-return matching puts
`c∈C^-(d)`, so `c R d`. Dually, if the second two-edge path is
bad, then `a R b`.

If both paths are good, the matching itself gives both boundary
conditions `a R b` and `c R d`. If only the first path is bad,
the first boundary cannot belong to `R`: otherwise `e*b=a`
makes the path `e→a→b` good, and the five-cycle law together
with the good path `b→c→d` would make `a→b→c` good as well.
The other mixed case is dual. Thus the classification is exact:

| First two statuses | First boundary `a→b` | Last boundary `c→d` |
| --- | --- | --- |
| Good, good | in `R` | in `R` |
| Bad, bad | in `R` | in `R` |
| Bad, good | outside `R` | in `R` |
| Good, bad | in `R` | outside `R` |

For each top-return endpoint pair, the matching counts exactly
`r-k_a-k_d` good-good high paths. Their total is

\[
\sum_{G_{da}=1}(r-k_a-k_d)
=r|G|-2rV, \tag{4}
\]

using the exact weighted identities `k^TG1=k^TG^T1=rV`.
The boundary classification therefore gives

\[
\boxed{
\begin{aligned}
N_T&=\operatorname{tr}\bigl((D-R)DRG\bigr),\\
B_T&=\operatorname{tr}(RDRG)-r|G|+2rV.
\end{aligned}} \tag{5}
\]

All matrices in these traces have the same high-vertex index set;
`G_{da}=1` selects the reverse good return for a path from `a`
to `d`.

## A second exact formula for mixed top returns

The trace `tr(DEG)` counts good-good and bad-good high paths with
top good return. Thus

\[
N_T=\operatorname{tr}(DEG)-r|G|+2rV.
\]

Use `E=J-K-G`, `tr(DKG)=rV`, and

\[
\operatorname{tr}(DJG)
=(d_0\mathbf1+\ell)^TG^T\mathbf1
=(d_0+r)|G|-rV.
\]

This yields the further exact identity

\[
\boxed{N_T=d_0|G|-\operatorname{tr}(DG^2)\ge0.} \tag{6}
\]

Combining (3) and (6) also determines `B_T` in terms of
`tr(DG²)`, although it does not yet determine its sign relative to
`N_T`.

One elementary upper bound retains an important extra term. Since
`(RDR)_{ad}≤ℓ_aℓ_d`, equations (4)--(5) give

\[
\begin{aligned}
B_T
&\le\sum_{G_{da}=1}
  \bigl(\ell_a\ell_d-r+k_a+k_d\bigr)\\
&=r(r-1)(|G|-2V)+k^TGk\\
&=\boxed{r(r-1)(|G|-2V)+r k^TRk.}
\end{aligned} \tag{7}
\]

The first term on the last line cannot simply be omitted: it is
nonnegative, and the entrywise expression is
`(r-1)(r-k_a-k_d)+k_ak_d`, not just `k_ak_d`.
