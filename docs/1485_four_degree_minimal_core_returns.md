# Top returns bound four-degree models with the smallest central class

Research note, 19 September 2026. These are analytic necessary
conditions, not Lean declarations. They do not exclude the entire
four-degree family considered here.

Assume the central class has size `r`, and the four occurring
translation degrees are

\[
r<q<2r<s=2q,\qquad n=2rq.
\]

The [minimal-central-count theorem](1485_minimal_central_count.md)
and its [first-output improvement](1485_first_top_output_fibers.md)
write `q=r+k`, where `k` is a positive proper divisor of `r`.
There are `r²` tops, and every vertex has `r` top predecessors
and successors.

Write `A,B` for degrees `q,2r`, with sizes `f,g`, and put

\[
N=f+g=n-r-r^2=r^2+2rk-r.
\]

Every member of `A` has sharp degree `k` in both directions.
For `b∈B`, denote its sharp degree by `j_b`. This degree is
also balanced: besides its `r` top neighbors, it has `j_b`
sharp neighbors in `A` and `r−j_b` ordinary neighbors in `B`.
Reciprocal neighbor balance equates the two sharp counts, since
their weighted sums have the form
`2r²+rk+(r−k)j_b`. Consequently

\[
1\le j_b\le r,\qquad
\sum_{b\in B}j_b=kf.
\]

**Main bounds.** If `k>1`, every `j_b≤r−1`, and hence

\[
\boxed{f\le
\left\lfloor\frac{(r-1)(r^2+2rk-r)}{r+k-1}\right\rfloor.}
                                                               \tag{1}
\]

The maximum-sharp-count refinement in §3 can be substantially
stronger. For example it gives `f≤36` when `(r,k)=(6,3)`,
and `f≤66` when `(r,k)=(8,4)`.

## 1. Good-return fibers and the internal path budget

If `b,d∈B` have top product `e=b*d`, consider

\[
X=L_e^{-1}(d),\qquad Y=R_e^{-1}(b).
\]

Both sets have size `r`. E1485 and its dual show that
`x↦x*b` bijects `X` with `Y`, with inverse `y↦d*y`.
Each matched pair is an ordinary edge. The set `X` contains
all `j_d` sharp successors of `d` in `A`, while `Y` contains
all `j_b` sharp predecessors of `b` in `A`. There are no
ordinary `A→A` edges because `q²<2rq=n`. Hence

\[
\boxed{b*d\in T\quad\Longrightarrow\quad j_b+j_d\le r.}
                                                               \tag{2}
\]

For clarity, the bijection uses only the two identities

\[
(x*b)*(b*(e*x))=b,
\qquad ((b*d)*x)*(x*b)=x.
\]

Substitution of `e*x=d` and `b*d=e` gives the claimed fiber
memberships and inverse. No full-core assumption is involved.

For a fixed `b∈B`, ordinary two-step paths to `B` endpoints
through the two middle classes have total number

\[
H_b=k j_b+
\sum_{x\in Row(b)\cap B}(r-j_x).
                                                               \tag{3}
\]

The first term counts the paths through its sharp `A` successors.
Every endpoint not reached by such a path must have top product
with `b`: a central middle is impossible. Thus at least `g−H_b`
members of `B` are top-return partners. This lower bound remains
valid when negative. Combining it with (2) gives the useful
distributional inequality

\[
\boxed{
\#\{d\in B:j_d\le r-j_b\}\ge g-H_b.}
                                                               \tag{4}
\]

No goodness assertion about all paths counted in (3) is needed.
Counting paths only upper-bounds the number of reachable endpoints.

## 2. The maximal sharp count is absent when `k>1`

The elementary bound `kf=Σj_b≤rg` gives

\[
g\ge\frac{kN}{r+k}
=rk+\frac{rk(k-1)}{r+k}.
\]

If `k>1`, this is strictly larger than `rk`. A hypothetical
vertex with `j_b=r` has no internal `B` successor, so (3)
gives only `H_b=rk` paths. It therefore has a top-return partner,
contrary to (2) and the positivity of every sharp count.
This proves `j_b≤r−1`. Summing yields (1).

More generally, the same argument proves

\[
\boxed{g>rk\quad\Longrightarrow\quad j_b\le r-1
\text{ for every }b\in B,}
\]

even when `k=1`.

## 3. Refine the bound using the maximum sharp count

Suppose `j_b≤r−1` is known, and let `d=max_b j_b`. The
sharp-edge sum first gives `g≥kN/(k+d)`.

For a vertex attaining `d`, the crude path bound from (3) is

\[
H_b\le H_d:=kd+(r-1)(r-d).
\]

At least `g−H_d` vertices therefore have sharp count at most
`r−d`. If `2d>r`, each such vertex contributes a deficit of
at least `2d−r` from the maximum `d`. Thus

\[
dg-kf\ge(2d-r)(g-H_d).
\]

After substituting `f=N−g`, this proves

\[
\boxed{
g\ge\max\left\{
\left\lceil\frac{kN}{k+d}\right\rceil,
\left\lceil\frac{kN-(2d-r)H_d}{r+k-d}\right\rceil
\right\}\qquad(2d>r).}
                                                               \tag{5}
\]

For `2d≤r`, retain just the first term. Minimizing these
explicit integer lower bounds over `1≤d≤r−1` yields a bound
without knowing the maximum in advance. For example:

| `r` | `k` | `N=f+g` | Lower bound on `g` | Upper bound on `f` |
| ---: | ---: | ---: | ---: | ---: |
| 4 | 2 | 28 | 13 | 15 |
| 6 | 2 | 54 | 16 | 38 |
| 6 | 3 | 66 | 30 | 36 |
| 8 | 4 | 120 | 54 | 66 |

This table evaluates the proved formula; it is not a classification
or an existence claim for any listed class size.

## 4. A short route through the order-forty-eight class bounds

Take `r=4,k=2`, so `N=28`. Section 2 gives `j_b≤3` and
`f≤16`. If `f=16`, then `g=12` and `Σj_b=32`, forcing
some `j_b=3`. Such a vertex has at most `3·2+3=9` paths
through `A∪B`, so it has at least three top-return partners.
All have sharp count one. But the total deficit from sharp count
three is only `3g−Σj_b=4`; three sharp-count-one vertices
would already contribute six. This excludes `f=16` and gives
`f≤15` without the longer specialized packing argument.

The internal-graph argument in
[the order-48 note, §7](1485_order_forty_eight_min_four.md#7-fifteen-degree-six-vertices-are-impossible-as-well)
then excludes fifteen and gives `f≤14`.
The packing arguments in that note remain independently useful:
they also give matching properties of high top outputs and an
exact expression for the number of bad internal two-edge paths.

## 5. The next-to-largest class is impossible when `k=1`

Let `r≥3`, `k=1`, and suppose `f=r²−1`. Then `N=r²+r`
gives `g=r+1>rk`. Section 2 excludes `j_b=r`. But

\[
\sum_bj_b=f=r^2-1=(r-1)g,
\]

so every `j_b=r−1`. Each vertex has one internal `B`
successor, also of sharp count `r−1`. Its path budget (3)
is therefore `(r−1)+1=r<g`, forcing a top-return partner.
Equation (2) would give `2r−2≤r`, impossible for `r≥3`.
Thus

\[
\boxed{k=1,\ r\ge3\quad\Longrightarrow\quad f\ne r^2-1.}
\]

This excludes the next-to-saturated class, not the saturated
`f=r²` case or all smaller classes.
