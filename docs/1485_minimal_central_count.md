# The smallest possible central class restricts the next degree

Research note, 18 September 2026. These are pen-and-paper consequences
of finite E1485 structure, not Lean declarations. They do not exclude
the smallest possible central class in general.

Let `r` be the minimum translation degree, and suppose the central
class `Z` has its smallest possible size, `|Z|=r`. Assume a
noncentral vertex exists, and let `q>r` be the least noncentral
translation degree.

**Theorem.** There is a positive divisor `k` of `r` such that

\[
q=r+k.
\]

Every vertex of degree `q` has exactly `k` sharp neighbors in each
direction. If `k<r`, the number of degree-`q` vertices is at most

\[
\left\lfloor\frac{r^2(r-1)}{r-k}\right\rfloor.
\]

In particular, at minimum degree three with three central vertices,
the next degree is either four, occurring at most nine times, or six,
with all three sharp neighbors in each direction. Degree five cannot
be the least noncentral degree. Neither alternative is excluded here.

## Central coordinates form an `r` by `r` grid

Let `T` be the top-degree class, with central in/out counts `k⁻,k⁺`.
The [central incidence identities](1485_unrestricted_central_incidence.md)
give

\[
\sum_T k^- =\sum_T k^+=r^2,
\qquad \sum_T k^-k^+=r^2.
\]

Every count is positive. Equality in
`Σk⁻k⁺≥Σk⁻` forces every `k⁺=1`; the other first moment then
gives `|T|=r²` and every `k⁻=1`. Label the central vertices
`z_i`. Every ordered central pair has a unique good top middle, so

\[
T=\{t_{ij}=z_i*z_j\},\qquad z_i\to t_{ij}\to z_j.
\]

For any vertex `x`, its top predecessor set meets every central row
of this grid exactly once; its top successor set meets every central
column exactly once. Hence both sets have size `r`. A product of
two top vertices is central precisely when their adjacent grid labels
agree:

\[
t_{ij}*t_{\ell m}\in Z\quad\Longleftrightarrow\quad j=\ell.
\]

## Least-degree vertices give a regular equality matrix

Fix `a` of degree `q`. Every non-top neighbor of `a` is sharp:
its complementary degree is an occurring degree greater than `r`
and at most `q`, so minimality makes it `q`. The `r` top
neighbors in each direction leave exactly `k=q−r` sharp neighbors.
Thus `1≤k≤r`.

Write the two top profiles of `a` as

\[
\operatorname{TopPred}(a)=\{t_{i,p(i)}:i<r\},\qquad
\operatorname{TopSucc}(a)=\{t_{w(j),j}:j<r\}.
\]

The central-middle matrix on this endpoint rectangle is

\[
H_{ij}=\mathbf1_{p(i)=w(j)}.
\]

It has every row and column sum `k`. Indeed a top translation
fiber with value `a` has size `r` and contains all `k` sharp
neighbors on the other side; its remaining `r−k` inputs are top.
The other `k` top paths are bad. Strict degree descent says their
good replacement is central, since `q` is the least noncentral
degree. Conversely a central middle makes the path through `a` bad.

Every value occurring in `p` therefore occurs exactly `k` times
in `w`; dually every value occurring in `w` occurs exactly `k`
times in `p`. The two supports coincide, and each of their values
has multiplicity `k`. Since each list has length `r`, this proves
`k` divides `r`.

## Counting the degree class

Each degree-`q` vertex is the good middle of exactly `r(r−k)`
ordered top endpoint pairs. These pairs are disjoint for different
vertices. There are `r⁴` ordered top pairs in total, of which
exactly `r³` have a central middle: each of the `r` central
vertices has `r` top predecessors and `r` top successors.
Thus, when `k<r`,

\[
|\{a:d(a)=q\}|\,r(r-k)\le r^4-r^3.
\]

Dividing proves the stated class-size bound. When `k=r`, there
are no top-top products of degree `q`; the bound is deliberately
not asserted in that case.
