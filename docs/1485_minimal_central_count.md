# The smallest possible central class restricts the next degree

Research note, 18 September 2026. These are pen-and-paper consequences
of finite E1485 structure, not Lean declarations. They do not exclude
the smallest possible central class in general.

**Update, 19 September:** for `r>1`, the new
[first-top-output fiber theorem](1485_first_top_output_fibers.md#4-the-smallest-central-class-forces-a-proper-divisor)
proves that `k` below is a **proper** divisor. Thus the `q=2r`
branch discussed at the end of this historical note is now excluded
for every `r>1`. The case `r=1` is full core and is different.
At `r=3`, the [complete full-core theorem](1485_min_three_full_core.md)
now excludes this smallest-central-class configuration altogether.

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
be the least noncentral degree. Subsequent
[top-output arguments](1485_three_central_minimum_top_output.md)
exclude the degree-six alternative, and the
[saturated-profile proof](1485_three_central_saturated_four.md)
improves the degree-four class bound to eight.

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

## A further gap when the next degree is twice the minimum

Suppose `r>2` and `q=2r`. Let `p` be the least degree of a
noncentral top-top product. Such a product exists because `|Z|=r<r²`.
Degree-`2r` vertices are sharp-regular and cannot be top-top products,
so `p>2r`. The general product-degree bound gives `p≤r²`.

At a first top output `a`, the bad-path matrix on its top profiles
is again an equality matrix `H_ij=1_{u(i)=v(j)}`. Any bad path
has a smaller-degree top-product replacement, which must be central.
Each row and column of `H` is positive, because top translation
fibers also contain a sharp non-top input. The two lists `u,v`
therefore have the same support. It has at least two elements:
one support element would give `H=J`, so no top pair would produce `a`.

Let `α_z,β_z` be the positive multiplicities on that support,
of size `ℓ≥2`. Both sum to `r`. Writing
`α_z=1+A_z`, `β_z=1+B_z` gives

\[
\sum_z\alpha_z\beta_z
=2r-\ell+\sum_z A_zB_z
\le2r-\ell+(r-\ell)^2
\le(r-1)^2+1.
\]

The last expression is the largest value over `2≤ℓ≤r`.
Consequently the number `g` of good top pairs producing `a` satisfies

\[
g=r^2-\sum_z\alpha_z\beta_z\ge2(r-1)>r.
\]

The [equality-case matching theorem](1485_top_output_saturation.md)
therefore excludes `p=r²`. In particular `p≤r²−1`.

Write `p=2r+t`, with `t≥1`, and let `k≥1` be the sharp
out-degree of `a`. If `t≤r`, the
[top-fiber slot bound](1485_three_central_minimum_top_output.md#a-general-top-fiber-slot-bound)
specializes to

\[
g\le r(r-k)-(r+t-k)(r-t)=t(t-k)\le t(t-1).
\]

If `t>r`, the inequality `t(t−1)≥2(r−1)` is automatic.
In either case the necessary gap is

\[
\boxed{p=2r+t\le r^2-1,\qquad t(t-1)\ge2(r-1).}
\]

For `r=3`, it would require `t≥3` and `p≤8`, an immediate
contradiction. For larger `r` this remains a restriction, not a
general exclusion of `q=2r` or of the smallest central class.

## A first restriction at minimum degree four

Update, 19 September. The preceding `q=2r` discussion is superseded
by the proper-divisor theorem linked at the top of this note.
At `r=4, |Z|=4`, the next degree is therefore five or six.
The following additional restriction concerns the degree-five branch;
it does not exclude that branch.

Write `A` for the degree-five class and `B` for degree `n/5`.
Then each member of `A` has sharp degree one and four top neighbors
in either direction. The equality-matrix argument above shows that
both top profiles are permutation transversals of the central `4×4`
grid. Its twelve good top pairs give `|A|≤16` by the class bound.
The sharp maps `F,G:A→B` are onto and jointly injective, so
`|A|≤|B|²`.

Two permutation transversals of this grid meet once precisely when
their relative permutation is a three-cycle. Let `V₄` denote the
normal Klein-four subgroup of `S₄`. The three-cycles are exactly
the even permutations outside `V₄`. Thus the unique-intersection
graph on the 24 transversals is two disjoint copies of `K_{4,4,4}`:
the two components are permutation parity, and the three parts of
each component are the four-element `V₄` cosets.

For members `a,c∈A`, if `F(a)≠G(c)`, the endpoint pair has no
non-top middle and hence exactly one top middle. Consequently

\[
|TopSucc(a)\cap TopPred(c)|\ne1
\quad\Longrightarrow\quad F(a)=G(c).
\]

If `|B|≥3`, all predecessor profiles have the same parity.
Otherwise choose one of each parity; any successor profile differs
in parity from one of them, forcing its `F`-value to be one of
two fixed `G`-values. This contradicts surjectivity. Dually all
successor profiles have constant parity, and the two constant
parities must agree: if not, every endpoint pair would have a
sharp middle and both maps would be constant.

If further `|B|≥4`, the predecessor profiles cannot use all three
`V₄` cosets of that parity. Choosing one representative of each
would similarly force every `F`-value to be one of three fixed
`G`-values, by matching its successor profile's coset. Dually the
successor profiles use at most two cosets.

In particular `|A|≥5` forces the common-parity restriction, and
`|A|≥10` forces the two-coset restriction on each side. The
order-three proof used the simpler unique-intersection graph on
`S₃`; these are its precise order-four counterparts, not an
assertion that the remaining incidence configurations are impossible.
