# Completing the two-degree argument through minimum degree eleven

Research note, 18 September 2026. The
[mixed-five-cycle argument](1485_two_degree_lower_bound.md) proves standard
parameters for minimum translation degree `r≤9`. Here we extend that to
`r≤11`. These are pen-and-paper proofs; the finite arithmetic below does
not rely on an unrecorded SAT or SMT refutation.

Use the same notation: translation degrees `r<s`, central and high
cardinalities `m,h`, and sharp degrees `k_a` for `a∈H`. Standard means
`s=2r`, `m=h=r²`, and all `k_a=r`. A nonstandard model satisfies

\[
 s\ge2r,\quad 2\le k_a\le r-2,\quad
 m+h=rs,\quad \sum k_a=mr,\quad \sum k_a^2=m^2.
 \tag{1}
\]

## Weighted counts for the high-product relation

Let `E=J-CB` be the zero-one relation on high vertices whose endpoint
product is high. The known identities `BC=J`, `C1=k`, and `1ᵀB=kᵀ`
give

\[
 E1=h1-rk,\qquad Ek=m(r1-k). \tag{2}
\]

For the second identity, `Bk=BC1=m1`, whence `CBk=mk`, while
`Jk=mr1`. Every `E`-neighbor of `a` has sharp degree at most `r-k_a`,
by the good-path endpoint bound. In a nonstandard model its degree is
also at least two. Thus

\[
 2(h-rk_a)\le m(r-k_a)
 \le(r-k_a)(h-rk_a). \tag{3}
\]

In particular, if `k_a=r−2`, all its `E`-neighbors have sharp degree
exactly two, so (2) implies

\[
 \boxed{2m=r(s-r+2).} \tag{4}
\]

Write `K=max k_a`. Applying `(k_a-2)(k_a-K)≤0` to the moments gives

\[
 m^2-[r(K+2)+2K]m+2Krs\le0.
\]

Hence

\[
 [r(K+2)+2K]^2\ge8Krs. \tag{5}
\]

We will also use this refinement of the tail bound. If sharp degree `j`
occurs and `2≤L=r−j<K`, then

\[
 \boxed{m^2-(L+2)mr+2Lh
 \le (K-2)(K-L)j^2.} \tag{6}
\]

Indeed, for every `2≤k≤K`,

\[
 (k-2)(k-L)\le (K-2)(K-L)\mathbf1_{k>L}.
\]

Sum this inequality and use the moments and the previously proved tail
bound `#{a:k_a>L}≤j²`.

## Minimum degree ten

Suppose `r=10` and the parameters are nonstandard. The improved bound
in the lower-bound note leaves `s=20` or `21`. Also `2≤K≤8`.
For `K∈[2,7]`, even the weaker discriminant condition obtained from
`s≥20` fails:

\[
 (20+12K)^2-1600K<0.
\]

This convex quadratic has values `−1264` and `−384` at the endpoints
`2,7`, so is negative throughout that interval. Thus `K=8`.
Equation (4) gives `m=5(s−8)`.

If `s=21`, then `m=65`. But the moments modulo two give
`m²≡mr (mod 2)`, requiring `m` even when `r=10`. This is impossible.

If `s=20`, then `m=60`, `h=140`. For an occurring sharp degree
`j∈{3,4,5,6}`, the difference between the left and right sides of
(6), with `L=10−j`, is

\[
 320j-800-6(j-2)j^2.
\]

Its values are respectively `106,288,350,256`, all positive.
None of those degrees can occur. Only `2,7,8` remain. If their
multiplicities are `c₂,c₇,c₈`, the zeroth, first, and second moments
give

\[
 5c_7+6c_8=320,\qquad 45c_7+60c_8=3040.
\]

Subtracting nine times the first equation gives `6c₈=160`, impossible
for integer `c₈`. This excludes every nonstandard case at `r=10`.

## Minimum degree eleven

Now let `r=11`. The bounds leave `s∈{22,23,24}` and `2≤K≤9`.
For `K∈[2,7]`, the discriminant from `s≥22` is

\[
 (22+13K)^2-1936K<0.
\]

Again it is a convex quadratic with negative endpoint values `−1568`
and `−783`. Thus `K=8` or `9`.

### Case `K=9`

Equation (4) gives `2m=11(s−9)`. Integrality excludes `s=22,24`,
leaving `s=23`, `m=77`, and `h=176`. For any occurring degree
`j∈{3,4,5,6,7,8}`, the excess of the left side of (6) over its
right side is

\[
 495j-1210-7(j-2)j^2.
\]

The six values are `212,546,740,752,540,62`, all positive.
Only sharp degrees two and nine remain, but the first moment gives
`7c₉=11m−2h=495`, impossible for integer `c₉`.

### Case `K=8`

Condition (5) becomes `126²≥704s`, so only `s=22` remains. For a
vertex of degree eight, the lower inequality in (3) gives
`2(154−m)≤3m`, hence `m≥62`.

For an occurring degree `j∈{4,5,6,7}`, put `L=11−j`. The excess
in (6) is

\[
 Q_j(m)=m^2-(13L+22)m+484L-6(j-3)j^2.
\]

For `m≥62` these four quadratics are strictly increasing: their
derivatives are `2m-(13L+22)≥124−113>0`. At `m=62` their values
are `130,248,222,16`, all positive. Thus only degrees `2,3,8` remain.
Eliminating the multiplicities of two and three from the moments gives

\[
 30c_8=m^2-61m+1452. \tag{7}
\]

The right side modulo five is `m²−m+2`. Its values at residues
`0,1,2,3,4` are `2,2,4,3,4`, never zero. This contradicts (7).

We have excluded all nonstandard cases at `r=11` as well. Therefore

\[
 \boxed{r\le11\quad\Longrightarrow\quad
 s=2r,\quad m=h=r^2,\quad k_a=r\text{ for all }a\in H.}
\]

## Scope and spectrum consequence

In particular every order `pq` with distinct primes `p<q` and
`p∈{2,3,5,7,11}` is excluded. A model of that order would have precisely
the degrees `p,q`, but the theorem would give `q=2p`.

This does not classify models with three or more translation degrees.
For the two-degree problem, any remaining nonstandard case must have
`r≥12` and nonconstant sharp degrees. The full spectrum converse remains
open in this work.
