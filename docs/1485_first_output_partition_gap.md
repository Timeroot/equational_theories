# A sharper first-output gap from common central blocks

Research note, 19 September 2026. This is an unconditional finite
E1485 inequality, not yet formalized in Lean. It sharpens the
[square-root divisor gap](1485_first_top_output_divisor_gap.md)
using the regular central-middle matrix of a first noncentral top
output.

Let the central core be non-full, write `n=rs` for the product of
minimum and maximum translation degrees, and let `p` be the least
degree of a noncentral product of two top vertices. Assume `p≥2r`.
Put

\[
a=\left\lceil\frac{p-r}{r-1}\right\rceil,
\qquad b=r-a,
\qquad c=\left\lceil\frac{p-r}{b}\right\rceil.
\]

**Theorem.** Necessarily `2a<r`, and

\[
\boxed{a(p+1)+c(r-2a)\le r^2.}                    \tag{1}
\]

In particular, the previous bound `a(p+1)≤r²` is strict in
this range. For example, the maximum first-output degree at minimum
five improves from eleven to ten; at minimum six, from sixteen to
fourteen.

## Two partitions with common blocks

For a top vertex `v`, write `C_v` for its central successor set.
The existing divisor-gap proof gives

\[
a\le |C_v|,|P_v|\le b=r-a                         \tag{2}
\]

for every top vertex, where `P_v` is its central predecessor set.
These bounds imply `a≤b`.

Choose a degree-`p` top output `x`. Its top successor set `V`
has size `t≥p−r+1>r`. The central-endpoint uniqueness theorem
says that the sets `C_v`, for `v∈V`, partition the central set `Z`.
For any central `z`, its ordinary row `Row(z)` consists of `r`
top vertices, and their sets `C_w` also partition `Z`.

Let `j_z=|V∩Row(z)|`. The two partitions have these `j_z`
identical, pairwise disjoint blocks. Remove them from both sides.
The remaining `t−j_z` blocks in the first partition have size
at least `a`; the remaining `r−j_z` blocks in the second have
size at most `b`. Since their unions are the same,

\[
a(t-j_z)\le b(r-j_z),
\qquad at\le br-j_z(b-a).                         \tag{3}
\]

If `a=b`, this forces `t≤r`, a contradiction. Thus `a<b`,
or `2a<r`.

## Regularity supplies a large common intersection

The [first-output theorem](1485_first_top_output_fibers.md)
says that the central-middle matrix on
`TopPred(x)×TopSucc(x)` has every row sum `p−r`.
For any top predecessor `u` of `x`, this row sum is

\[
p-r=\sum_{z\in C_u}|V\cap Row(z)|
    =\sum_{z\in C_u}j_z.                          \tag{4}
\]

The summands count disjoint sets: two distinct central middles
for the same ordered endpoint pair are impossible. There are at
most `b` summands, by (2). Therefore at least one central `z`
satisfies

\[
j_z\ge\left\lceil\frac{p-r}{b}\right\rceil=c.
\]

Use this `z` in (3), and use `t≥p−r+1`:

\[
a(p-r+1)\le br-c(b-a).
\]

Substituting `b=r−a` and cancelling the terms `ar` proves (1).
No assumption of uniform central incidence, sharp regularity, or
parameter independence was used.

## A larger forbidden multiplicative gap

Suppose the least noncentral degree is at least `ℓr`, where
`ℓ≥2` is an integer. Then `p≥ℓr`, `a≥ℓ`, and also `c≥a`,
because `b=r−a≤r−1`. Formula (1), with `r−2a>0`, implies

\[
r^2\ge a\bigl(p+1+r-2a\bigr)
\ge \ell\bigl((\ell+1)r+1-2\ell\bigr).             \tag{5}
\]

For the last step, the function
`x↦x((ℓ+1)r+1−2x)` is increasing on `ℓ≤x<r/2`.
The earlier gap theorem already gives `r>ℓ²`. On the interval
`ℓ²<r≤ℓ(ℓ+1)−2`, the quadratic obtained from (5),

\[
r^2-\ell(\ell+1)r+2\ell^2-\ell,
\]

is increasing and is at most its value `4−3ℓ<0` at the right
endpoint. This contradicts (5). Consequently

\[
\boxed{r\ge\ell^2+\ell-1.}                        \tag{6}
\]

This strengthens `r>ℓ²`. It does not settle the next odd
prime-power frontier: minimum `r=ℓ³` at order `ℓ⁹` still
satisfies these inequalities.
