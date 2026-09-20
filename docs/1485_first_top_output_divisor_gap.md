# A square-root divisor gap for non-full central cores

Research note, 19 September 2026. These are unconditional finite
E1485 deductions, not Lean declarations. They combine the
[first-output fiber theorem](1485_first_top_output_fibers.md) with
[central-block packing](1485_refined_top_product_packing.md).

Write `n=rs`, where `r` and `s` are the minimum and maximum
translation degrees. Let `Z,T` be the central and top classes,
and put `m=|Z|`. Assume that the central core is not full,
so `m<r²`, and let `p` be the least degree of a noncentral
product of two top vertices. Such a product exists. The already
proved minimum-degree-one result allows us to assume `r≥2`.

**Theorem.** Put

\[
a=\left\lceil\frac{p-r}{r-1}\right\rceil.
\]

Then

\[
\boxed{a(p+1)\le r^2.}                                      \tag{1}
\]

In particular, if the least noncentral translation degree is at
least `ℓr`, for an integer `ℓ≥2`, then

\[
\boxed{r>\ell^2.}                                           \tag{2}
\]

Consequently every odd prime seventh power is absent from the finite
spectrum. This extends the previously established fifth-power
exclusion; it does not exclude every odd prime power.

## 1. A large first output excludes full central incidence counts

Write

\[
P_t=Col(t)\cap Z,\quad C_t=Row(t)\cap Z,\qquad
k^-_t=|P_t|,\quad k^+_t=|C_t|.
\]

Suppose first that `p≥2r`. We claim that every `k⁻` and `k⁺`
is strictly smaller than `r`.

Here is the incidence argument, without a regularity assumption.
Let `B:Z→T`, `C:T→Z` be the ordinary adjacency matrices,
`K=CB`, and `F=J−K`. We have `BC=J`, `K≤J`, and

\[
BF=\mathbf1(r\mathbf1-k^-)^T.
\]

If `k⁻_j=r`, column `j` of `BF` is zero. Each top vertex
has a central predecessor, so nonnegativity forces column `j`
of `F` to be zero. Column `j` of `K` is therefore all ones.

For any vertex `x`, let `v` indicate its top successor set.
Central-endpoint uniqueness gives `vᵀC=1ᵀ`, hence
`vᵀK=(k⁻)ᵀ`. Reading column `j` proves

\[
|TopSucc(x)|=r.
\]

The first-output fiber theorem says that a degree-`p` top output
has equally many top neighbors on both sides, say `t`, and
`1≤p−t≤r−1`. Here `t=r`, so `p≤2r−1`, a contradiction.
The dual argument excludes `k⁺_j=r` as well. Thus, when `p≥2r`,

\[
1\le k^\pm_t<r\qquad(t\in T).                              \tag{3}
\]

## 2. The same gap bounds every central block from both sides

The row-local first-output bound supplies, in each top row with
`k⁺_u<r`, a noncentral top output of degree at most
`r+(r−1)k⁺_u`. Since `p` is the globally least such degree,

\[
p\le r+(r-1)k^+_u,
\qquad\text{so}\qquad k^+_u\ge a.
\]

The dual statement gives `k⁻_u≥a`.

Conversely fix any top vertex `t` and choose a top successor `u`;
every vertex has one. By (3), `k⁺_u<r`. The refined packing
theorem for the ordinary top edge `t→u` supplies a noncentral
top output of degree at most `r²−(r−1)k⁻_t`. Therefore

\[
k^-_t\le
\left\lfloor\frac{r^2-p}{r-1}\right\rfloor
=r-a.
\]

Duality gives the same upper bound on `k⁺`. We have proved

\[
\boxed{a\le k^\pm_t\le r-a\qquad(t\in T)}                  \tag{4}
\]

whenever `p≥2r`.

## 3. Compare a first-output partition with the incidence moments

The central moments are

\[
\sum_{t\in T}k^-_t=rm,\qquad
\sum_{t\in T}k^-_t k^+_t=m^2.
\]

Using the upper bound in (4), and dividing by `m>0`, gives

\[
m\le r(r-a).                                               \tag{5}
\]

Fix a degree-`p` top output. It has `t≥p−r+1` top predecessors,
whose central predecessor sets partition `Z`. Each block has
size at least `a` by (4), so

\[
m\ge at\ge a(p-r+1).                                       \tag{6}
\]

Combining (5) and (6), and cancelling the terms `ar`, proves
`a(p+1)≤r²`.

If instead `r<p≤2r−1`, then `a=1` and
`a(p+1)≤2r≤r²`, since `r≥2`. This proves (1) in all cases.

An explicit, slightly weaker form follows by replacing the ceiling
by its argument:

\[
p\le
\frac{r-1+\sqrt{4r^3-3r^2+2r+1}}2.
\]

The ceiling version (1) is preferable for individual orders.
For example it gives `p≤7` at minimum degree four, and `p≤11`
at minimum degree five.

## 4. Multiplicative gaps between occurring degrees

Let `q` be the least noncentral translation degree and assume
`q≥ℓr`, where `ℓ≥2` is an integer. Since `p≥q`,

\[
a=\left\lceil\frac{p-r}{r-1}\right\rceil
\ge\left\lceil\frac{(\ell-1)r}{r-1}\right\rceil
\ge\ell.
\]

Consequently (1) implies

\[
r^2\ge\ell(p+1)\ge\ell(\ell r+1)
=\ell^2r+\ell.
\]

In particular `r>ℓ²`, proving (2). Thus a non-full core requires
an occurring degree strictly between `r` and `ℓr` whenever
`r≤ℓ²`. This is a necessary condition, not an assertion that
all integer degrees in that interval occur.

## 5. Odd prime seventh powers are excluded

Let `ℓ` be an odd prime. At order `ℓ^e`, all occurring translation
degrees are powers of `ℓ`. A non-full core therefore has
`q≥ℓr`, so (2) excludes minimum degrees `r=ℓ` and `r=ℓ²`.
Minimum one is already impossible for a non-full core. Equivalently,
any non-full-core magma of prime-power order has minimum degree
at least `ℓ³`.

Now suppose `n=ℓ^7`. The minimum degree is `r=ℓ^i`, with
`0≤i≤3`, because `r≤s=n/r`. A full central core would give
`n=r²·2^j`, impossible for this odd nonsquare order. The preceding
gap excludes `i=0,1,2`. For `i=3`, all degrees lie between
`r=ℓ³` and `s=ℓ⁴`, so exactly those two degrees occur.
The unconditional [two-degree theorem](1485_two_degree_lower_bound.md)
would give `s=2r`, contradicting `s=ℓr` with `ℓ` odd. Hence

\[
\boxed{\ell\text{ odd prime}\quad\Longrightarrow\quad
\ell^7\text{ is not in the finite E1485 spectrum}.}
\]

More generally, for odd exponent `e=2k+1`, any remaining prime-power
counterexample must have `r=ℓ^i` with `3≤i≤k−1`. The endpoint
`i=k` is excluded by the same two-degree argument. Thus the first
odd prime-power exponent not excluded by these deductions is now
nine; there its only possible minimum is `ℓ³`, and its occurring
degrees must be `ℓ³,ℓ⁴,ℓ⁵,ℓ⁶`.
