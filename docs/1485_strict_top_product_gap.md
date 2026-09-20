# A failed central core has a top product strictly below saturation

Research note, 18 September 2026. This is an analytic finite theorem,
not a Lean declaration. Let `M` satisfy E1485, let `r` and `s` be
its minimum and maximum translation degrees, and write `n=rs`.
Let `Z,T` be its central and top classes, with `m=|Z|`.

Call a product of two top vertices **saturated** when its degree is
`r²`, the upper bound from the three-degree product inequality.

**Theorem.** Fix `u∈T`. Distinct top inputs `v,w` for which
`u*v` and `u*w` are saturated have disjoint central successor sets:

\[
v\ne w\quad\Longrightarrow\quad
(Row(v)\cap Z)\cap(Row(w)\cap Z)=\varnothing.
\]

The dual statement holds for saturated products in a fixed column.

## 1. Rotate two saturated products around a common central label

Suppose instead that a central `z` succeeds both `v` and `w`.
Put

\[
a=u*v,\qquad b=u*w,\qquad t=z*u.
\]

The vertex `t` is top because `z` is central. Since `v→z`,
there is an input `y` with `y*z=v`; E1485 gives

\[
t*a=(z*u)*(u*(y*z))=u.
\]

The same argument using `w→z` gives `t*b=u`.

For the [fixed-parameter sets](1485_image_research.md), the absorption
identity gives

\[
Row(a)\subseteq F_t(u),\qquad Row(b)\subseteq F_t(u),
\qquad |F_t(u)|=\frac{n^2}{d(t)d(u)}.
\]

Both `t,u` are top, so this last cardinality is `r²`. By
saturation, both ordinary rows also have size `r²`. Consequently

\[
Row(a)=F_t(u)=Row(b).
\]

Now `u→b` because `b=u*w`, and `b→v` because
`v∈Row(a)=Row(b)`. Thus `u→b→v` is a path whose good middle
is `u*v=a`. Its middle `b` has the same degree as `a`, so
strict degree descent forces `a=b`.

The [saturation matching theorem](1485_top_output_saturation.md)
applied to `u*v=u*w=a` then gives `v=w`, a contradiction.
This proves the theorem.

There is a quantitative version even when not all noncentral products
are saturated. The total central-successor weight of all noncentral
inputs in row `u` is `m(r−k⁺_u)`, whereas the saturated inputs
have total weight at most `m`. Hence

\[
\boxed{
\sum_{v\in T:\ r<d(u*v)<r^2} k^+_v
\ge m\max(0,r-1-k^+_u).
}                                                     \tag{1}
\]

The corresponding predecessor-weight inequality holds in each column.

## 2. The first noncentral top output is strictly below saturation

Suppose the central core is not full and every noncentral product
of two top vertices is saturated. Write

\[
k^+_v=|Row(v)\cap Z|,\qquad
K_{uv}=\mathbf1_{u*v\in Z},\qquad F=J-K.
\]

The theorem makes the central successor sets of all missing inputs
in any row pairwise disjoint. Therefore

\[
\sum_{v:F_{uv}=1}k^+_v\le m.
\]

The [central-incidence identities](1485_unrestricted_central_incidence.md)
give `Fk⁺=m(r\mathbf1−k⁺)`, so

\[
m(r-k^+_u)\le m,
\qquad k^+_u\ge r-1\quad(u\in T).
\]

Using the mixed moment and `Σk⁻=rm`, we obtain

\[
m^2=\sum_{u\in T}k^+_uk^-_u
\ge(r-1)\sum_{u\in T}k^-_u=r(r-1)m.
\]

Thus `m≥r(r−1)`. But the
[central-defect gap and boundary exclusion](1485_boundary_central_defect.md)
give `m≤r²−r−1` for a non-full finite core when `r≥2`.
This is a contradiction. At `r=1` the core is already full.

Every failed full core therefore supplies a noncentral top product
whose degree is strictly between `r` and `r²`:

\[
\boxed{\exists u,v\in T,\qquad r<d(u*v)<r^2.}
\]

This strengthens the earlier upper bound `d(u*v)≤r²`. It does
not exclude smaller irregular degrees or prove full core in general.

## 3. Minimum degree three consequences

At minimum degree three, the first noncentral top output has degree
at most eight. In particular:

- The four-central, ten-top branch cannot have least noncentral
  degree six: its [profile and slot bound](1485_four_central_residual.md)
  would force the first top output to have degree nine.
- In a four-central, nine-top model whose only degrees are
  `3,6,9,s`, least-degree-six vertices are sharp-regular and cannot
  be top outputs. Non-fullness would force a noncentral top output
  of degree strictly below nine, but there is no available degree.

The second assertion applies in particular to the remaining
minimum-degree-three branch at order 54, where `s=18`.

## 4. Four central and nine top vertices with least degree six require degree eight

Suppose the minimum degree is three, there are four central vertices
and nine tops, and the least noncentral degree is six. The
[least-degree-six lemma](1485_four_central_nine_top.md#6-least-degree-six-is-sharp-regular)
makes every degree-six vertex sharp-regular, so none is a top product.
The theorem above puts the first noncentral top-output degree `p`
strictly below nine. We now exclude seven, leaving exactly eight.

Suppose `p=7`, and fix a degree-seven noncentral top product `a`.
Write `I,O` for its top predecessor and successor counts, and
`k⁻,k⁺` for its sharp counts. Its non-top neighbors have
complementary degrees six or seven: complementary degrees are
occurring integers at most seven, and degrees four and five are
absent. Reciprocal-neighbor balance is therefore

\[
7k^-+6(7-I-k^-)+3I
=7k^++6(7-O-k^+)+3O.
\]

Thus `k⁻−k⁺=3(I−O)`. A noncentral top output has sharp counts
one or two, so the left side has absolute value at most one. Hence
`I=O=t` and `k⁻=k⁺=k`, with `t∈{2,3,4}`.

The [variable-neighborhood slot bound](1485_three_central_minimum_top_output.md#a-general-top-fiber-slot-bound)
gives

\[
g\le t(3-k)-(7-t-k)\max(0,t-1),
\]

where `g>0` counts the good ordered top endpoint pairs with middle
`a`. For `t=2` or `t=3`, the right side is `1−k≤0`, impossible.
For `t=4`, it is `3−k≤2`.

In the latter case both top profiles have four singleton central
labels. Among the four predecessor tops, at least two have singleton
central successor sets: there are only two tops of profile `(1,2)`.
For either such row, at most two of the four successor tops admit a
central middle, because each central row has exactly two tops with
singleton central successor sets. Thus each of these two rows has
at least two noncentral endpoint pairs. Minimality of `p` makes
all such pairs have good middle `a`, so `g≥4`, a contradiction.

Consequently

\[
\boxed{p=8.}
\]

In particular both six and eight occur, so the order is divisible by
24. The proof is independent of the total order and does not assume
that degree-seven vertices themselves are absent; it excludes seven
as the first noncentral top-output degree.
