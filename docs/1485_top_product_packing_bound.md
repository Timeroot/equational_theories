# Every top product has degree at most r²−r+1

Research note, 19 September 2026. This is an unconditional finite
E1485 theorem, not a Lean declaration. It strengthens both the
three-degree product bound and the later strict top-product gap.

Let `r,s` be the minimum and maximum translation degrees of a
nonempty finite E1485 magma, and write `n=rs`. Let `T` be its top
class and `Z` its central class.

**Theorem.** For all top vertices `u,w`,

\[
\boxed{d(u*w)\le r^2-r+1.}
\]

## Proof

Put `b=u*w`. Choose a central successor `z` of `w`; every top
vertex has one. The ordinary column `Col(z)` has exactly `r`
vertices, all top, and contains `w`. Put `t=z*u`, also top.

For every `v∈Col(z)`, choose `y` with `y*z=v` and set
`a_v=u*v`. E1485 gives

\[
t*a_v=(z*u)*(u*(y*z))=u.
\]

Recall the [fixed-parameter set](1485_image_research.md)

\[
F_t(u)=\{h:t*(u*h)=u\},\qquad
|F_t(u)|=\frac{n^2}{d(t)d(u)}=r^2.
\]

The same absorption identity used in the three-degree product bound,
now applied to `t*a_v=u`, gives `Row(a_v)⊆F_t(u)`.
Since `v∈Row(a_v)`, we obtain

\[
Col(z)\subseteq F_t(u).
\]

Taking `v=w` also gives `Row(b)⊆F_t(u)`. Moreover

\[
Row(b)\cap Col(z)=\{w\}.
\]

Indeed `b→w→z` is a path, and every path from `b` to the
central endpoint `z` is good. Its middle is consequently unique.
Counting the union inside the `r²`-element fixed-parameter set yields

\[
d(b)+r-1=|Row(b)\cup Col(z)|\le r^2,
\]

as required. No saturation, least-degree hypothesis, or full-core
assumption is used.

## Consequences at minimum degree three

Every product of two top vertices now has degree at most seven.
In particular:

- The four-central, nine-top branch cannot have least noncentral
  degree six: the [profile and slot argument](1485_strict_top_product_gap.md#4-four-central-and-nine-top-vertices-with-least-degree-six-require-degree-eight)
  would force its first noncentral top product to have degree eight.
  This excludes that whole branch, independently of the total order.
- A [central-block refinement](1485_refined_top_product_packing.md)
  subsequently excludes the entire
  [four-central, ten-top branch](1485_four_central_ten_top_exclusion.md),
  including both its regular and irregular degree-five alternatives.

For the least noncentral top-product degree there is a further,
stronger [existence bound](1485_first_top_output_fibers.md): every
non-full core supplies one of degree at most `r²−2r+2`.
