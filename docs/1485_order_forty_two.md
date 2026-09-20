# Order 42 is absent from the E1485 spectrum

Research note, 18 September 2026. **There is no E1485 magma of order
42.** This is an analytic finite proof, not a Lean declaration. It
uses no SAT conclusion or exhaustive incidence enumeration.

Write `r` for the minimum translation degree and `s` for the maximum.
Finite structure gives `rs=42` and says every degree divides 42.
Thus `r∈{1,2,3,6}`.

- `r=1` would force power-of-two order.
- `r=2` has full core and therefore order `4·2^j`, impossible here.
- `r=6` leaves only degrees six and seven. The two-degree cardinality
  theorem would instead give order `2·6²=72`.

It remains to exclude `r=3`, where `s=14`.

## Only four central and nine top vertices remain

The possible degrees are `3,6,7,14`. Both middle degrees occur:
otherwise the two-degree theorem would give order eighteen. The least
noncentral degree is therefore six.

The central-defect theorems and
[five-central exclusion](1485_five_central_binary_blocks.md) leave
central cardinalities three, four, or nine. Full core, cardinality
nine, forces order `9·2^j`, not 42. Three central vertices force
degree four, which cannot divide 42.

For four central vertices the top count is nine or ten. The
[ten-top theorem](1485_four_central_residual.md#6-least-degree-six-forces-saturation-and-is-now-excluded)
would require a degree-nine first noncentral top product, again
impossible by degree divisibility. Thus only four central vertices
and nine top vertices remain.

Write `A,B,T` for the degree-six, degree-seven, and degree-fourteen
classes. The [least-degree-six lemma](1485_four_central_nine_top.md#6-least-degree-six-is-sharp-regular)
shows that every member of `A` is sharp-regular, with three top
neighbors in each direction. No member of `A` is a top-top product.
The top-product degree bound is nine, so all noncentral top products
would have to belong to `B`. At least one exists because the core
is not full.

## Degree-seven vertices have balanced top and sharp counts

Fix a degree-seven vertex `b`. Let `I,O` be its top predecessor
and successor counts, and `k⁻,k⁺` its sharp in/out counts. Its
non-top neighbors have degree six or seven; its sharp neighbors
are exactly those of degree six. Reciprocal-neighbor balance gives

\[
7k^-+6(7-I-k^-)+3I
=7k^++6(7-O-k^+)+3O.
\]

Thus `k⁻−k⁺=3(I−O)`. Both sharp counts lie between one and
three, so their difference has absolute value at most two. Hence

\[
I=O=t,\qquad k^-=k^+=k.
\]

Central-neighborhood partitions give `t∈{2,3,4}`.

## No degree-seven vertex can be a top product

Suppose `b` is such a product and let `g>0` count its ordered
top representations. The [variable top-fiber slot bound](1485_three_central_minimum_top_output.md#a-general-top-fiber-slot-bound)
with `q=6,p=7` gives

\[
g\le t(3-k)-(7-t-k)\max(0,t-1).
\]

For `t=2` or `t=3`, the right side is `1−k≤0`, a
contradiction. For `t=4`, it is `3−k≤2`.

In the last case let `U,V` be the four-element top predecessor
and successor profiles of `b`. At least two members `u∈U`
have singleton central successor sets: all four have singleton
predecessor sets, and only two tops have profile `(1,2)`. For each
such `u`, at most two members of `V` admit a central middle from
`u`. Indeed all members of `V` have singleton successor sets,
and every central row contains only two such tops.

Every noncentral pair in `U×V` must have good middle `b`: a bad
path would have a smaller-degree top-product replacement, which
could only be central or degree six, and degree six was excluded
as a top output. Each of those two rows consequently has at least
two good pairs. Thus `g≥4`, contradicting `g≤2`.

No noncentral top product is possible. This contradicts the
four-element, non-full central core and completes the exclusion
of order 42.
