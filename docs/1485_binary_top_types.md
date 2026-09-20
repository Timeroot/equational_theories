# A binary top-product obstruction at minimum degree three

Research note, 18 September 2026. This is a pen-and-paper theorem,
not a Lean declaration. It isolates the argument used in the
[five-central exclusion](1485_five_central_binary_blocks.md).

**Theorem.** Suppose a finite E1485 magma has minimum translation
degree three, every vertex has exactly three top predecessors and
three top successors, and there are maps `α,β:T→{0,1}` such that

\[
u*v\text{ is central}\quad\Longleftrightarrow\quad
\alpha(u)=\beta(v).
\]

Then its central core is full. The same conclusion holds with
inequality in place of equality, by reversing one of the two labels.

The maps need not be surjective, and the theorem makes no assumption
about the number of central or top vertices.

## Odd regular binary submatrices are constant

Let `K_uv=1` exactly when the product `u*v` is central.
Every `3×3` submatrix of `K` with constant row and column sums
has common sum either zero or three. Indeed, if both row types
occur and `b` columns have type zero, the two row sums are `b`
and `3−b`; equality is impossible. If only one row type occurs,
each column is constant, and equal column sums make the whole
matrix constant.

## The least noncentral degree would be six

Assume for contradiction that the core is not full. Let `q>3`
be the least noncentral degree, and choose a vertex `a` of that
degree. Every non-top neighbor of `a` is sharp. The
[least-degree balance lemma](1485_unrestricted_central_incidence.md)
gives equal sharp in/out counts `k`, with

\[
q=3+k,\qquad 1\le k\le3.
\]

On the three top predecessors and three top successors of `a`,
each top translation fiber has three slots. Its `k` sharp inputs
leave `3−k` top inputs. Every other path through `a` has a
strictly lower-degree replacement, necessarily central. Thus this
`3×3` submatrix of `K` has every row and column sum `k`.
The preceding binary observation forces `k=3` and `q=6`.
In particular no degree-six vertex is a top-top output: its three
sharp inputs already exhaust any top translation fiber.

## The first noncentral top output is impossible

Non-full core supplies a noncentral top-top product. Let its least
possible degree be `p`, and choose such an output `a`. The
[product-degree bound](1485_image_research.md) gives `p≤9`,
so `p∈{7,8,9}`.

Put `U=TopPred(a)` and `V=TopSucc(a)`. Minimality of `p`
means the bad paths through `a` in this rectangle have precisely
the central replacements: its bad-path matrix is `K[U,V]`.
If the sharp degrees are `k⁺,k⁻`, each row of that matrix has
sum at least `k⁺≥1`, and each column has sum at least `k⁻≥1`.

Both binary types must occur among the selected rows and among
the selected columns. Otherwise these positive sums force the
entire matrix to be one, leaving no good pair with product `a`.
Neither sharp degree can be two: both opposite types would then
need multiplicity at least two in a list of length three. Hence

\[
k^+=k^-=1.
\]

The type multiplicities are one and two in each list. Therefore
`K[U,V]` has four or five ones, and `a` has four or five good
ordered top endpoint pairs; write their number as `g≥4`.

The [top-fiber slot bound](1485_three_central_minimum_top_output.md),
with `r=3`, `q=6`, and sharp degree one, gives

\[
g\le6-(p-4)\max(0,9-p).
\]

For `p=7` or `p=8`, this gives respectively `g≤0` or `g≤2`.
For `p=9`, the [equality-case product bound](1485_top_output_saturation.md)
makes the good pairs a matching between `U` and `V`, giving `g≤3`.
Every case contradicts `g≥4`. The core is therefore full.
