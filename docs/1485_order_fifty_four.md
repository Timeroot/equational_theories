# Order 54 is absent from the E1485 spectrum

Research note, 18 September 2026. **There is no E1485 magma of order
54.** This is an analytic finite proof, not a Lean declaration. No
SAT conclusion or finite incidence enumeration is used.

Write `r` and `s` for the minimum and maximum translation degrees.
Finite structure gives `rs=54`; all occurring degrees divide 54.
Since `r≤s`, the possible minimum degrees are `1,2,3,6`.

- Minimum degree one forces power-of-two order.
- Minimum degree two has full core and forces order `4·2^j`.
- Minimum degree six leaves only degrees six and nine. The
  two-degree theorem would force order `2·6²=72`, not 54.

Thus only `r=3`, `s=18` needs consideration. Its possible degrees
are `3,6,9,18`. Both middle degrees occur: degree reciprocity pairs
six with nine, and if neither occurred the two-degree theorem would
force order eighteen. In particular the least noncentral degree is six.

## The remaining central counts

The central-defect theorems and
[five-central exclusion](1485_five_central_binary_blocks.md) leave
central cardinalities three, four, or nine.

- Full core, cardinality nine, forces order `9·2^j`, not 54.
- Three central vertices force degree four, which cannot divide 54.
- For four central vertices, the top count is nine or ten. The
  [ten-top profile theorem](1485_four_central_residual.md) with least
  noncentral degree six would force the first noncentral top product
  to have degree nine. The
  [strict top-product gap](1485_strict_top_product_gap.md) instead
  makes its degree strictly less than nine, a contradiction.

It remains to consider four central vertices and nine top vertices.

## The nine-top branch has no possible first noncentral top product

Every degree-six vertex is sharp-regular by the
[least-degree-six lemma](1485_four_central_nine_top.md#6-least-degree-six-is-sharp-regular).
Such a vertex cannot be a top-top product: any top translation fiber
at it would contain its three non-top sharp neighbors as well as a
top input, exceeding the fiber size three.

The central core is not full. The strict top-product gap therefore
supplies top vertices `u,v` with

\[
3<d(u*v)<9.
\]

The only occurring degree in this interval is six, just excluded as
a top product. This final contradiction excludes the nine-top branch
and completes the proof for order 54.
