# Order twenty-eight is impossible

Research note, 18 September 2026. This is a global exclusion, not only
a minimum-degree-two result:

**Theorem.** No E1485 magma has order 28.

The filename records an earlier minimum-degree-two reduction, now
superseded by the shorter proof below. No assertion here is a Lean
declaration.

We use the [finite degree theorems](1485_graph_research.md), the
[constant-row classification](1485_spectrum_research.md), the
[two-degree cardinality theorem](1485_two_degree_lower_bound.md), and the
[four-degree minimum-two theorem](1485_four_degree_min_two.md).

## The three possible minimum degrees

Suppose a model has order 28. Its minimum degree \(r\) divides 28,
its maximum degree is \(28/r\), and \(r\le\sqrt{28}\). Thus

\[
r\in\{1,2,4\}.
\]

If \(r=1\), a translation row is constant. The constant-row
classification forces the finite order to be a power of two, contrary
to 28.

If \(r=2\), every degree is a divisor of 28 between 2 and 14, hence
belongs to \(\{2,4,7,14\}\). The
[neighbor-gap theorem](1485_min_two_neighbor_gap.md) forces degree four
to occur, since the degree spectrum is nonconstant. Reciprocity then
forces degree seven. All four degrees therefore occur, and the
four-degree minimum-two theorem forces order 32, a contradiction.

If \(r=4\), the maximum degree is seven. The only divisors of 28 in
that interval are four and seven, so exactly those two degrees occur.
The two-degree theorem would give order \(2r^2=32\), again a
contradiction.

All possible minimum degrees are excluded.
