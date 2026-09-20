# Eight central elements: a sharper bound on ten degree-five profiles

Research theorem, 20 September 2026. This is an independently audited
analytic finite E1485 inequality, not a Lean theorem. No enumeration,
SAT assertion, or linear-programming infeasibility is used.

Assume order forty, minimum degree four, eight central elements, and
ten degree-five elements. Let `h` count tops, let `q` count the
degree-five elements with top-profile size three, and let `n22` count
tops whose central predecessor and successor blocks both have size two.

**Theorem.**

\[
\boxed{4q+n_{22}\le320-19h.}
\]

Together with the [previous ten-degree-five bounds](1485_order_forty_eight_central_ten_five.md),
this leaves only

\[
 h=15,\quad6\le q\le8,
 \qquad\text{or}\qquad
 h=16,\quad0\le q\le4.
\]

The inequality also excludes `h=17` directly. It does not by itself
exclude all ten-degree-five candidates or all eight-central models.

The subsequent [universal six-three-profile bound](1485_order_forty_eight_central_six_three_profiles.md)
removes `h=15,q=7,8`; the
[sixteen-top equality exclusion](1485_order_forty_eight_central_four_three_profiles.md)
removes `h=16,q=4`; and the
[all-four-profile bound](1485_order_forty_eight_central_all_four.md#1-reducing-the-top-count-and-degree-class-sizes)
removes `h=16,q=0`. The
[three-three-profile exclusion](1485_order_forty_eight_central_three_three_profiles.md)
also removes `h=16,q=3`. Finally, the
[unused-top source bound](1485_first_degree_source_unused_tops.md#3-fifteen-tops-and-eight-central-elements)
excludes fifteen tops with ten degree-five elements analytically.
The combined remaining ten-degree-five cases are
therefore precisely the necessary possibilities

\[
                    h=16,\qquad q\in\{1,2\}.
\]

No construction realizing one of these possibilities is asserted.

## 1. The local incidence intervals

For each top `u`, write

\[
 P=|P_u|,\quad C=|C_u|,\quad
 \alpha=|Row(u)\cap A|,\quad\beta=|Col(u)\cap A|.
\]

The [full-block theorem](1485_order_forty_ten_central_full_blocks.md)
gives `1≤P,C≤3`, and the existing auxiliary support bounds give
`α≤f(C)`, `β≤f(P)`, where `f=(4,3,1)`.

Set `w=7−2C−α`. It is nonnegative. In every central row the
four `C` blocks sum to eight and the four `α` values sum to ten,
so the four weights sum to two. Every top occurs in a central row;
therefore `w≤2`. This gives the full intervals

| Central successor size `C` | Possible `α` values |
| ---: | --- |
| 1 | 3, 4 |
| 2 | 1, 2, 3 |
| 3 | 0, 1 |

The same intervals hold for `β`, with `P` in place of `C`.

## 2. A pointwise inequality summed over all tops

These intervals imply

\[
 (P-2)\alpha+(C-2)\beta+\mathbf1_{P=C=2}
       \le -3PC+8(P+C)-19.                              \tag{1}
\]

Here is the entire local check; swapping `P,C` and `α,β` handles
the other three block types.

| `(P,C)` | Left side of (1) | Its upper bound, equal to the right side |
| --- | --- | ---: |
| `(1,1)` | `−α−β` | −6 |
| `(1,2)` | `−α` | −1 |
| `(1,3)` | `−α+β` | 4 |
| `(2,2)` | `1` | 1 |
| `(2,3)` | `β` | 3 |
| `(3,3)` | `α+β` | 2 |

The exact incidence moments are

\[
 \sum P=\sum C=32,\quad\sum PC=64,\quad\sum1=h,
 \qquad\sum\alpha=\sum\beta=40-q,
 \qquad\sum P\alpha=\sum C\beta=80.
\]

Thus `Σ(P−2)α=Σ(C−2)β=2q`. Summing (1) proves

\[
 4q+n_{22}\le-3\cdot64+8\cdot64-19h=320-19h,
\]

as claimed. At fifteen tops the right side is 35, hence `q≤8`;
at sixteen it is 16, hence `q≤4`. No conjectural equal-fiber,
full-core, or uniformity premise is used.
