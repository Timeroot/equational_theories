# Order forty with eight central elements: current proof inventory

Updated 20 September 2026. This branch is **not yet excluded**. The
table below lists the degree-class counts not excluded by the linked
proofs, not asserted magma constructions. None of these research
results is a Lean declaration.

Let `h,a,b` count elements of degrees `10,5,8`, respectively; there
are eight elements of degree four. Let `q` count degree-five elements
with three top predecessors and successors. The remaining `a−q`
have four. In particular `a+b+h=32`.

## Proved reductions

- [At most ten degree-five elements](1485_order_forty_eight_central_high_five.md).
- [Weighted top bound](1485_order_forty_eight_central_top_bound.md),
  followed by the [nineteen-top exclusion](1485_order_forty_eight_central_nineteen_tops.md):
  initially `15≤h≤18` and `4a+q≤160−7h`. The
  [fifteen-top exclusion](1485_order_forty_eight_central_fifteen_profile_bound.md#6-consequence-fifteen-tops-are-impossible-at-order-forty)
  now sharpens this to **`16≤h≤18`**.
- [At most six smaller profiles](1485_order_forty_eight_central_six_three_profiles.md),
  and the two [profile-capacity inequalities](1485_order_forty_eight_central_profile_potentials.md).
- At `a=10`, the [profile inequality and equality exclusions](1485_order_forty_eight_central_ten_five_profile_bound.md)
  and the [unused-top source argument](1485_first_degree_source_unused_tops.md)
  leave only `(h,q)=(16,1),(16,2)`. In particular the
  [three-profile case at sixteen tops](1485_order_forty_eight_central_three_three_profiles.md)
  is excluded analytically.
- With eighteen tops and eight degree-five elements, all cases are
  excluded: [one](1485_order_forty_eight_central_eighteen_one_small.md),
  [two](1485_order_forty_eight_central_eighteen_two_small.md), or
  [no small profiles](1485_order_forty_eight_central_eighteen_all_four.md).
  The proofs share one finite central-incidence generator: 200 fixtures,
  independently checked for both profile sizes, no SAT.
- At eighteen tops, the [general small-profile bound](1485_order_forty_eight_central_eighteen_small_profile_bound.md)
  gives `q≤2`, and the [two-profile exclusion](1485_order_forty_eight_central_eighteen_two_small_exclusion.md)
  sharpens it to **`q≤1`**, with no assumption on `a`.
- The [unified all-small exclusion](1485_order_forty_eight_central_all_small.md)
  is entirely analytic at `16≤h≤18`: **`q<a`**. It supersedes
  the earlier finite-assisted all-small proof at eighteen tops.
- With seventeen tops and nine degree-five elements, both
  [one small profile](1485_order_forty_eight_central_seventeen_nine_one_small.md)
  and [no small profiles](1485_order_forty_eight_central_seventeen_nine_all_four.md)
  are excluded analytically. This class-count branch is closed.
- The [all-size-four branch](1485_order_forty_eight_central_all_four.md)
  originally gave four degree-class splits; the two exclusions above
  leave only `(h,a,b)=(17,8,7),(18,7,7)`. The former's
  degree-eight counts need not all be balanced.
- At fifteen tops the analytic
  [unused-top identities](1485_first_degree_source_unused_tops.md) give
  `8a−7q≤30` and `a−q≤2`. The complete 69-family
  [finite profile check](1485_order_forty_eight_central_fifteen_profile_bound.md)
  gives `q≤4`, excluding this entire top-count branch.

All the analytic statements above have been independently audited.
The two finite lemmas are explicitly separated from those analytic
arguments; neither is represented as a Lean proof.

## Remaining necessary class counts

These are the exact surviving **numerical possibilities under the
listed restrictions**, not a completeness claim about all consequences
of E1485: **33 triples `(h,a,q)` in nine degree-class splits**.
A later structural argument may exclude further entries.

| Tops `h` | Degree-five `a` | Degree-eight `b` | Smaller-profile count `q` |
| ---: | ---: | ---: | --- |
| 16 | 6 | 10 | 4, 5 |
| 16 | 7 | 9 | 2–6 |
| 16 | 8 | 8 | 1–5 |
| 16 | 9 | 7 | 1–4 |
| 16 | 10 | 6 | 1, 2 |
| 17 | 6 | 9 | 3–5 |
| 17 | 7 | 8 | 1–6 |
| 17 | 8 | 7 | 0–3 |
| 18 | 7 | 7 | 0, 1 |

For reproducibility, besides the displayed exclusions and profile
inequalities, the numerical filter uses sharp coverage `b≤a+q`
and the exact residual top-pair counts

\[
 F=h^2-128-12a+6q,\qquad W=8(4h-32-3a+q),
 \qquad0\le F\le W\le3F.
\]

For `q>0`, the one-hole theorem further gives `2W≤5F+16`.
No optimizer result is included in the table's premises.

At sixteen tops and ten degree-five elements, the
[one-small-profile table](1485_order_forty_eight_central_sixteen_one_profile.md)
and [two-small-profile block restrictions](1485_order_forty_eight_central_sixteen_two_profiles.md)
are independently audited necessary refinements, not exclusions.
The fifteen-top finite check passed all 226,500 complete normalized
central tables with independent profile oracles. Partial searches and
unfinished diagnostics are not treated as exclusions here.
