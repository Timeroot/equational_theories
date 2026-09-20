# E1485: current proof frontier

Updated 20 September 2026. The square-or-double-square spectrum conjecture
is **not yet proved**. This page distinguishes analytic pen-and-paper
proofs, proofs with explicit finite incidence checks, and open targets.
None of the new research results below is a Lean declaration.

For a nonempty finite model write `n` for its order, `r` for its
minimum translation degree, and `Z,T` for the central and top classes.
Established finite structure gives `n=r·max d` and `r≤|Z|≤r²`.
The **full-core hypothesis** is `|Z|=r²`.

## Main outcome and remaining gap

Full core implies **`n=r²·2^j`**, hence square or twice-square order,
at every minimum degree. Full core is proved unconditionally for
minimum degrees **one, two, and three**. Its proof for arbitrary
`r` remains open.

The new [minimum-degree-three theorem](1485_min_three_full_core.md) is:

> Every finite E1485 magma with minimum translation degree three has
> full core and order **`n=9·2^j`**. Conversely every such order is
> realized at this minimum degree.

This proof combines analytic arguments with **five explicit finite
profile lemmas**, all rerun successfully. Its dependency inventory
and verification commands are in the linked theorem. In particular,
it is not yet a completely formalized Lean proof.

Any counterexample to the square-or-double-square spectrum conjecture
must therefore have **minimum translation degree at least four**.
No non-full finite model is asserted to exist.

The [order-forty, four-central case is now completely excluded](1485_order_forty_four_central_exclusion.md).
Its proof inventory separates analytic steps, explicit finite incidence
checks, and retained, independently verified LRAT refutations. This is
not yet a Lean theorem. The [ten-central case is also excluded](1485_order_forty_ten_central_exclusion.md),
this time entirely analytically. The
[nine-central case is now excluded too](1485_order_forty_nine_central_exclusion.md):
the new final step combines a central-moment inequality with two small
orbit checks. Its earlier three-profile reduction still uses five
previously retained LRAT proofs. Order forty itself remains open: its
surviving central counts are **five through eight**, all at minimum degree four.

At minimum degree four, the new divisor gap already forces a first
noncentral top-output degree of five, six, or seven if the core is
not full. The defect bounds restrict its central count to `4,…,10`.
The minimum-four classification remains open; the refinements below
exclude some branches but do not complete it. With exactly five
central vertices, the new analytic
[degree-seven exclusion](1485_min_four_five_central_seven_exclusion.md)
  lowers the first-output bound to **five or six**.

With six central vertices, the entire
[degree-seven first-output branch](1485_min_four_six_central_seven_exclusion.md)
is now **excluded analytically**. Singleton-label separation, a
containment bound, and a diagonal-cell argument eliminate all triple
blocks; an elementary singleton-crown lemma then finishes the proof.
  The first noncentral top-product degree is therefore **five or six**.
No finite enumeration is needed. This does not exclude all models with
six central vertices or finish the minimum-four classification.
With seven central vertices, the
[degree-seven branch is now excluded as well](1485_seven_central_three_by_two.md).
The proof combines the new uniform analytic singleton separation with
three explicit finite profile lemmas. All eleven cases of the final
lemma were independently rerun with direct witness comparisons.
In particular, a first-output degree of seven at minimum four now
requires **at least eight central vertices**.

## New analytic tools

- [One-hole first-output grids](1485_one_hole_first_output_grid.md):
  if `r=t+1`, `|Z|=t²−1`, and a first degree-`r+1` top output
  has profile size `t`, there are **at most `2t−2` maximal central
  blocks in each direction**. If both counts are maximal, every
  opposite pair of maximal blocks intersects exactly once, and the
  two block-multiplicity deficiency sets are disjoint. This general
  analytic theorem has been independently audited. It improves the
  eight-central triple-block bound from five to four and requires no
  finite enumeration. The same hypotheses give
  `t²+2t≤|T|≤t²+4t−1`, with the lower endpoint excluded for `t≥4`,
  and explicit linear bounds on the first-degree class and its smaller
  profiles.
- [Singleton-source saturation](1485_singleton_source_first_degree_saturation.md)
  and the [general unused-top identities](1485_first_degree_source_unused_tops.md):
  at first noncentral top-output degree `r+1`, a singleton central
  successor block with `r` first-degree successors forces at most
  `r²` tops. A source block of size `r−1` with a first-degree
  successor of profile size `t` forces at least `r(r−1)+t` tops.
  These are general, independently audited analytic counting arguments.
  The unused-top identities now also extend to every least noncentral
  top-output degree `p=r+k`, with retained unions of `k` blocks;
  the correct profile range is `k+1≤t≤r+k−1`.
- [Maximal first-output grids](1485_maximal_first_output_grid.md):
  suppose `r≥4`, `|Z|=(r−1)²`, and the first noncentral top-output
  degree is `r+1`, with at least one such output having `r−1` top
  neighbors. Then **`r²≤|T|≤r²+r−1`**. At most four degree-`r+1`
  vertices can have this smaller profile when `r=4,5`, and at most
  three when `r≥6`. Exact complement tilings, central partitions,
  and a weighted incidence inequality prove this analytically at
  arbitrary minimum degree. The theorem was independently audited;
  its hypotheses are essential and it is not a general full-core proof.
- [Near-square central class capacities](1485_near_square_central_class_capacity.md):
  if `r≥4`, `|Z|=(r−1)²+1`, and every central top block has size
  at most `r−1`, the degree-`r+1` class has at most `2r−1` vertices.
  At equality there are exactly `r²` tops and every vertex has exactly
  `r` top neighbors in each direction. A class of size `2r−2` instead
  forces `|T|≤r²+r−3`. This general analytic theorem was independently
  audited; it does not impose a restriction on the other degree classes.
- [Pointwise top-product packing](1485_top_product_packing_bound.md):
  every `u,w∈T` satisfies `d(u*w)≤r²−r+1`.
- [Central-block refinement](1485_refined_top_product_packing.md):
  if `t*b=u` with `t,u∈T`, then
  `d(b)≤r²−(r−1)|Col(t)∩Z|`. This controls the actual
  fixed-parameter fiber, not just its cardinality.
- [Small-block confinement of top returns](1485_top_return_small_blocks.md):
  if a product of two tops is top, both central blocks of **all three**
  vertices have size at most `floor((r²-max d)/(r-1))`, for `r>1`.
  At order forty and minimum four this excludes every triple-block
  top from every auxiliary top-to-top edge. The proof is analytic
  and independently audited; it does not yet show that no such
  top-valued products remain.
- [First-top-output fibers](1485_first_top_output_fibers.md):
  a least-degree noncentral top output has balanced top neighborhoods.
  Every top fiber at it contains all its non-top neighbors; there are
  at most `r−1` of those in either direction. The associated
  central-middle matrix is regular.
- The same theorem gives a first noncentral top-output degree
  `r<p≤r+(r−1)⌊|Z|/r⌋≤r²−2r+2` in every non-full core.
  It strengthens the earlier [strict gap](1485_strict_top_product_gap.md).
- If `|Z|=r>1`, the next degree is `r+k` for a **proper**
  divisor `k|r`. This excludes the previously open `2r`
  alternative for every `r>1`. For prime `r`, the next
  degree is `r+1`.
- With [one extra central vertex](1485_one_extra_central_first_output_gap.md),
  namely `|Z|=r+1` and `r≥4`, the first noncentral top output
  has degree **at most `2r−2`**. A short exact-intersection lemma
  replaces the earlier case-specific rectangle analysis.
- The new [two-extra-central-vertex theorem](1485_two_extra_central_first_output_gap.md)
  extends the same conclusion to **`m=r+2`, for every `r≥4`**:
  the first noncentral top output has degree at most `2r−2`.
  This includes the completed six-central case at minimum four.
  Its proof is entirely analytic.
- The [small-central-block theorem](1485_small_central_blocks_first_output_gap.md)
  gives the same gap whenever all central blocks have size at most two
  and `m<2r`, for `r≥4`. For **`r≥6` no separate central-count
  hypothesis is needed**: at `m=2r`, the boundary output would require
  a crown larger than the maximum size five for two-element sets.
- More generally, [singleton-label separation and containment](1485_singleton_central_labels_first_output.md)
  constrain boundary outputs `p=2r−1` when `m≤2r−2`.
  Singleton predecessor and successor labels are disjoint; retained
  crown columns cannot be nested. They imply the block-size bound
  `b≤3m−4r+2` and, for `r≥4`, the strict cardinality bound
  **`m>4r/3`** at this boundary degree. These are general structural
  lemmas, not assumptions about a small finite search.
- The new
  [maximal-central-block bound](1485_maximal_central_block_first_output_gap.md)
  gives `p≤2r−2` for `r≥3` whenever a top has central block sizes
  `(m−r+1,1)` or `(1,m−r+1)`, where `m=|Z|`. At the excluded
  boundary `p=2r−1`, exact replacement produces crown profiles
  and then forces two identical crown columns. This argument is
  analytic and is not restricted to minimum degree four.
- The [bounded-central-excess theorem](1485_bounded_central_excess.md)
  gives `p≤r+m−⌈m/binom(2c+2,c+1)⌉` when `m=|Z|=r+c`.
  At `c=1`, a new sharp [regular two-set bound](1485_linear_two_set_regular_bound.md)
  improves the binomial factor six to five, giving
  `p≤min(2r−2,2r+1−⌈(r+1)/5⌉)` for `r≥4`.
  These are analytic inequalities, not finite enumerations.
- At the next central count, [overlapping singleton labels](1485_boundary_singleton_overlap.md)
  have a restricted form when `m=p=2r−1`: each common label has
  unique singleton occurrences pointing from a predecessor-only label
  to a successor-only label. The outside maps have fibers at most
  `r−2`, giving at most `2r−5` common labels. These are necessary
  conditions only. The stronger uniform separation theorem below now
  supersedes these overlap bounds.
- The [joint outside-fiber bound](1485_common_singleton_joint_fibers.md)
  strengthens these analytic overlap restrictions. If two outside fibers
  have sizes `k,l` and intersection size `j`, their residual central
  partitions give `m−k−l+j≤(r−k)(r−l)`. Together with a block-excess
  argument this makes the number of common singleton labels at most
  **`2r−6` for every `r≥4`** at `m=p=2r−1`, improving the preceding
  bound by one. The proof is analytic at all these minimum degrees.
- The new [uniform singleton-label separation theorem](1485_boundary_output_singleton_separation.md)
  proves **`S_P∩S_C=∅` for every `r≥3` whenever `p=2r−1`**, with
  no central-count restriction. Arbitrary-omission replacement would
  give an isolated complete bipartite block; its equality case forces
  too many singleton labels into a unique outside label. This analytic
  proof supersedes all earlier finite singleton-overlap checks.
- The [full-size block theorem](1485_full_central_blocks_boundary_output.md)
  shows, at the same first-output degree, that any size-`r` predecessor
  block forces **no singleton successor blocks**, and dually. It has no
  central-count restriction. At `m=2r`, such a block therefore forces
  every opposite block to be a pair and exactly `r²` top vertices.
- At the same boundary, the
  [maximal-size block exclusion](1485_boundary_singleton_overlap.md#no-central-block-can-have-size-r-at-the-boundary)
  gives **`|P_v|,|C_v|≤r−1` for every top** when `m=2r−1`,
  for every `r≥3`; the full-size block theorem above extends this to
  every `m<2r`. No such unconditional bound is proved for `m≥2r`.
  This does not require separation of the singleton labels. A block
  of size `r` would meet every opposite block exactly once and give
  a crown column with too many ones. This subsumes the earlier
  special exclusion of a profile `(r,r)`.
- The [square-root divisor gap](1485_first_top_output_divisor_gap.md)
  strengthens the first-output bound to
  `⌈(p−r)/(r−1)⌉·(p+1)≤r²`. If the next occurring degree is
  at least `ℓr`, a non-full core requires **`r>ℓ²`**.
  In particular, every odd prime seventh power is excluded analytically.
- [Common central blocks](1485_first_output_partition_gap.md) sharpen
  that last necessary condition to **`r≥ℓ²+ℓ−1`**. More precisely,
  for `p≥2r`, put `a=⌈(p−r)/(r−1)⌉` and
  `c=⌈(p−r)/(r−a)⌉`. Then `2a<r` and
  `a(p+1)+c(r−2a)≤r²`. At minimum five this lowers the maximum
  first-output degree to ten; at minimum six, to fourteen.
- [Ordered auxiliary degrees](1485_auxiliary_ordered_degree_bound.md)
  extend the fiber argument to every vertex. At prime-power order
  `ℓ^e` with minimum degree at least `ℓ`, every vertex has at least
  `ℓ` sharp neighbors in each direction. This gives further restrictions,
  not an exclusion, at the remaining ninth-power frontier.
- [Four-degree top-return bounds](1485_four_degree_minimal_core_returns.md)
  give uniform restrictions when `|Z|=r` and the degrees are
  `r,r+k,2r,2(r+k)`. In particular, if `k>1`, every reciprocal-class
  vertex has sharp degree below `r`. This supplies a shorter analytic
  route to the order-48 bounds and further class-size bounds at larger
  minima; it does not exclude the entire four-degree family.
- [Return matching for arbitrary products](1485_general_return_matching.md)
  gives `j_b^-+j_d^+≤n/d(b*d)` for sharp neighbors in any
  ordinary-edge-independent set. At equality every matched edge meets
  that set. Applying this also to intermediate-degree products gives
  a much shorter, entirely analytic fourteen/six exclusion at order 40.
- [Central-assisted top returns](1485_central_assisted_top_returns.md)
  force unique ordinary middles and bound intersections with the top
  profiles of a first output. These are unconditional finite-model
  lemmas, with the first-output hypothesis stated for the profile bound.
- [Mixed-return capacity](1485_four_degree_mixed_return_capacity.md)
  bounds the number of good-good three-edge paths with both internal
  vertices in the intermediate classes by `r`, in the minimal-core
  four-degree family `r,r+k,2r,2(r+k)`. The sharper bound at a
  degree-`2r` return keeps both bad-extension counts. This analytic
  constraint includes top-valued returns; it does not exclude the family.
- [Profiles at first output degree `r+1`](1485_first_successor_degree_profiles.md)
  cannot differ by just one top vertex: their central-middle permutation
  would force two distinct central rectangles to overlap. At minimum four
  and first-output degree five, the common top-profile size is three or
  four. Size three requires `5≤m≤9` and at most one shared top; size
  four allows at most two shared tops unless the profiles coincide,
  in which case `m=4`. These are analytic reductions, not exclusions
  of the remaining profile sizes.
- [Exact regular-hole fibers](1485_order_forty_regular_hole_fibers.md)
  strengthen aggregate top-pair counts to individual endpoint counts.
  In the balanced twelve/eight profile grid, the central-valued pairs
  in each nonempty hole rectangle form either an empty matching or a
  perfect matching. Partial nonempty overlap is impossible. This analytic
  observation finishes the balanced branch after a small incidence
  reduction and also has a separately checked LRAT application.
- The [unit-or-large central-tile theorem](1485_unit_large_central_tiles.md)
  excludes, for every `r≥3`, the pattern with `(r−1)²+1` central
  elements and all block pairs either `(1,1)` or `(r−1,r−1)`.
  It uses balanced first-output profiles and an invertible central
  incidence matrix, with no bound on the first-output degree and no
  finite enumeration. Consequently, at this central count and with all
  blocks at most `r−1`, the top-class bound is strictly below
  `2((r−1)²+1)`. This is a general analytic exclusion, not full core.
- The [global order-forty good-pair count](1485_order_forty_uniform_top_counts.md)
  proves that four top neighbors in both directions at every vertex
  force **at most six central elements**. It counts bad internal paths
  globally, so no equality of individual predecessor/extension counts
  is assumed. The [full-block reduction](1485_order_forty_ten_central_full_blocks.md)
  consequently rules out size-four central blocks for every central
  count seven through ten at this order. Both arguments are analytic.

## Minimum degree four: new local exclusions

These include a completed local order-forty exclusion and restrictions
on other hypothetical non-full models, **not** proofs excluding either
order forty or order forty-eight in full.

- At `r=4,m=7`, the entire first-output-degree-seven branch is
  [excluded](1485_seven_central_three_by_two.md). Analytic singleton
  separation and the size-four block exclusion reduce it to three
  finite profile lemmas, in noncircular order: `(3,3)`, `(3,1)`, then
  `(3,2)`, with their duals. Once all triple blocks are excluded,
  the analytic small-block theorem finishes the argument. The final
  eleven-case check visited 16,523,801 states and found no surviving
  incidence cover. Earlier singleton-overlap and single-singleton-label
  checks remain independently verified alternatives or corroboration,
  not dependencies of this shortest proof. The result is not yet Lean.
- With five central vertices, a
  [small central-rectangle argument](1485_min_four_five_central_partitions.md)
  and the row-local output bound exclude first-output degree seven.
  This is analytic and applies at every order with this minimum and
  central count, not only at orders 40 or 48.
- At order 40 with four central vertices, **every possible degree-five
  class size is now excluded**; see the
  [complete theorem and dependency inventory](1485_order_forty_four_central_exclusion.md).
  The following paragraphs describe its reductions and finite premises.
  The [permutation-profile argument](1485_min_four_large_five_class.md)
  forces at least one profile family into a single Klein-four coset
  once the class has at least twelve vertices. The smaller cases have
  an explicit two-exceptional-vertex alternative. At saturation, an
  [analytic collapse](1485_order_forty_saturated_profiles.md) forces
  both families into single cosets. The
  [explicit finite check](1485_order_forty_single_coset.md) then excludes
  every candidate: 10,368 binary linear systems leave 144 forced
  partial tables, all contradicting E1485. This is an exact
  finite-assisted proof, not a SAT result or a Lean declaration.
  The [next class size, fifteen](1485_order_forty_near_saturation.md),
  is excluded analytically: small sharp degree sums force a top
  return which violates the four-element fiber matching.
  Size fourteen is now [excluded analytically](1485_order_forty_fourteen_exclusion.md):
  arbitrary-product return matching forces the sharp-degree-three
  vertices' mutual products into the degree-five class. The remaining
  internal-degree counts contradict each other. This short argument
  needs **no finite enumeration**. It supersedes both the earlier
  six-vertex incidence reduction and the longer affine-profile proof,
  which are retained as alternative structural analyses. The separate
  size-sixteen exclusion still has its stated finite-check dependency.
  At size thirteen, the
  [three-high-sharp distribution](1485_order_forty_thirteen_three_high.md)
  is also excluded analytically: edgewise bad-extension balance forces
  a star-and-permutation graph with a forbidden five-walk. The
  [two-high-sharp distribution](1485_order_forty_thirteen_two_high.md)
  is excluded by a separate, audited seven-vertex incidence check:
  488,266 internal graphs reduce to two final types, both with explicit
  forbidden return paths. This second exclusion has a finite-check
  dependency. The same checker also excludes the
  [one-high-sharp distribution](1485_order_forty_thirteen_one_high.md):
  1,413,400 internal graphs reduce to seven final types, each violating
  a return-path bound. The last distribution, **`(1,2,2,2,2,2,2)`**,
  is now excluded as well. In that distribution, the
  [affine-profile reduction](1485_order_forty_thirteen_profiles.md)
  now excludes every mixed-coset arrangement analytically: both
  degree-five profile families use single cosets, all seven partner
  profiles are affine transversals, and every internal edge has exactly
  two top return inputs. A further exact seven-vertex incidence check
  takes about **2.5 seconds** and leaves one internal type. The
  [final affine-profile obstruction](1485_order_forty_thirteen_directions.md)
  excludes it analytically: three attached directions split two plus one,
  and the resulting three-hole incidence counts contradict every possible
  rank pattern. Thus **the entire thirteen/seven split is excluded**.
  The final obstruction uses neither a SAT result nor an unverified
  solver certificate. The earlier finite incidence reductions remain
  explicit dependencies, and this is not yet a Lean theorem. The
  remaining degree-five class sizes are handled next; other central
  counts at order forty remain open. The
  [ten/ten split is now excluded](1485_order_forty_ten_profile_expansion.md):
  repeated profiles force a three-element set with at most four internal
  predecessors, while eight independently checked LRAT refutations rule
  out that expansion failure. The encoder has only 200 primary Boolean
  variables and no auxiliary variables; all proof files are retained.
  The [eleven/nine split is also excluded](1485_order_forty_eleven_profile_capacity.md).
  Repeated profiles force a compressed pair of low-sharp targets; exact
  intersection capacities exclude all 37 normalized cases. All archived
  LRAT proofs were independently replayed against regenerated CNFs,
  including their exact hashes, in 38.4 seconds. No unverified solver
  report is used in either exclusion.
  At size twelve, new [high-sharp profile restrictions](1485_order_forty_twelve_high_profiles.md)
  rule out partner profiles equal to an occupied-family line and make
  every sharp-degree-three partner affine. Conditional on both degree-five
  families using single cosets, each such partner has exactly two good
  top pairs. The
  [two-high-sharp distribution](1485_order_forty_twelve_two_high_exclusion.md)
  `(1^6,3^2)` is now excluded by a short analytic endpoint-counting
  argument, independently of any affine-profile choice. The
  [one-high distribution](1485_order_forty_twelve_one_high_exclusion.md)
  `(1^5,2^2,3)` is now completely excluded as well. The high vertex's
  internal loop has an explicit 56-permutation incidence check; its
  medium and low successor cases have separately verified LRAT proofs.
  Both archives and independently regenerated CNFs match their recorded
  hashes. This leaves **`(1^4,2^4)`** at class size twelve. The
  [analytic profile bounds](1485_order_forty_twelve_no_high_profiles.md)
  exclude an empty predecessor-profile line and force a single successor
  coset whenever one predecessor line has multiplicity one. The latter
  [thin-line pattern is now completely excluded](1485_order_forty_twelve_thin_exclusion.md)
  by an independently checked line-capacity refutation (0.85 seconds
  for CNF generation, 6.2 seconds for proof production, 0.72 seconds
  to verify). After choosing a single-coset orientation, the remaining
  predecessor multiplicities are `(4,4,2,2)`, `(4,3,3,2)`, and
  `(3,3,3,3)`. All
  [mixed successor-coset cases](1485_order_forty_twelve_mixed_exclusion.md)
  are now excluded by five checked refutations. With both families in
  single cosets, [joint capacities](1485_order_forty_twelve_joint_capacities.md)
  exclude six profile-grid orbits. The final balanced orbit is
  [excluded by a small incidence check and an analytic fiber contradiction](1485_order_forty_twelve_balanced_incidence.md).
  An independent C++ rerun reproduced all 56 survivors and their required
  four-cycle structure in 9.74 seconds; the analytic tail was separately
  audited. A second, independently checked
  [regular-hole LRAT proof](../data/1485_certificates/A12_REGULAR_HOLES.md)
  excludes the same final orbit without that incidence classification.
  Thus the entire four-central case is complete. Central counts five
  through eight remain open at order forty; their first-output degree is
  five, not the degree seven addressed by the earlier central-count
  exclusions.
- With ten central elements at order forty, the
  [entire branch is now excluded](1485_order_forty_ten_central_exclusion.md)
  **analytically**, with no enumeration or SAT premise. The
  [small-central-block reduction](1485_order_forty_ten_central_small_blocks.md)
  first leaves seventeen or eighteen tops. Every ordinary top-to-degree-five
  edge then uses at least seven of the ten auxiliary parameters, bounding
  the degree-five class by seven. At seven, central partitions give a
  parity contradiction. At six, two families of central blocks partition
  the same subset but their counts differ by eight, beyond the available
  ten central labels. The unified proof and its prerequisites were
  independently audited. The earlier
  [seventeen-top proof](1485_order_forty_seventeen_tops.md) and
  [eighteen-top quantitative bounds](1485_order_forty_ten_central_eighteen_tops.md)
  remain independent alternatives, not dependencies of this shorter proof.
- With nine central elements and a first degree-five output having
  three top neighbors, the [complement-tiling argument](1485_nine_central_three_profile.md)
  and the [eighteen-top exclusion](1485_nine_central_eighteen_top.md)
  restrict the top count to **sixteen or seventeen**, independently
  of the total order. Exact auxiliary membership gives disjoint tilings
  of three column complements; their saturation and a small explicit
  integer case split exclude all other moment solutions. The arithmetic
  checker was read and independently rerun. At eighteen tops, three
  normalized profiles have analytic exclusions and the other five have
  [archived LRAT refutations](../data/1485_certificates/NINE_CENTRAL_H18.md).
  All five CNFs were independently regenerated; all archive, CNF, and
  decompressed-proof hashes matched; independent LRAT replay took
  3.46 seconds in total. No order-forty-only fiber bound was used.
  These are externally checked finite proofs, not Lean declarations.
  This does not handle the
  alternative in which every degree-five profile has size four.
  At order forty the [sixteen-top case is now entirely excluded](1485_nine_central_sixteen_exclusion.md).
  The [analytic reduction](1485_nine_central_sixteen_degree_counts.md)
  forces `(|A_5|,|B_8|,|A_3|)=(7,8,2)`, six triple blocks on each
  side, and four degree-eight vertices of each top count three and five.
  It then forces at least 25 bad paths through a four-vertex subset.
  Two explicit sixteen-bit graph lemmas give respective upper bounds
  20 and 24, completing the contradiction. The reductions and source
  were independently audited; both checks were independently rerun.
  They use exact enumeration, not optimizer infeasibility or SAT claims,
  and are not Lean declarations. Consequently at order forty the
  nine-central case with a size-three degree-five profile would require
  **exactly seventeen tops**. The subsequent
  [seventeen-top proof](1485_nine_central_seventeen_degree_counts.md)
  excludes that possibility analytically: joint capacity slack forces
  `a=6,b=8`, after which four- and five-vertex matrix bounds give
  contradictions. Thus **no degree-five size-three profile can occur**
  in an order-forty model with nine central elements.
- In the remaining all-size-four-profile alternative, the
  [nine-central reduction](1485_order_forty_nine_central_reduction.md)
  excludes eighteen and nineteen tops and forces the single degree split
  **`(|Z|,|A_5|,|B_8|,|T|)=(9,7,7,17)`**. Every degree-eight
  vertex has sharp degree one in each direction and balanced top counts.
  Its sharp two-step endpoint relation is a permutation matrix.
  The paired central type count `N22` is zero or two. The
  [uniform top-count subcase is now excluded analytically](1485_order_forty_nine_central_uniform_exclusion.md):
  a seven-point design identity and the one-degree-five five-cycle rule
  give an integer matrix whose square has both even and odd trace.
  The same obstruction works at every odd internal degree under the
  analogous graph hypotheses. No enumeration or projective-plane
  classification is used. The [remaining graph bounds](1485_order_forty_nine_central_nonuniform_B.md)
  force fifteen through twenty internal edges and three through six
  top neighbors at each degree-eight vertex. A subsequent
  [ninety-case orbit proof](1485_order_forty_nine_central_fifteen_edges.md)
  excludes fifteen edges, with a literal forbidden five-walk in its one
  intermediate graph. A new
  [analytic central-moment inequality](1485_nine_central_missing_degree_five_neighbor.md)
  forces a top with no degree-five neighbors in one direction, excluding
  all sixteen-edge profiles whose internal degrees are at least two.
  The stronger central-gap calculation now forces `K=19` or `20`,
  no internal degree-one vertices, and `τ≥19`. The
  [81-case whole-orbit proof](1485_order_forty_nine_central_dense_closed_orbits.md)
  excludes `τ=K`; the
  [396-case single-defect proof](1485_order_forty_nine_central_twenty_one_defect.md)
  excludes `K=20,τ=19`. Both were independently audited and rerun.
  This completes the [entire nine-central exclusion](1485_order_forty_nine_central_exclusion.md).
  The earlier fifteen- and sixteen-edge finite checks are optional
  corroboration, not mathematical dependencies of this final reduction.
- At nine central elements and nineteen tops, the
  [seven-triple central type is excluded](1485_nine_central_nineteen_seven_triples.md)
  even when the first degree-five output has profile size four.
  Its complete central normalization and encoder were independently
  audited; the [retained LRAT proof](../data/1485_certificates/NINE_CENTRAL_H19.md)
  was checked against a regenerated, hash-identical CNF. The other
  nineteen-top types with size-four profiles are not excluded by this
  theorem, and time-limited exploratory checks are not proof premises.
  At order forty, the new degree-class capacity argument above now
  excludes all nineteen-top types; this retained finite theorem has
  the separate advantage of not requiring the order to be forty.
- At order forty with eight central elements, the
  [consolidated reduction and remaining-count table](1485_order_forty_eight_central_reduction.md)
  records the exact scope of the current results. In particular the
  [degree-five class has size at most ten](1485_order_forty_eight_central_high_five.md).
  This is an independently audited analytic theorem. Auxiliary support
  capacities, two central partitions, a mixed incidence moment, and
  weighted top-pair counts exclude class sizes eleven and twelve;
  no finite enumeration is required. The eight-central branch itself
  remains open.
  The [weighted top bound](1485_order_forty_eight_central_top_bound.md)
  and [central-row deficit argument](1485_order_forty_eight_central_nineteen_tops.md)
  now give **fifteen through eighteen tops**, excluding nineteen,
  twenty, and twenty-one entirely analytically.
  The new [fifteen-top exclusion](1485_order_forty_eight_central_fifteen_profile_bound.md#6-consequence-fifteen-tops-are-impossible-at-order-forty)
  improves the surviving interval to **sixteen through eighteen**.
  Its analytic reduction combines `a−q≤2` with sharp coverage;
  a standalone finite lemma gives `q≤4`. All 69 maximal-block
  families and 226,500 complete central tables were checked with
  two independent profile implementations in 893.285 seconds.
  The [universal profile bound](1485_order_forty_eight_central_six_three_profiles.md)
  gives **at most six degree-five three-profiles**, with no
  lower-bound assumption on the degree-five class size. A six-row
  potential and its impossible equality case prove this analytically.
  At the remaining boundary class size ten, the
  [pointwise profile inequality](1485_order_forty_eight_central_ten_five_profile_bound.md)
  and subsequent analytic exclusions leave only **sixteen tops
  with one or two three-profiles**. In particular the new
  [unused-top source count](1485_first_degree_source_unused_tops.md)
  excludes the last fifteen-top case. The equality exclusions use
  an impossible fixed-complement partition and a local slack count;
  they do not rely on optimizer infeasibility or SAT.
  The subsequent [three-profile exclusion](1485_order_forty_eight_central_three_three_profiles.md)
  is also entirely analytic: a small slack table reduces the last case
  to two central rectangles that necessarily overlap.
  If all degree-five profiles instead have size four, the
  [analytic all-four reduction](1485_order_forty_eight_central_all_four.md)
  originally left `(h,a,b)=(17,8,7),(17,9,6),(18,7,7),(18,8,6)`.
  The new exclusions below leave only the first and third splits.
  Only the third automatically has balanced degree-eight counts;
  the first retains both possible unbalanced types.
  Two further [analytic profile potentials](1485_order_forty_eight_central_profile_potentials.md)
  give `58h+8a+30q≤1168` for `a≥8,q>0`, and
  `118h+24a+34q≤2272` for `a≥9,q>0`. At seventeen tops
  they leave `q≤3` for `a=8` and `q≤1` for `a=9`; the last
  positive value for `a=9` is now also
  [excluded analytically](1485_order_forty_eight_central_seventeen_nine_one_small.md).
  The [all-four-profile argument](1485_order_forty_eight_central_seventeen_nine_all_four.md)
  now closes the last seventeen-top/nine-degree-five case too, entirely
  analytically: its final central patterns overfill a four-by-four
  quadrant or force overlapping weighted stars.
  With eighteen tops and eight degree-five elements,
  [two smaller profiles](1485_order_forty_eight_central_eighteen_two_small.md)
  and [one smaller profile](1485_order_forty_eight_central_eighteen_one_small.md)
  are now excluded. Their analytic reductions share **one 200-fixture
  central-incidence lemma**, independently rerun in 4.436 seconds with
  literal-set profile checks and ninety normalization controls. No SAT
  is used. The [all-size-four case is now excluded as well](1485_order_forty_eight_central_eighteen_all_four.md),
  using singleton saturation and a four-profile extension of the same
  200-fixture check, independently replayed in 7.241 seconds.
  At eighteen tops the
  [general small-profile bound](1485_order_forty_eight_central_eighteen_small_profile_bound.md)
  and [two-profile exclusion](1485_order_forty_eight_central_eighteen_two_small_exclusion.md)
  now prove **`q≤1` for every degree-five class size**. The only
  remaining eighteen-top triples are `(h,a,q)=(18,7,0),(18,7,1)`.
  The new [unified all-small exclusion](1485_order_forty_eight_central_all_small.md)
  proves `q<a` entirely analytically at sixteen through eighteen tops,
  removing three additional sixteen-/seventeen-top triples. The
  consolidated table now contains 33 necessary numerical triples in
  nine degree-class splits; these are not asserted constructions.
- At order 48 with four central vertices and degrees `4,6,8,12`,
  the [auxiliary-fiber and return-matching argument](1485_order_forty_eight_min_four.md)
  proves that the degree-six class has size **`10,…,14`**, excluding
  the previous possibilities fifteen, sixteen, seventeen, and eighteen.
  It uses exact fiber counts and ordinary graph degrees, with no
  SAT/ATP premise. Smaller class sizes remain under investigation.
  At size fourteen, the
  [seven/three sharp-degree branch](1485_order_forty_eight_seven_three.md)
  has a further analytic restriction: at least four of its seven
  sharp-degree-three vertices must attach to sharp-degree-one vertices,
  and the only possible attachment counts are now **four, five, or
  seven**. The other vertices form either one three-cycle, one
  two-cycle, or no internal high-sharp cycle. This is a partial
  restriction, not an exclusion of that class size. With five central
  vertices, [new fiber-packing restrictions](1485_order_forty_eight_five_central.md)
  constrain top-valued top products and auxiliary edge counts.
  The [two-double-block case](1485_order_forty_eight_five_central_d2.md)
  `N₂₂=2` is now excluded by an audited, explicit check of 984
  central tilings and their possible degree-six profiles (17.2 seconds
  locally, no SAT). The cases `N₂₂=0,1` and the overall order remain
  open; this result has a finite-check dependency, not a Lean proof.
  Within `N₂₂=1`, [constant top neighborhoods](1485_order_forty_eight_constant_top_profiles.md)
  give the analytic bound `9≤|A₆|≤14`. A common center for each
  family of double central blocks suffices for this extra hypothesis;
  it is not assumed for all five-central configurations.

## Minimum degree three: what has actually been excluded

The [central-defect gap](1485_boundary_central_defect.md) reduces a
non-full core to central counts three, four, or five.

| Configuration | Current result | Proof status |
| --- | --- | --- |
| Five central vertices, any order | Excluded by [binary-type and fiber arguments](1485_five_central_binary_blocks.md) | Analytic |
| Four central, eight top | [Excluded](1485_four_central_eight_top.md) | Analytic |
| Four central, ten top | [Excluded](1485_four_central_ten_top_exclusion.md) | Analytic |
| Four central, nine top, least degree four | [Excluded](1485_four_central_degree_four_exclusion.md) | Analytic reduction + explicit finite profile check |
| Four central, nine top, least degree five | [Excluded](1485_four_central_degree_five.md) | Analytic reduction + explicit finite profile check |
| Four central, nine top, least degree at least six | Excluded directly by the [first-output bound of five](1485_first_top_output_fibers.md) | Analytic |
| Three central, degree five absent | [Excluded](1485_three_central_requires_five.md) | Analytic |
| Three central, degree five present | [Excluded](1485_min_three_full_core.md#2-exclude-three-central-vertices) | Analytic arguments + three explicit finite profile checks |

The finite checks enumerate bounded central/top incidence data,
not all magma tables. They do not use an unverified SAT or ATP answer.
Their mathematics and code are documented together in the linked notes.

The last three-central branch had a nonempty degree-four class of
size at most six. Its [singleton case](1485_three_central_singleton_exclusion.md)
is excluded analytically; sizes two, three, and four are excluded by
finite profile checks. The new
[five-vertex proof](1485_three_central_five_four_exclusion.md)
forces two distinct sharp fibers to intersect twice, violating
unique goodness. The
[six-vertex proof](1485_three_central_six_four_exclusion.md)
forces the degree-five class to have at least four vertices and at
most three. Both final exclusions are analytic.

The older [few-degree theorem](1485_min_three_few_degrees.md) and
[multiple-of-sixty reduction](1485_min_three_spectrum_reduction.md)
are superseded by the unrestricted minimum-degree-three theorem.

## The completed full-core proof chain

1. [Canonical top rectangles](1485_canonical_triples.md) and
   [sharp regularity](1485_full_core_sharp_regularity.md) identify
   a canonical relation having `r` neighbors in each direction.
2. [Cyclic blocks](1485_full_core_cyclic_blocks.md) partition the
   carrier into blocks of size `r²`. Sharp adjacency moves them
   by a permutation.
3. [The Boolean quotient](1485_full_core_quotient.md) proves that
   multiplication respects these blocks. The quotient has a constant
   row and therefore power-of-two order. Thus `n=r²·2^j`.

This chain assumes full core, but no separate unproved congruence or
quotient hypothesis. The [period-ten theorem](1485_full_core_period_ten.md)
and [minimum-two kernel-mate theorem](1485_top_kernel_cycles.md)
are additional proved consequences, not assumptions of the quotient step.

## Precisely what a general proof still needs

For any central `h`, the `r²`-element rectangle

\[
\{u*v:u∈Row(h), v∈Col(h)\}
\]

contains all central vertices. The missing assertion is that all its
elements are central. Equivalently, prove any of the targets in the
[full-core equivalences](1485_full_core_equivalences.md): sharp
regularity, equality of the extreme degree-class sizes, symmetry of
central-valued products, or centrality of every top square.

The [central-parameter criterion](1485_central_parameter_components.md)
also makes full core equivalent to equality of all central auxiliary
relations. A connected central row/column-sharing graph suffices.
The finite mixed-coordinate rank formula is proved; equality of the
auxiliary relations in general is not.
The same note now gives an exact overlap Gram matrix for these auxiliary
relations, a pseudometric measuring their disagreement, and a necessary
membership-space condition. These are proved finite reductions, not a
resolution of the remaining rank or parameter-independence problem.

Existing unconditional restrictions include the
[boundary gap](1485_boundary_central_defect.md)
`r²−|Z|≥r+1` for non-full cores and the
[quantitative defect bounds](1485_second_central_defect_gap.md).
The new top-fiber bounds above add substantially stronger restrictions
on the degrees which can occur in such a core.

There are genuine limits to simpler approaches:

- The unrestricted rectangle assertion is
  [false for infinite models](1485_graph_research.md#why-rectangle-closure-cannot-be-proved-purely-equationally);
  finiteness is essential.
- [Central incidence equations alone](1485_central_incidence_obstruction.md)
  do not force full core.
- At minimum four with eight central vertices and all central blocks
  of size two, [both possible four-crown types](1485_min_four_eight_central_pair_crowns.md)
  extend to the documented central/top incidence conditions, even after
  the new return restrictions. A small explicit verifier checks these
  incomplete systems. They are **not magma models** and do not establish
  the existence of a degree-seven output; this is a limitation of those
  incidence conditions, not a spectrum result.
- [Joint-support](1485_pair_joint_support.md) remains conjectural,
  and the naive [ordinary-rank claim](1485_adjacency_rank_counterexample.md)
  is false.
- The [mixed-retraction obstructions](1485_mixed_retraction_bands.md)
  rule out several unrestricted image-intersection formulas, even with
  a parameter on a genuine translation cycle. The countable completions
  can also have sharp predecessors and successors everywhere. Thus
  sharp-neighbor existence alone cannot replace finite cardinality
  comparisons. The accompanying solver-free checker verifies the
  finite certificates; these are not finite countermodels to the
  spectrum conjecture.
- The [order-36 searches](1485_order36_countermodel_search.md) and
  [profile-obstruction search](1485_three_central_profile_obstruction_search.md)
  are not proofs of impossibility. No unverified solver refutation
  is a premise of the results listed as proved here.

## Other spectrum results and verification

Every square and twice-square order has a known construction.
Other completed consequences include:

- Constant-row models have power-of-two order; constant-degree models
  have square order.
- [Exactly two degrees](1485_two_degree_lower_bound.md) force
  `n=2r²`, without full core.
- An odd number of distinct degrees forces square order.
- [Four degrees under full core](1485_four_degree_regular_gap.md)
  force `n=8r²`.
- Orders [24](1485_order_twenty_four.md),
  [42](1485_order_forty_two.md), and [54](1485_order_fifty_four.md)
  are excluded. The latter two exclusions are analytic; the broader
  order-24 proof explicitly identifies its finite incidence step.
- [Sparse-divisor consequences](1485_sparse_divisor_spectrum.md)
  and the [square-root gap](1485_first_top_output_divisor_gap.md)
  classify prime-power orders through exponent seven and exclude
  several infinite families involving two primes, including `p³q`
  for primes `q>p³` (hence `8q` for every prime `q≥11`). The first remaining
  odd prime-power exponent is nine, not an asserted possible order.

The formula regressions in `scripts/1485_structure_check.py` passed
394 available finite tables after adding the common-block bound,
the bounded-central-excess bounds, weighted top-fiber balance, and
the unconditional good-return fiber matching with its independent-set
bound and actual inverse maps. They also passed after adding both
central-assisted return identities and their unique ordinary middles.
The built-in tests
include an order-32 model whose squaring
has order-five twist, and rectangle models of orders nine and eighteen.
All these examples have full cores: their success is a sanity check,
not a test of existence or impossibility in the remaining non-full branch.

The continuation beginning **23:09:38 UTC on 19 September 2026**
completed the thirteen/seven order-40 exclusion and the analytic
two-extra-central-vertex theorem. Independent proof audits checked the
singleton-label, containment, two-label, and boundary-overlap arguments.
The latest complete research-checker timings were **29.2 seconds** for
the two-high-sharp case, **140.6 seconds** for the one-high-sharp case,
and **2.5 seconds** for the low-sharp incidence/support check. These
are Python run times, not Lean elaboration times. The eight-central-vertex
incidence examples were also rerun, including 6,656 determined W and
6,656 determined dual instances per example. No new Lean formalization
or git publication was part of this continuation.

The continuation beginning **02:47:08 UTC on 20 September 2026**
proved the general joint outside-fiber inequality and analytic bound
of `2r−6` common singleton labels, the analytic three-overlap exclusion
at seven central vertices, and the finite-assisted two- and one-overlap
exclusions. Independent audits checked the normalization,
analytic arguments, and exact-cover search. The four two-overlap cases
reran in **31.3, 31.1, 31.3, and 23.0 seconds**; the last case's twenty
raw covers all fail outside-label multiplicity. Positive and negative
controls also checked its selected-rectangle recorder. The separate
three-overlap search was rerun without line-count pruning (65,522 and
124,141 states, no covers), although its result is no longer a proof
dependency. These are Python timings, not Lean elaboration timings.
The three one-overlap cases independently reran in **24.3, 29.6, and
26.6 seconds**, visiting 455,715, 698,286, and 634,463 states. The first
100 crown-witness calls in each case were also compared with a direct
reference generator. Additional analytic results exclude the two-high
sharp-degree pattern in the twelve/eight order-40 branch and forbid
one-vertex differences between top profiles at first output degree `r+1`.
The single-singleton-label cases reran independently in **15.7, 27.5,
and 20.0 seconds**. The `(3,3)` profile cases reran in **3.1, 12.6,
14.5, and 13.9 seconds**, with all 9,292 raw covers rejected by
forward crowns; the dual checks were also present. Both programs used
100 fast/direct witness audits per nonempty case. The order-40 unique
high-sharp loop subcase separately reran in **11.3 seconds** using its
standalone C++17 checker (56 permutation classes, 738 degree-compatible
matrices, 720 edge-balanced matrices, no closure survivors).
The two `(3,1)` profile checks independently reran in **44.9 and
25.3 seconds**, with 100 partial witness audits in each and 100 complete
witness audits in the case with completed covers.
The final `(3,2)` check independently reran all eleven cases, with
100 fast/direct partial-witness comparisons per case, in **110.1, 45.0,
215.8, 243.3, 96.3, 12.4, 28.4, 57.1, 9.5, 20.8, and 19.0 seconds**.
Uniform analytic singleton separation subsequently removed the overlap
checks from the shortest seven-central proof, leaving three finite lemmas.
The order-40 A10 and A11 exclusions and the A12 one-high and thin-line
exclusions have explicit archived LRAT proofs. A11's complete 37-proof
archive independently replayed against regenerated CNFs in **38.4 seconds**.
The two A12 one-high archives and regenerated CNFs matched every recorded
hash; the medium/low proofs independently verified in **1.18/1.51 seconds**.
All five A12 mixed-coset archives were also independently replayed against
freshly regenerated, hash-identical CNFs. The final balanced-incidence
check reran in **9.74 seconds** with every stage count reproduced.
Its alternative regular-hole proof used **3.29 seconds** for generation,
**15.08 seconds** for proof production, and **1.25 seconds** for independent
LRAT verification; replaying the retained archive against a fresh CNF
verified again in **1.28 seconds**, with both hashes matched.
All six joint-capacity archives were independently replayed against
regenerated CNFs, with every hash checked, in **47.14 seconds**.
The general full-core conjecture remains open.

The continuation beginning **13:27:36 UTC on 20 September 2026**
worked past **15:38 UTC**, completing the nine-central order-forty
exclusion and the further eight-central reductions above. The new
nine-central final checks independently replayed in **2.264** and
**8.043 seconds**; the complete nine-central proof still depends on
five previously retained LRAT proofs in its earlier reduction.

For eight central elements, the fifteen-top obstruction exhausted
**69 normalized maximal-block families, 32,567,237 search nodes,
and 226,500 complete central tables**. Its full target-five replay
passed in **893.285 seconds**, with independent literal-set profile
and compatibility checks on every table. The earlier, weaker
target-six replay passed in **876.868 seconds**. The common
eighteen-top central generator was also replayed: its three-profile
check passed in **4.283 seconds**, and its four-profile extension
passed in **7.141 seconds**. No new SAT premise was needed for
these eight-central results.

Independent mathematical audits checked the singleton saturation,
general unused-top identities (including arbitrary first-output gaps),
one-hole bounds, all-small-profile exclusion, the seventeen-top
weighted-star and quadrant arguments, and the eighteen-top repeated
retained-block argument. The remaining eight-central numerical table
was independently recounted: **33 triples in nine class-size splits**.
Targeted formatting checks and all 221 local links in sixteen principal
notes passed. No new Lean formalization or git publication was part of
this continuation. The full square-or-double-square theorem, and order
forty itself, remain open.
