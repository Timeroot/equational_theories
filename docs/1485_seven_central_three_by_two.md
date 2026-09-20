# The remaining `(3,2)` central top profiles at `r=4,m=p=7`

Research note, 20 September 2026. This is a completed solver-free finite
incidence exclusion. All eleven packaged cases have also been rerun
successfully with 100 direct witness comparisons each. This is not a
Lean formalization.

**Theorem.** At minimum degree four and central count seven, the least
noncentral top-product degree cannot be seven. In a non-full core it
is therefore five or six, by the existing first-output divisor bound.

## Dependencies and noncircular order

Assume minimum degree four, seven central labels, and least noncentral
top-product degree seven. First use the analytic
[size-four block exclusion](1485_full_central_blocks_boundary_output.md),
then [uniform singleton-label separation](1485_boundary_output_singleton_separation.md).
The older common-label overlap checks are no longer needed.

The [three-by-three exclusion](1485_seven_central_three_by_three.md)
then rules out profile `(3,3)`. The
[three-by-one exclusion](1485_seven_central_three_by_one.md), which
allows arbitrary `(3,2)` and `(2,3)` profiles, rules out `(3,1)`;
its dual rules out `(1,3)`. Thus every size-three block has an
opposite block of size two. There is no dependency on the present
`(3,2)` check in any of those exclusions.

If all central blocks had size at most two, the analytic
[small-block theorem](1485_small_central_blocks_first_output_gap.md)
would already exclude degree seven. Consequently, after duality,
it suffices to exclude a distinguished top `v` with `(P_v,C_v)=(A,B)`
of sizes `(3,2)`.

The check is

```sh
python3 -Werror scripts/1485_m7_three_by_two_check.py --audit-witnesses 100
```

One can select an individual case with `--case 1` through `--case 11`.
There is no search timeout and no external solver.

## Complete two-partition normalization

Choose a central column containing `v`. Its predecessor partition is
necessarily of shape `3+2+1+1`, and may be relabeled as

`A={0,1,2}, D={3,4}, {5}, {6}`.

Thus `5,6` are actual singleton-predecessor labels. Choose also any
central row containing `v`; its successor partition consists of `B`
and three residual blocks partitioning `Z\B`. It has shape `2+2+2+1`
or `2+3+1+1`.

Every successor block meets `A,D` in at most one point. Under permutations
within `A`, within `D`, and within `{5,6}`, the distinguished pair `B`
has four possibilities: one point of `A` and one of `D`; one of `A`
and one of `{5,6}`; one of `D` and one of `{5,6}`; or both points
`5,6`. Normalize these to `B={0,3},{0,5},{3,5},{5,6}`.

Each residual successor block also meets `A,D` at most once, and a
singleton residual block cannot have label `5` or `6`, by singleton
separation. Modulo the subgroup preserving `B`, exactly eleven cases
remain:

| Case | `B` | Other three successor blocks |
|---|---|---|
| 1 | `{0,3}` | `{1}`, `{2}`, `{4,5,6}` |
| 2 | `{0,3}` | `{1}`, `{4}`, `{2,5,6}` |
| 3 | `{0,3}` | `{1}`, `{2,4}`, `{5,6}` |
| 4 | `{0,3}` | `{1}`, `{2,5}`, `{4,6}` |
| 5 | `{0,3}` | `{4}`, `{1,5}`, `{2,6}` |
| 6 | `{0,5}` | `{1}`, `{3}`, `{2,4,6}` |
| 7 | `{0,5}` | `{1}`, `{2,3}`, `{4,6}` |
| 8 | `{0,5}` | `{3}`, `{1,4}`, `{2,6}` |
| 9 | `{3,5}` | `{0}`, `{1}`, `{2,4,6}` |
| 10 | `{3,5}` | `{0}`, `{1,4}`, `{2,6}` |
| 11 | `{5,6}` | `{0}`, `{1,3}`, `{2,4}` |

The program independently verifies this list: it enumerates every
three-element collection of nonempty subsets of sizes at most three,
keeps exactly the allowed partitions of `Z\B`, and chooses the least
image under all 24 permutations preserving the first predecessor
partition and then the subgroup preserving `B`. It asserts equality
with the displayed list. Choosing an unordered collection loses no
information because the three residual blocks are not distinguished.

Let `T` be the one or two singleton-successor labels in the chosen
partition. These labels really occur in any putative magma belonging
to the case, as do singleton-predecessor labels `5,6`.

## Necessary central incidence search

Generate every nonempty pair `(P,C)` of subsets of seven labels with
block sizes at most three, excluding profiles `(3,3),(3,1),(1,3)`.
Require self-orthogonality, orthogonality to every block of the two
chosen partitions, and compatibility with the required rectangle
`A×B`. Singleton `P` blocks avoid `T`; singleton `C` blocks avoid
`5,6`; diagonal singleton rectangles are forbidden.

For distinct candidates require disjoint central rectangles, global
predecessor/successor orthogonality, and disjointness of all actual
singleton labels. Also use the exact
[boundary containment restriction](1485_boundary_singleton_overlap.md):
if `Q⊆P`, `Q∩T≠∅`, and `|C|≥2`, then `(P,C)` cannot
coexist with `(Q,F)` when `|F|≥2` or `|C|≥3`; use its dual
with the known singleton-predecessor labels `5,6` as well. No label
merely permitted to be singleton is treated as known to occur.

Search exact covers of all 49 central cells, with exactly four
rectangles through each central row and column. The only specifically
required rectangle is `A×B`. As in the three-by-three check, the search
uses the necessary constraints from the other chosen partition blocks
without requiring their actual occurrence or fixing the chosen central
row/column labels. This enlarges the search and is safe for exclusion.

## Partial-crown lookahead

The exact-cover recursion and crown witness enumerator are the already
audited implementations reused by the earlier checks. The new pruning
step is the following necessary test on a partial selection of rectangles.

If a selected singleton-successor source `u` has `C_u={c}` and four
tops of `Row(c)` are already selected, choose the first selected
singleton-successor omission `d` on that row. Such an omission exists:
four disjoint nonempty subsets of seven labels cannot all have size
at least two. Any genuine completion must supply its exact-replacement
crown. Every vertex of that crown must be either an already selected
top or one of the currently active candidate rectangles. The witness
enumerator exhausts all such possibilities, so the branch is rejected
if none exists. The dual condition is checked as well.

If the four selected row tops do not cover every central cell on that
row, the branch cannot complete in any event: all further rectangles
through that row have been removed by the exact-cover line-count rule.
Thus performing this same lookahead before the usual line-hole rejection
cannot discard an actual completion.

The lookahead **does not commit to a witness** and does not require
witnesses for different omissions to be mutually consistent. In the
dual witness search some additional static containment restrictions
between future witness vertices are also relaxed. Each relaxation
only permits more candidates, and a failure still excludes completion.
The only required omission at this partial stage is the chosen first
one, whose existence is guaranteed by exact replacement. If a complete
incidence cover is reached, the inherited all-crown checker checks
every singleton omission in both orientations.

A crown row/column vertex may coincide; the witness implementation
permits this. Distinct row vertices themselves and distinct column
vertices are enforced by the incidence pattern and the predecessor
partition, as in the earlier audited enumerator. The selected-rectangle
state is restored on return from each recursive branch.

The finite object being searched is only a necessary **central rectangle
system**, not a magma. No unverified SAT or ATP result is a premise.

## Controls and audit status

The program checks the full eleven-case orbit inventory and the existing
positive central-incidence and positive/negative crown controls. An
additional partial-state control selects only a singleton source and
its four central-row tops: there is exactly one crown using active
candidates, and removing its unique replacement destroys every witness.
Both the fast and direct enumerators check these assertions.

For the first 100 partial-witness calls in each case, the program compares
the complete set returned by the fast bitset method against the slower
direct set-intersection implementation. All eleven packaged reruns passed.

## Exhaustive inventory and conclusion

Every one of the eleven cases has been exhausted and rejected. No
complete incidence cover survives partial-crown lookahead.

| Case | Candidate rectangles | Search states | Surviving complete incidence covers | Audited run (seconds) |
|---|---:|---:|---:|---:|
| 1 | 532 | 2,408,063 | 0 | 116.095 |
| 2 | 586 | 929,577 | 0 | 49.049 |
| 3 | 646 | 4,435,991 | 0 | 307.965 |
| 4 | 644 | 4,174,707 | 0 | 214.418 |
| 5 | 707 | 1,831,387 | 0 | 111.421 |
| 6 | 525 | 248,433 | 0 | 17.787 |
| 7 | 578 | 557,522 | 0 | 35.259 |
| 8 | 632 | 923,880 | 0 | 67.474 |
| 9 | 459 | 186,964 | 0 | 15.146 |
| 10 | 539 | 435,062 | 0 | 33.436 |
| 11 | 495 | 392,215 | 0 | 22.917 |

The total is 16,523,801 search states. The checker asserts this inventory
case by case; the direct-witness audit does not change the search tree.
The displayed timings include all 100 direct witness comparisons per
case and were obtained while other research processes were running;
they should not be treated as isolated-machine benchmarks.

As an independent check of the lookahead's effect, exploratory searches
without partial-crown pruning exhausted cases 1, 9, 10, and 11. They
produced respectively 6,300, 578, 83,981, and 665,108 complete necessary
incidence covers, every one rejected by the full-cover crown tests.
Those exploratory runs are corroboration, not additional dependencies
of the packaged exclusion.

Thus `(3,2)` is impossible after the preceding `(3,3)` and `(3,1)`
exclusions. Duality also excludes `(2,3)`, leaving every block of size
at most two. The analytic small-block first-output theorem then excludes
degree seven entirely at central count seven.

The shortest finite-assisted proof uses **three finite lemmas**:
the `(3,3)`, `(3,1)`, and `(3,2)` profile exclusions. Singleton-label
separation and the global block-size bound are analytic. The earlier
two- and one-common-label checks, and the separate
[one-singleton-label exclusion](1485_seven_central_one_singleton_label.md)
are valid independent corroboration, but are **not needed** in this
dependency chain: the `(3,1)` and `(3,2)` searches do not assume that
both singleton-label sets have size at least two.
