# Order forty, twelve/eight: mixed successor cosets are impossible

Research note, 20 September 2026. **Completed finite-assisted theorem:**
in the remaining sharp-degree distribution `(2^4,1^4)` of the order-forty
twelve/eight branch, both degree-five profile families belong to single
Klein-four cosets. The proof uses analytic profile restrictions and five
explicit, independently checked LRAT refutations. It is not yet in Lean.
This theorem does not exclude the remaining single-coset configurations
or prove the full E1485 spectrum conjecture.

Let `Z,A,B,T` have degrees `4,5,8,10` and sizes `4,12,8,16`.
By the [large-class theorem](1485_min_four_large_five_class.md), after
taking the opposite operation if necessary, all predecessor profiles
`U_a`, `a∈A`, are lines in one four-line coset `P`. Each predecessor
line has all its successor partners in one other coset. Call these
possible successor cosets `Q,R`.

The [empty-line argument](1485_order_forty_twelve_no_high_profiles.md#5-no-predecessor-line-can-be-empty)
and [checked thin-line exclusion](1485_order_forty_twelve_thin_exclusion.md)
reduce the predecessor multiplicities to `(4,4,2,2)`, `(4,3,3,2)`,
and `(3,3,3,3)`. Suppose both `Q,R` occur. Write `M,L⊆B` for
the four sharp-degree-two and four sharp-degree-one vertices.

## 1. The nonexceptional mixed cases force exactly two non-affine profiles

The analytic proofs in
[Sections 9 and 11 of the profile note](1485_order_forty_twelve_no_high_profiles.md#9-mixed-balanced-profiles-force-an-exact-affinenon-affine-split)
give the following dichotomy for every mixed case except a successor
population split `10+2`:

- Exactly two medium predecessor profiles `U_b` are central-successor
  columns. Their intersection rows with the four `P` lines are
  `(1,1,1,1)`, and both their internal successors lie in `M`.
- The other two are non-affine. Their intersection rows are permutations
  of `(2,1,1,0)` or `(3,1,0,0)`, and both their internal predecessors
  lie in `M`.

The proof counts at least eight exact-one incidences for each medium
profile. A non-affine profile can have at most eight, forcing two
medium predecessor fibers. An affine profile cannot fail a populated
coset unless that coset consists of the sole multiplicity-two row;
the full-line capacity argument handles the additional four-four-two-two
possibility. Thus nonexceptional affine profiles are central columns.
At least three internal edges cross between `L` and `M` in each
direction, allowing at most two profiles of each kind. The XOR of the
four line labels distinguishes the affine and non-affine row shapes
without assuming any additional coordinate normalization.

The [split encoder](../scripts/1485_n40_twelve_mixed_split_cnf.py)
adds precisely these conditions to the necessary incidence and exact
line-capacity equations from the thin-line proof. Labeling the two
central-column vertices `0,1` and the non-affine ones `2,3` is permitted
because all four have the same sharp degree. No further graph symmetry
or multiplication-table assumption is imposed. Each of the three
resulting CNFs has an independently checked LRAT refutation.

## 2. The exceptional ten-plus-two cases have a different trichotomy

The exception can occur only for predecessor multiplicities `(4,3,3,2)`
or `(4,4,2,2)`. Normalize the minority predecessor line to index `3`,
and let `I` be the two distinct sharp `F`-images of its two vertices.
The full proof in
[Section 10 of the profile note](1485_order_forty_twelve_no_high_profiles.md#10-the-mixed-ten-plus-two-exception-has-a-profile-trichotomy)
gives three possibilities for each medium intersection row:

| Row type, up to permutation | Additional necessary condition |
|---|---|
| `(1,1,1,1)` | Already handled by the baseline return equations |
| `(2,2,0,0)` | Its two internal predecessors are exactly `I` |
| `(2,1,1,0)` or `(3,1,0,0)` | Two medium predecessors; their whole `F`-fibers contain exactly `u_p−2` vertices on each line `p` |

For the middle row type the profile is affine, transversal to the
ten-vertex majority coset but not the minority coset. Both minority
vertices therefore require their sharp `F`-images as predecessors.
For the last row types the profile is non-affine; the bound of eight
exact-one incidences is attained separately on every predecessor line,
giving the stated exact fiber counts.

The [ten-plus-two encoder](../scripts/1485_n40_twelve_mixed_ten_two_cnf.py)
applies these conditions with Boolean guards for each medium row's
actual type. A row has respectively zero, two, or one entries at least
two in the three alternatives. Every row is classified; no unproved
global affineness assumption is used. Both resulting CNFs also have
independently checked LRAT refutations.

## 3. Certification and conclusion

The complete source encoders and mathematical reductions were audited
independently. The primary variables of any putative magma satisfy the
necessary conditions, and the exact Boolean gate definitions extend
them to a satisfying assignment. A checked UNSAT certificate therefore
excludes that case.

| Case | Variables | Clauses | Generation | Refutation | Independent check |
|---|---:|---:|---:|---:|---:|
| Nonexceptional `(3,3,3,3)` | 14,395 | 52,755 | 1.06 s | 1.79 s | 0.34 s |
| Nonexceptional `(4,3,3,2)` | 14,361 | 52,653 | 1.16 s | 2.12 s | 0.80 s |
| Nonexceptional `(4,4,2,2)` | 14,327 | 52,551 | 1.64 s | 2.64 s | 0.10 s |
| Ten-plus-two `(4,3,3,2)` | 14,565 | 53,305 | 0.71 s | 35.38 s | 1.00 s |
| Ten-plus-two `(4,4,2,2)` | 14,523 | 53,175 | 0.72 s | 12.31 s | 0.44 s |

Timings are wall-clock measurements under concurrent load, not Lean
elaboration times. CaDiCaL 2.1.2 produced the text LRAT files; the
independent `lrat-check` verified their derivations through the final
empty clause. The
[retained certificate inventory](../data/1485_certificates/A12_MIXED.md)
records all five archives, exact hashes, checker provenance, and
solver-free replay commands. No unpublished SAT result is a premise.

Every mixed-coset possibility lies in exactly one of the five checked
cases. This contradicts the assumption that both `Q,R` occur.
Consequently the successor profiles also belong to a single coset,
which is distinct from `P`. Thus the entire twelve/eight branch has
been reduced to the single-coset setting, after the previously stated
sharp-distribution and thin-line exclusions.
