# FO-structural equivalence priorities

Date: 2026-09-21. All arrows are source → target.

A gap is a pair of distinct proved equivalence classes with neither direction refuted. These are equivalence questions, not the much larger collection of individual open arrows.

| Carriers | Proved classes | Unresolved class pairs | Both directions open | Raw unordered equation pairs |
|---|---:|---:|---:|---:|
| Arbitrary | 737 | 1001 | 743 | 12416 |
| Finite | 712 | 1049 | 734 | 12490 |

The tables below rank open arrows by the smaller of their positive and negative impacts. Thus a leading target is useful whichever way it resolves. Counts refer to old unresolved class pairs in the indicated variant; they are conditional propagation counts, not predictions of which outcome holds. Counts for different targets overlap.

## Finite carriers: balanced targets

| Source | Target | Pairs settled if positive | Pairs settled if negative | Classes merged if positive |
|---:|---:|---:|---:|---|
| 8 | 3 | 10 | 9 | 3, 8, 326, 3715, 4470 |
| 3522 | 3715 | 10 | 8 | 8, 326, 3522, 3715, 4470 |
| 3253 | 326 | 10 | 6 | 8, 326, 3253, 3319, 3522 |
| 3253 | 4470 | 10 | 6 | 8, 3253, 3319, 3522, 4470 |
| 3319 | 3715 | 10 | 6 | 8, 326, 3319, 3715, 4470 |
| 8 | 3715 | 6 | 18 | 8, 326, 3715, 4470 |
| 3253 | 8 | 6 | 10 | 8, 3253, 3319, 3522 |
| 11 | 109 | 6 | 8 | 11, 109, 844, 1256 |
| 1 | 3522 | 6 | 6 | 1, 3253, 3456, 3522 |
| 3456 | 326 | 6 | 6 | 8, 326, 3456, 3522 |
| 3456 | 4470 | 6 | 6 | 8, 3456, 3522, 4470 |
| 1 | 8 | 36 | 5 | 1, 8, 411, 1020, 1629, 3253, 3319, 3456, 3522 |

## Finite carriers: large conditional gains

| Source | Target | Pairs settled if positive | Pairs settled if negative |
|---:|---:|---:|---:|
| 1 | 3 | 253 | 1 |
| 1 | 3715 | 171 | 2 |
| 1 | 326 | 78 | 3 |
| 1256 | 108 | 0 | 70 |
| 1 | 4470 | 66 | 3 |
| 844 | 108 | 0 | 63 |

## Arbitrary carriers: balanced targets

| Source | Target | Pairs settled if positive | Pairs settled if negative | Classes merged if positive |
|---:|---:|---:|---:|---|
| 11 | 3471 | 5 | 7 | 11, 3471 |
| 3662 | 11 | 6 | 4 | 11, 3662, 3663, 3729 |
| 1255 | 109 | 8 | 4 | 109, 1255 |
| 8 | 99 | 4 | 8 | none |
| 8 | 614 | 4 | 8 | none |
| 8 | 817 | 4 | 8 | none |
| 8 | 1223 | 4 | 8 | none |
| 8 | 1426 | 4 | 8 | none |
| 8 | 3722 | 4 | 8 | none |
| 8 | 4380 | 4 | 8 | none |
| 11 | 1255 | 4 | 7 | none |
| 99 | 3319 | 4 | 5 | none |

## Arbitrary carriers: large conditional gains

| Source | Target | Pairs settled if positive | Pairs settled if negative |
|---:|---:|---:|---:|
| 1256 | 108 | 0 | 56 |
| 108 | 109 | 52 | 1 |
| 844 | 108 | 0 | 49 |
| 1252 | 109 | 45 | 1 |
| 11 | 108 | 1 | 42 |
| 4484 | 40 | 0 | 42 |

## Validation

The full positive and negative matrices were rebuilt from the audited sources. Weighted class-pair totals agree with an independent count over every raw unordered equation pair. The first twelve balanced candidates in each variant were independently checked by full Boolean matrix propagation on the quotient.

Source SHA-256: `a422c65b6e784b35bc789a2861a8aaa3e78b0684ecf1d2a622ec6bc448f107a1`.

[Complete pairs, memberships, and candidate impacts](../data/definability_structural_equivalence_gaps.json).

Regenerate with `OPENBLAS_NUM_THREADS=2 python3 scripts/definability_structural_equivalence_gaps.py --write`.
