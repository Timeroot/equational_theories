# FO-structural equivalence priorities

Date: 2026-09-21. All arrows are source → target.

A gap is a pair of distinct proved equivalence classes with neither direction refuted. These are equivalence questions, not the much larger collection of individual open arrows.

| Carriers | Proved classes | Unresolved class pairs | Both directions open | Raw unordered equation pairs |
|---|---:|---:|---:|---:|
| Arbitrary | 737 | 1094 | 777 | 12822 |
| Finite | 712 | 1049 | 735 | 12490 |

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
| 1 | 4470 | 66 | 3 |
| 3471 | 108 | 0 | 66 |
| 1256 | 108 | 0 | 60 |

## Arbitrary carriers: balanced targets

| Source | Target | Pairs settled if positive | Pairs settled if negative | Classes merged if positive |
|---:|---:|---:|---:|---|
| 3253 | 326 | 10 | 6 | 8, 326, 3253, 3319, 3522 |
| 8 | 3 | 6 | 9 | 3, 8, 326, 3715 |
| 3253 | 8 | 6 | 8 | 8, 3253, 3319, 3522 |
| 3522 | 3715 | 6 | 8 | 8, 326, 3522, 3715 |
| 11 | 109 | 6 | 7 | 11, 109, 844, 1256 |
| 3319 | 3715 | 6 | 6 | 8, 326, 3319, 3715 |
| 3456 | 326 | 6 | 6 | 8, 326, 3456, 3522 |
| 1 | 3522 | 6 | 5 | 1, 3253, 3456, 3522 |
| 3662 | 11 | 6 | 5 | 11, 3662, 3663, 3729 |
| 1 | 8 | 36 | 4 | 1, 8, 411, 1020, 1629, 3253, 3319, 3456, 3522 |
| 3253 | 3715 | 15 | 4 | 8, 326, 3253, 3319, 3522, 3715 |
| 3456 | 3715 | 10 | 4 | 8, 326, 3456, 3522, 3715 |

## Arbitrary carriers: large conditional gains

| Source | Target | Pairs settled if positive | Pairs settled if negative |
|---:|---:|---:|---:|
| 1 | 3 | 253 | 1 |
| 1 | 3715 | 136 | 2 |
| 3471 | 108 | 0 | 60 |
| 1256 | 108 | 0 | 54 |
| 844 | 108 | 0 | 48 |
| 844 | 1252 | 0 | 48 |

## Validation

The full positive and negative matrices were rebuilt from the audited sources. Weighted class-pair totals agree with an independent count over every raw unordered equation pair. The first twelve balanced candidates in each variant were independently checked by full Boolean matrix propagation on the quotient.

Source SHA-256: `d71384ba900d1638ae4407e1d42530cef1a0e570aa5ab73d4826e2475e920bf7`.

[Complete pairs, memberships, and candidate impacts](../data/definability_structural_equivalence_gaps.json).

Regenerate with `OPENBLAS_NUM_THREADS=2 python3 scripts/definability_structural_equivalence_gaps.py --write`.
