# FO-structural equivalence priorities

Date: 2026-10-14. All arrows are source → target.

A gap is a pair of distinct proved equivalence classes with neither direction refuted. These are equivalence questions, not the much larger collection of individual open arrows.

| Carriers | Proved classes | Unresolved class pairs | Both directions open | Raw unordered equation pairs |
|---|---:|---:|---:|---:|
| Arbitrary | 735 | 604 | 438 | 9736 |
| Finite | 711 | 1047 | 722 | 12482 |

The [one-exceptional-row counting proofs](definability_single_defect_counting.md) separate all nine unrestricted pairs between source classes {E1020, E1629, E3456} and target classes {E8, E47, E3319}. Their finite FO-structural versions remain open.

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
| 4274 | 4481 | 3 | 4 | 4274, 4387, 4481 |
| 3683 | 4387 | 3 | 2 | 3683, 4274, 4387 |
| 4295 | 4387 | 3 | 2 | 4274, 4295, 4387 |
| 4303 | 4387 | 3 | 2 | 4274, 4303, 4387 |
| 4470 | 3715 | 2 | 2 | 3715, 4470 |
| 3522 | 3319 | 2 | 2 | none |
| 3283 | 317 | 6 | 1 | 317, 3270, 3280, 3283 |
| 3683 | 4481 | 6 | 1 | 3683, 4274, 4387, 4481 |
| 4295 | 4481 | 6 | 1 | 4274, 4295, 4387, 4481 |
| 4303 | 4481 | 6 | 1 | 4274, 4303, 4387, 4481 |
| 4411 | 4526 | 6 | 1 | 4407, 4411, 4526, 4535 |
| 73 | 125 | 3 | 1 | 73, 125, 1692 |

## Arbitrary carriers: large conditional gains

| Source | Target | Pairs settled if positive | Pairs settled if negative |
|---:|---:|---:|---:|
| 10 | 3467 | 0 | 22 |
| 319 | 4392 | 0 | 18 |
| 4410 | 3283 | 0 | 16 |
| 4410 | 3285 | 0 | 16 |
| 3280 | 4277 | 0 | 15 |
| 4417 | 3488 | 0 | 15 |

## Validation

The full positive and negative matrices were rebuilt from the audited sources. Weighted class-pair totals agree with an independent count over every raw unordered equation pair. The first twelve balanced candidates in each variant were independently checked by full Boolean matrix propagation on the quotient.

Source SHA-256: `6925e970dc3381142f659afb54fb2f7a3c2ff0e609e80f4e43c32899f4119c62`.

[Complete pairs, memberships, and candidate impacts](../data/definability_structural_equivalence_gaps.json).

Regenerate with `OPENBLAS_NUM_THREADS=2 python3 scripts/definability_structural_equivalence_gaps.py --write`.
