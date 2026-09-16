# Open-cell totals

[Audit and interpretation](../definability_open_audit.md).

**Completely open in all eight definability variants: [68 raw pairs / 18 class pairs](completely_open.md).**

Snapshot: 2026-09-16. Source SHA-256: `e03ff2c067693bdf3b7f5421d4b33dad88a3bae5f52fcdbe15c643ba82680243`.

All counts exclude diagonal pairs. Each full grid has 22,028,942 directed pairs.

| Relation / carriers | Classes | Positive | Negative | Raw open | Reduced open |
|---|---:|---:|---:|---:|---:|
| [implies/all](implies_all.md) | 1,415 | 8,173,585 | 13,855,357 | 0 | 0 |
| [implies/fin](implies_fin.md) | 1,370 | 8,174,405 | 13,854,535 | 2 | 2 |
| [termStructural/all](termStructural_all.md) | 739 | 8,561,335 | 13,442,080 | 25,527 | 5,211 |
| [termStructural/fin](termStructural_fin.md) | 716 | 8,563,515 | 13,441,940 | 23,487 | 4,698 |
| [structural/all](structural_all.md) | 737 | 9,030,147 | 12,554,243 | 444,552 | 60,586 |
| [structural/fin](structural_fin.md) | 712 | 9,066,155 | 12,553,985 | 408,802 | 53,983 |
| [termDefinable/all](termDefinable_all.md) | 112 | 14,382,905 | 7,644,711 | 1,326 | 273 |
| [termDefinable/fin](termDefinable_fin.md) | 91 | 14,383,835 | 7,642,797 | 2,310 | 232 |
| [definable/all](definable_all.md) | 108 | 14,397,807 | 7,627,141 | 3,994 | 662 |
| [definable/fin](definable_fin.md) | 88 | 14,400,810 | 7,624,609 | 3,523 | 332 |

## Arbitrary versus finite carriers

These are **raw pairs with the same equation numbers**, not comparisons between
different quotients. `P` = proved, `N` = refuted, `O` = open in the extracted board.

| Relation | all O / fin O | all O / fin P | all N / fin O | all N / fin P |
|---|---:|---:|---:|---:|
| implies | 0 | 0 | 2 | 820 |
| termStructural | 23,347 | 2,180 | 140 | 0 |
| structural | 408,544 | 36,008 | 258 | 0 |
| termDefinable | 940 | 386 | 1,370 | 544 |
| definable | 3,523 | 471 | 0 | 2,532 |

`all N / fin P` is a **settled** distinction, not an open question.
The JSON also records P/P and N/N. P/O, P/N and O/N must be zero.

## Historical shortlist rechecked

Every one of the 35 cells in the historical report §3.5, in its original relation.
The full profile uses `I, TS, S, TD, D`, with `all` then `fin` within each pair.

| Relation originally open | Source → target | Current status | I · TS · S · TD · D |
|---|---|---|---|
| termStructural/all | 63 → 125 | OPEN | NN · OP · OP · OP · OP |
| termStructural/all | 63 → 3548 | OPEN | NN · OP · OP · OP · OP |
| termStructural/all | 124 → 1648 | OPEN | NN · OP · OP · PP · PP |
| termStructural/all | 124 → 3343 | OPEN | NN · OP · OP · PP · PP |
| termStructural/all | 124 → 4130 | OPEN | NN · OP · OP · PP · PP |
| termStructural/all | 125 → 3548 | OPEN | NN · OP · OP · PP · PP |
| termStructural/all | 125 → 3954 | OPEN | NN · OP · OP · PP · PP |
| termStructural/all | 206 → 1648 | OPEN | NP · OP · OP · PP · PP |
| termStructural/all | 206 → 3343 | OPEN | NN · OP · OP · PP · PP |
| termStructural/all | 222 → 3548 | OPEN | NN · OP · OP · PP · PP |
| termStructural/all | 271 → 3548 | OPEN | NN · OP · OP · OP · OP |
| termStructural/all | 1648 → 124 | OPEN | NN · OP · OP · PP · PP |
| termStructural/all | 1648 → 206 | OPEN | NP · OP · OP · PP · PP |
| termStructural/all | 1648 → 3343 | OPEN | NN · OP · OP · PP · PP |
| termStructural/all | 1648 → 4130 | OPEN | NN · OP · OP · PP · PP |
| termStructural/all | 56 → 50 | OPEN | NN · OO · PP · PP · PP |
| termStructural/all | 167 → 117 | REFUTED | NN · NN · OO · PP · PP |
| termStructural/all | 440 → 414 | OPEN | NN · OO · PP · PP · PP |
| termStructural/all | 467 → 437 | OPEN | NN · OP · OP · PP · PP |
| termStructural/all | 473 → 429 | OPEN | NN · OP · OP · PP · PP |
| termStructural/all | 477 → 417 | OPEN | NN · OP · OP · PP · PP |
| termStructural/all | 481 → 452 | OPEN | NN · OP · OP · PP · PP |
| termStructural/all | 504 → 427 | OPEN | NN · OP · OP · PP · PP |
| termStructural/all | 543 → 4541 | OPEN | NN · OP · PP · PP · PP |
| termStructural/all | 879 → 632 | OPEN | NN · OP · OP · PP · PP |
| termStructural/all | 910 → 427 | OPEN | NN · OP · PP · PP · PP |
| termStructural/all | 1492 → 417 | OPEN | NN · OP · PP · PP · PP |
| termStructural/all | 1496 → 452 | OPEN | NN · OP · PP · PP · PP |
| termStructural/fin | 56 → 50 | OPEN | NN · OO · PP · PP · PP |
| termStructural/fin | 167 → 117 | REFUTED | NN · NN · OO · PP · PP |
| termStructural/fin | 440 → 414 | OPEN | NN · OO · PP · PP · PP |
| structural/fin | 56 → 50 | PROVED | NN · OO · PP · PP · PP |
| structural/fin | 167 → 117 | OPEN | NN · NN · OO · PP · PP |
| structural/fin | 332 → 3 | OPEN | NN · NN · OO · PP · PP |
| structural/fin | 440 → 414 | PROVED | NN · OO · PP · PP · PP |
