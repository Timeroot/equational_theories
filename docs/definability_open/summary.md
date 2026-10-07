# Open-cell totals

[Audit and interpretation](../definability_open_audit.md).

**Completely open in all eight definability variants: [28 raw pairs / 8 class pairs](completely_open.md).**

Snapshot: 2026-10-07. Source SHA-256: `f20f5084a81a61f7ac78776c4922563dca489e601cce899085cd6574dbe2f7c2`.

All counts exclude diagonal pairs. Each full grid has 22,028,942 directed pairs.

| Relation / carriers | Classes | Positive | Negative | Raw open | Reduced open |
|---|---:|---:|---:|---:|---:|
| [implies/all](implies_all.md) | 1,415 | 8,173,585 | 13,855,357 | 0 | 0 |
| [implies/fin](implies_fin.md) | 1,370 | 8,174,405 | 13,854,535 | 2 | 2 |
| [termStructural/all](termStructural_all.md) | 739 | 8,561,349 | 13,446,012 | 21,581 | 4,467 |
| [termStructural/fin](termStructural_fin.md) | 716 | 8,563,515 | 13,445,716 | 19,711 | 3,999 |
| [structural/all](structural_all.md) | 737 | 9,030,589 | 12,557,152 | 441,201 | 59,880 |
| [structural/fin](structural_fin.md) | 712 | 9,066,339 | 12,556,440 | 406,163 | 53,459 |
| [termDefinable/all](termDefinable_all.md) | 112 | 14,382,905 | 7,644,775 | 1,262 | 257 |
| [termDefinable/fin](termDefinable_fin.md) | 91 | 14,383,835 | 7,642,861 | 2,246 | 216 |
| [definable/all](definable_all.md) | 108 | 14,397,807 | 7,627,289 | 3,846 | 625 |
| [definable/fin](definable_fin.md) | 88 | 14,400,810 | 7,624,757 | 3,375 | 311 |

## Arbitrary versus finite carriers

These are **raw pairs with the same equation numbers**, not comparisons between
different quotients. `P` = proved, `N` = refuted, `O` = open in the extracted board.

| Relation | all O / fin O | all O / fin P | all N / fin O | all N / fin P |
|---|---:|---:|---:|---:|
| implies | 0 | 0 | 2 | 820 |
| termStructural | 19,647 | 1,934 | 64 | 232 |
| structural | 405,451 | 35,750 | 712 | 0 |
| termDefinable | 876 | 386 | 1,370 | 544 |
| definable | 3,375 | 471 | 0 | 2,532 |

`all N / fin P` is a **settled** distinction, not an open question.
The JSON also records P/P and N/N. P/O, P/N and O/N must be zero.

## Historical shortlist rechecked

Every one of the 35 cells in the historical report §3.5, in its original relation.
The full profile uses `I, TS, S, TD, D`, with `all` then `fin` within each pair.

| Relation originally open | Source → target | Current status | I · TS · S · TD · D |
|---|---|---|---|
| termStructural/all | 63 → 125 | OPEN | NN · OP · OP · OP · OP |
| termStructural/all | 63 → 3548 | REFUTED | NN · NP · OP · OP · OP |
| termStructural/all | 124 → 1648 | OPEN | NN · OP · OP · PP · PP |
| termStructural/all | 124 → 3343 | OPEN | NN · OP · OP · PP · PP |
| termStructural/all | 124 → 4130 | OPEN | NN · OP · OP · PP · PP |
| termStructural/all | 125 → 3548 | REFUTED | NN · NP · PP · PP · PP |
| termStructural/all | 125 → 3954 | REFUTED | NN · NP · PP · PP · PP |
| termStructural/all | 206 → 1648 | OPEN | NP · OP · OP · PP · PP |
| termStructural/all | 206 → 3343 | OPEN | NN · OP · OP · PP · PP |
| termStructural/all | 222 → 3548 | REFUTED | NN · NP · PP · PP · PP |
| termStructural/all | 271 → 3548 | REFUTED | NN · NP · OP · OP · OP |
| termStructural/all | 1648 → 124 | REFUTED | NN · NP · OP · PP · PP |
| termStructural/all | 1648 → 206 | REFUTED | NP · NP · OP · PP · PP |
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
