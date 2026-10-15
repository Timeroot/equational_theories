# Open-cell totals

[Audit and interpretation](../definability_open_audit.md).

**Completely open in all eight definability variants: [20 raw pairs / 6 class pairs](completely_open.md).**

Snapshot: 2026-10-14. Source SHA-256: `6925e970dc3381142f659afb54fb2f7a3c2ff0e609e80f4e43c32899f4119c62`.

All counts exclude diagonal pairs. Each full grid has 22,028,942 directed pairs.

| Relation / carriers | Classes | Positive | Negative | Raw open | Reduced open |
|---|---:|---:|---:|---:|---:|
| [implies/all](implies_all.md) | 1,415 | 8,173,585 | 13,855,357 | 0 | 0 |
| [implies/fin](implies_fin.md) | 1,370 | 8,174,405 | 13,854,535 | 2 | 2 |
| [termStructural/all](termStructural_all.md) | 739 | 8,561,349 | 13,446,881 | 20,712 | 4,309 |
| [termStructural/fin](termStructural_fin.md) | 716 | 8,563,515 | 13,446,581 | 18,846 | 3,844 |
| [structural/all](structural_all.md) | 735 | 9,037,755 | 12,569,391 | 421,796 | 56,851 |
| [structural/fin](structural_fin.md) | 711 | 9,067,699 | 12,556,446 | 404,797 | 53,202 |
| [termDefinable/all](termDefinable_all.md) | 112 | 14,382,905 | 7,644,794 | 1,243 | 251 |
| [termDefinable/fin](termDefinable_fin.md) | 91 | 14,383,835 | 7,642,880 | 2,227 | 210 |
| [definable/all](definable_all.md) | 108 | 14,397,811 | 7,627,299 | 3,832 | 619 |
| [definable/fin](definable_fin.md) | 87 | 14,400,818 | 7,624,767 | 3,357 | 302 |

## Arbitrary versus finite carriers

These are **raw pairs with the same equation numbers**, not comparisons between
different quotients. `P` = proved, `N` = refuted, `O` = open in the extracted board.

| Relation | all O / fin O | all O / fin P | all N / fin O | all N / fin P |
|---|---:|---:|---:|---:|
| implies | 0 | 0 | 2 | 820 |
| termStructural | 18,782 | 1,930 | 64 | 236 |
| structural | 391,852 | 29,944 | 12,945 | 0 |
| termDefinable | 857 | 386 | 1,370 | 544 |
| definable | 3,357 | 475 | 0 | 2,532 |

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
