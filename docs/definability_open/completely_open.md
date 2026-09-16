# Completely open in all eight definability variants

[Full audit](../definability_open_audit.md) · [All board totals](summary.md) · [Spectrum recheck](../definability_spectrum_check.md)

Snapshot: 2026-09-16. **284 directed equation pairs**, compressed losslessly into **61 class pairs**.

A pair `source → target` is completely open exactly when neither of these is known:

- A negative for **term-structural definability on arbitrary carriers** (TS/all).
- A positive for **FO definability on finite carriers** (D/fin).

TS/all is the strongest of the eight variants and D/fin the weakest.
Every positive anywhere implies D/fin positive; every negative anywhere implies
TS/all negative. Thus the endpoint test is equivalent to all eight statuses being
open. The generator checks this equivalence on every raw pair, not just representatives.

“Arbitrary carriers” allows infinite magmas; it does **not** mean infinitary terms.
Implication is excluded from the eight variants. OPEN means unresolved by the
current source-derived board, not necessarily unknown to mathematics.

## Counting and progress

We quotient by mutual **TS/all** positive arrows, using the least equation number
as representative. These classes refine those of every other definability variant,
so all eight statuses are constant on each rectangle. A weaker quotient would not
justify this claim. The raw count is the primary progress metric: class counts can
also fall merely because new positive equivalences merge classes.

The 15 September snapshot and the subsequent square-swap / argument-swap passes
all have **284 raw / 61 reduced** completely open pairs. Those passes improve
structural/all without changing either endpoint of this metric.

## Complete inventory

Each row denotes `class(source) × class(target)`. No pairs are omitted;
the next section supplies every member needed to expand the rectangles.

| Source representative | Target representative | Raw pairs |
|---:|---:|---:|
| 467 | 667 | 4 |
| 467 | 917 | 4 |
| 467 | 1086 | 4 |
| 467 | 1729 | 4 |
| 477 | 680 | 4 |
| 477 | 1073 | 12 |
| 477 | 1113 | 4 |
| 477 | 1695 | 4 |
| 481 | 680 | 4 |
| 481 | 1073 | 12 |
| 481 | 1113 | 4 |
| 481 | 1682 | 4 |
| 481 | 1695 | 4 |
| 704 | 504 | 4 |
| 704 | 870 | 4 |
| 704 | 910 | 4 |
| 704 | 917 | 4 |
| 704 | 1086 | 4 |
| 704 | 1722 | 4 |
| 704 | 1729 | 4 |
| 1076 | 1313 | 4 |
| 1276 | 680 | 4 |
| 1276 | 692 | 16 |
| 1276 | 707 | 4 |
| 1276 | 1316 | 4 |
| 1276 | 1695 | 4 |
| 1279 | 504 | 4 |
| 1279 | 870 | 4 |
| 1279 | 910 | 4 |
| 1279 | 917 | 4 |
| 1279 | 1086 | 4 |
| 1279 | 1722 | 4 |
| 1279 | 1729 | 4 |
| 1279 | 3345 | 4 |
| 1279 | 3548 | 4 |
| 1480 | 1482 | 4 |
| 1483 | 1479 | 4 |
| 1483 | 1485 | 4 |
| 1485 | 1483 | 4 |
| 1486 | 167 | 2 |
| 1486 | 168 | 6 |
| 1486 | 1479 | 4 |
| 1486 | 1480 | 4 |
| 1486 | 1483 | 4 |
| 1486 | 1485 | 4 |
| 1492 | 680 | 4 |
| 1492 | 1073 | 12 |
| 1492 | 1113 | 4 |
| 1492 | 1695 | 4 |
| 1496 | 680 | 4 |
| 1496 | 1073 | 12 |
| 1496 | 1113 | 4 |
| 1496 | 1682 | 4 |
| 1496 | 1695 | 4 |
| 1516 | 1489 | 4 |
| 1685 | 3548 | 4 |
| 3342 | 3545 | 4 |
| 3342 | 4405 | 2 |
| 3352 | 4408 | 4 |
| 3545 | 3342 | 4 |
| 3545 | 4405 | 2 |

## All participating class memberships

Classes not incident to a completely open pair are omitted. Ranges are inclusive.

| Representative | All members |
|---:|---|
| 167 | 167 |
| 168 | 168, 1487, 2164 |
| 467 | 467, 3140 |
| 477 | 477, 3150 |
| 481 | 481, 3161 |
| 504 | 504, 3143 |
| 667 | 667, 2900 |
| 680 | 680, 2947 |
| 692 | 692, 746, 1358, 1707, 1977, 2373, 2979, 2992 |
| 704 | 704, 2903 |
| 707 | 707, 2940 |
| 870 | 870, 2697 |
| 910 | 910, 2737 |
| 917 | 917, 2710 |
| 1073 | 1073, 1152, 1155, 2494, 2573, 2576 |
| 1076 | 1076, 2531 |
| 1086 | 1086, 2541 |
| 1113 | 1113, 2534 |
| 1276 | 1276, 2291 |
| 1279 | 1279, 2328 |
| 1313 | 1313, 2294 |
| 1316 | 1316, 2331 |
| 1479 | 1479, 2088 |
| 1480 | 1480, 2089 |
| 1482 | 1482, 2125 |
| 1483 | 1483, 2163 |
| 1485 | 1485, 2162 |
| 1486 | 1486, 2126 |
| 1489 | 1489, 2098 |
| 1492 | 1492, 2135 |
| 1496 | 1496, 2146 |
| 1516 | 1516, 2091 |
| 1682 | 1682, 1885 |
| 1685 | 1685, 1922 |
| 1695 | 1695, 1932 |
| 1722 | 1722, 1925 |
| 1729 | 1729, 1898 |
| 3342 | 3342, 4167 |
| 3345 | 3345, 4157 |
| 3352 | 3352, 4164 |
| 3545 | 3545, 3964 |
| 3548 | 3548, 3954 |
| 4405 | 4405 |
| 4408 | 4408, 4479 |

## Reproduction

Run `OPENBLAS_NUM_THREADS=2 python3 scripts/definability_audit.py --write --verify-closure`.
Use `--check` instead of `--write` to check the committed snapshot without rewriting it.
The `completely_open` record in [snapshot.json](snapshot.json) contains the same
pairs and class memberships. Counts are recomputed from Lean-source facts and closure;
this documentation does not feed proof facts back into the board.
