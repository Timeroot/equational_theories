# Completely open in all eight definability variants

[Full audit](../definability_open_audit.md) · [All board totals](summary.md) · [Spectrum recheck](../definability_spectrum_check.md)

Snapshot: 2026-09-16. **68 directed equation pairs**, compressed losslessly into **18 class pairs**.

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
all had **284 raw / 61 reduced** completely open pairs. Those passes improved
structural/all without changing either endpoint of this metric.
The later [Gaussian recovery obstructions](../definability_gaussian_recovery.md)
reduced the inventory to **180 raw / 43 reduced** pairs.
The [linear-counting and integrality pass](../definability_counting_recovery.md)
adds finite TS and arbitrary-carrier TS negatives; current counts and impacts include both.

## Complete inventory

Each row denotes `class(source) × class(target)`. No pairs are omitted;
the next section supplies every member needed to expand the rectangles.

The four **closure impact** columns count distinct raw pairs among the current
**68 completely open pairs** that would cease to be completely open.
Each column independently assumes just the indicated result for that row:
`+` means a positive theorem; `−` means a refutation of the named variant.
Counts include the row’s own raw pairs, not just additional consequences.
Already partly settled pairs, multiple flavours of the same pair, and future
class mergers are not counted. Rows overlap, so their impacts must not be added.

Closure includes transitivity, the finite/all and definability hierarchies, and
**propagation of existing negatives through newly proved positive arrows**.
Thus a positive assumption can resolve other pairs negatively as well.
Counting only newly positive pairs would make the two positive columns identical:
either assumption adds the same arrow to D/fin. These are conditional bookkeeping
consequences, not new proofs, predictions of solvability, or a minimal basis.

| Source representative | Target representative | Raw pairs | + TS/all | + D/fin | − TS/all | − D/fin |
|---|---|---:|---:|---:|---:|---:|
| [1076](https://teorth.github.io/equational_theories/implications/?1076) `x = y ◇ ((x ◇ (x ◇ y)) ◇ y)` | [1313](https://teorth.github.io/equational_theories/implications/?1313) `x = y ◇ (((y ◇ x) ◇ x) ◇ y)` | 4 | 4 | 4 | 4 | 4 |
| [1480](https://teorth.github.io/equational_theories/implications/?1480) `x = (y ◇ x) ◇ (x ◇ (x ◇ z))` | [1482](https://teorth.github.io/equational_theories/implications/?1482) `x = (y ◇ x) ◇ (x ◇ (y ◇ y))` | 4 | 4 | 4 | 4 | 4 |
| [1483](https://teorth.github.io/equational_theories/implications/?1483) `x = (y ◇ x) ◇ (x ◇ (y ◇ z))` | [1479](https://teorth.github.io/equational_theories/implications/?1479) `x = (y ◇ x) ◇ (x ◇ (x ◇ y))` | 4 | 4 | 4 | 8 | 8 |
| [1483](https://teorth.github.io/equational_theories/implications/?1483) `x = (y ◇ x) ◇ (x ◇ (y ◇ z))` | [1485](https://teorth.github.io/equational_theories/implications/?1485) `x = (y ◇ x) ◇ (x ◇ (z ◇ y))` | 4 | 8 | 8 | 4 | 4 |
| [1485](https://teorth.github.io/equational_theories/implications/?1485) `x = (y ◇ x) ◇ (x ◇ (z ◇ y))` | [1483](https://teorth.github.io/equational_theories/implications/?1483) `x = (y ◇ x) ◇ (x ◇ (y ◇ z))` | 4 | 4 | 4 | 4 | 4 |
| [1486](https://teorth.github.io/equational_theories/implications/?1486) `x = (y ◇ x) ◇ (x ◇ (z ◇ z))` | [167](https://teorth.github.io/equational_theories/implications/?167) `x = (y ◇ x) ◇ (x ◇ y)` | 2 | 2 | 2 | 8 | 8 |
| [1486](https://teorth.github.io/equational_theories/implications/?1486) `x = (y ◇ x) ◇ (x ◇ (z ◇ z))` | [168](https://teorth.github.io/equational_theories/implications/?168) `x = (y ◇ x) ◇ (x ◇ z)` | 6 | 24 | 24 | 6 | 6 |
| [1486](https://teorth.github.io/equational_theories/implications/?1486) `x = (y ◇ x) ◇ (x ◇ (z ◇ z))` | [1479](https://teorth.github.io/equational_theories/implications/?1479) `x = (y ◇ x) ◇ (x ◇ (x ◇ y))` | 4 | 4 | 4 | 18 | 18 |
| [1486](https://teorth.github.io/equational_theories/implications/?1486) `x = (y ◇ x) ◇ (x ◇ (z ◇ z))` | [1480](https://teorth.github.io/equational_theories/implications/?1480) `x = (y ◇ x) ◇ (x ◇ (x ◇ z))` | 4 | 8 | 8 | 10 | 10 |
| [1486](https://teorth.github.io/equational_theories/implications/?1486) `x = (y ◇ x) ◇ (x ◇ (z ◇ z))` | [1483](https://teorth.github.io/equational_theories/implications/?1483) `x = (y ◇ x) ◇ (x ◇ (y ◇ z))` | 4 | 4 | 4 | 10 | 10 |
| [1486](https://teorth.github.io/equational_theories/implications/?1486) `x = (y ◇ x) ◇ (x ◇ (z ◇ z))` | [1485](https://teorth.github.io/equational_theories/implications/?1485) `x = (y ◇ x) ◇ (x ◇ (z ◇ y))` | 4 | 8 | 8 | 10 | 10 |
| [1516](https://teorth.github.io/equational_theories/implications/?1516) `x = (y ◇ y) ◇ (x ◇ (x ◇ y))` | [1489](https://teorth.github.io/equational_theories/implications/?1489) `x = (y ◇ x) ◇ (y ◇ (x ◇ y))` | 4 | 4 | 4 | 4 | 4 |
| [1685](https://teorth.github.io/equational_theories/implications/?1685) `x = (y ◇ x) ◇ ((x ◇ y) ◇ y)` | [3548](https://teorth.github.io/equational_theories/implications/?3548) `x ◇ y = y ◇ ((x ◇ y) ◇ x)` | 4 | 4 | 4 | 4 | 4 |
| [3342](https://teorth.github.io/equational_theories/implications/?3342) `x ◇ y = y ◇ (x ◇ (x ◇ x))` | [3545](https://teorth.github.io/equational_theories/implications/?3545) `x ◇ y = y ◇ ((x ◇ x) ◇ x)` | 4 | 4 | 4 | 4 | 4 |
| [3342](https://teorth.github.io/equational_theories/implications/?3342) `x ◇ y = y ◇ (x ◇ (x ◇ x))` | [4405](https://teorth.github.io/equational_theories/implications/?4405) `x ◇ (x ◇ y) = (y ◇ x) ◇ x` | 2 | 2 | 2 | 2 | 2 |
| [3352](https://teorth.github.io/equational_theories/implications/?3352) `x ◇ y = y ◇ (y ◇ (x ◇ x))` | [4408](https://teorth.github.io/equational_theories/implications/?4408) `x ◇ (x ◇ y) = (y ◇ y) ◇ x` | 4 | 4 | 4 | 4 | 4 |
| [3545](https://teorth.github.io/equational_theories/implications/?3545) `x ◇ y = y ◇ ((x ◇ x) ◇ x)` | [3342](https://teorth.github.io/equational_theories/implications/?3342) `x ◇ y = y ◇ (x ◇ (x ◇ x))` | 4 | 4 | 4 | 4 | 4 |
| [3545](https://teorth.github.io/equational_theories/implications/?3545) `x ◇ y = y ◇ ((x ◇ x) ◇ x)` | [4405](https://teorth.github.io/equational_theories/implications/?4405) `x ◇ (x ◇ y) = (y ◇ x) ◇ x` | 2 | 2 | 2 | 2 | 2 |

## All participating class memberships

Classes not incident to a completely open pair are omitted. Ranges are inclusive.

| Representative | All members |
|---:|---|
| 167 | 167 |
| 168 | 168, 1487, 2164 |
| 1076 | 1076, 2531 |
| 1313 | 1313, 2294 |
| 1479 | 1479, 2088 |
| 1480 | 1480, 2089 |
| 1482 | 1482, 2125 |
| 1483 | 1483, 2163 |
| 1485 | 1485, 2162 |
| 1486 | 1486, 2126 |
| 1489 | 1489, 2098 |
| 1516 | 1516, 2091 |
| 1685 | 1685, 1922 |
| 3342 | 3342, 4167 |
| 3352 | 3352, 4164 |
| 3545 | 3545, 3964 |
| 3548 | 3548, 3954 |
| 4405 | 4405 |
| 4408 | 4408, 4479 |

## Reproduction

Run `OPENBLAS_NUM_THREADS=2 python3 scripts/definability_audit.py --write --verify-closure`.
Use `--check` instead of `--write` to check the committed snapshot without rewriting it.
The `completely_open` record in [snapshot.json](snapshot.json) contains the same
pairs, class memberships, and four counts per row in `closure_impacts`.
The impact calculation uses exact single-edge closure formulas, tested against
full recomputation on small boards, including cycles and mixed-flavour consequences.
Counts are recomputed from Lean-source facts and closure;
this documentation does not feed proof facts back into the board.
