# Completely open in all eight definability variants

[Full audit](../definability_open_audit.md) · [All board totals](summary.md) · [Spectrum recheck](../definability_spectrum_check.md)

Snapshot: 2026-09-21. **28 directed equation pairs**, compressed losslessly into **8 class pairs**.

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

In particular, **E1486 → E1483** (and its dual class rectangle) has a
[known computational proof](../definability_1483_order_eleven.md), but the
734 MiB certificate bundle is not distributed. Its Lean exclusion is marked
`proofAvailable` with `sorry`, and its negative is not counted as checked.

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

The [central-spectrum pass](../definability_central_spectrum.md) adds checked
D/fin negatives E1486 → E167 and E1486 → E168, hence negatives in all eight variants.

The [twisted-recovery pass](../definability_twisted_recovery.md) adds finite TS negatives
E1076 → E1313, E1516 → E1489, and E1685 → E3548, closing another 12 raw pairs.

The [idempotent-orbit pass](../definability_idempotent_orbit.md) adds a finite TD negative
E1483 → E1485, closing another four raw pairs in TD and TS, on both carrier flavours.

The [compatible-relations pass](../definability_binary_relations.md) adds a finite TD negative
E1480 → E1482, closing another four raw pairs in the same four variants.

The [prime-order pass](../definability_weak_central_prime.md) proves that E1485
has no odd-prime-order models. Together with the eleven-element E1486 witness,
this closes E1486 → E1485 and its class rectangle in all eight variants.

The [subalgebra pass](../definability_subsets.md) adds a finite TS negative
E3352 → E4408, closing four raw pairs in both TS variants.

The [broader counting pass](../definability_partial_counting.md) settles partially
resolved TS cells; it leaves this completely-open inventory unchanged.

The subsequent [finite-family counting pass](../definability_affine_counting.md)
adds affine, translation, unary-symmetry, and binary-relation obstructions to partially
resolved cells; these also leave this inventory unchanged.

## Complete inventory

Each row denotes `class(source) × class(target)`. No pairs are omitted;
the next section supplies every member needed to expand the rectangles.

The four **closure impact** columns count distinct raw pairs among the current
**28 completely open pairs** that would cease to be completely open.
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
| [1483](https://teorth.github.io/equational_theories/implications/?1483) `x = (y ◇ x) ◇ (x ◇ (y ◇ z))` | [1479](https://teorth.github.io/equational_theories/implications/?1479) `x = (y ◇ x) ◇ (x ◇ (x ◇ y))` | 4 | 4 | 4 | 4 | 4 |
| [1485](https://teorth.github.io/equational_theories/implications/?1485) `x = (y ◇ x) ◇ (x ◇ (z ◇ y))` | [1483](https://teorth.github.io/equational_theories/implications/?1483) `x = (y ◇ x) ◇ (x ◇ (y ◇ z))` | 4 | 4 | 4 | 4 | 4 |
| [1486](https://teorth.github.io/equational_theories/implications/?1486) `x = (y ◇ x) ◇ (x ◇ (z ◇ z))` | [1479](https://teorth.github.io/equational_theories/implications/?1479) `x = (y ◇ x) ◇ (x ◇ (x ◇ y))` | 4 | 4 | 4 | 8 | 8 |
| [1486](https://teorth.github.io/equational_theories/implications/?1486) `x = (y ◇ x) ◇ (x ◇ (z ◇ z))` | [1480](https://teorth.github.io/equational_theories/implications/?1480) `x = (y ◇ x) ◇ (x ◇ (x ◇ z))` | 4 | 8 | 8 | 4 | 4 |
| [1486](https://teorth.github.io/equational_theories/implications/?1486) `x = (y ◇ x) ◇ (x ◇ (z ◇ z))` | [1483](https://teorth.github.io/equational_theories/implications/?1483) `x = (y ◇ x) ◇ (x ◇ (y ◇ z))` | 4 | 4 | 4 | 4 | 4 |
| [3342](https://teorth.github.io/equational_theories/implications/?3342) `x ◇ y = y ◇ (x ◇ (x ◇ x))` | [4405](https://teorth.github.io/equational_theories/implications/?4405) `x ◇ (x ◇ y) = (y ◇ x) ◇ x` | 2 | 2 | 2 | 2 | 2 |
| [3545](https://teorth.github.io/equational_theories/implications/?3545) `x ◇ y = y ◇ ((x ◇ x) ◇ x)` | [3342](https://teorth.github.io/equational_theories/implications/?3342) `x ◇ y = y ◇ (x ◇ (x ◇ x))` | 4 | 4 | 4 | 4 | 4 |
| [3545](https://teorth.github.io/equational_theories/implications/?3545) `x ◇ y = y ◇ ((x ◇ x) ◇ x)` | [4405](https://teorth.github.io/equational_theories/implications/?4405) `x ◇ (x ◇ y) = (y ◇ x) ◇ x` | 2 | 2 | 2 | 2 | 2 |

## All participating class memberships

Classes not incident to a completely open pair are omitted. Ranges are inclusive.

| Representative | All members |
|---:|---|
| 1479 | 1479, 2088 |
| 1480 | 1480, 2089 |
| 1483 | 1483, 2163 |
| 1485 | 1485, 2162 |
| 1486 | 1486, 2126 |
| 3342 | 3342, 4167 |
| 3545 | 3545, 3964 |
| 4405 | 4405 |

## Reproduction

Run `OPENBLAS_NUM_THREADS=2 python3 scripts/definability_audit.py --write --verify-closure`.
Use `--check` instead of `--write` to check the committed snapshot without rewriting it.
The `completely_open` record in [snapshot.json](snapshot.json) contains the same
pairs, class memberships, and four counts per row in `closure_impacts`.
The impact calculation uses exact single-edge closure formulas, tested against
full recomputation on small boards, including cycles and mixed-flavour consequences.
Counts are recomputed from Lean-source facts and closure;
this documentation does not feed proof facts back into the board.
