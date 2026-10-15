# Small-order spectrum searches, 11 October 2026

The requested positive searches found **no new models**. They instead produced
several complete exclusions and narrowed the remaining searches. No order-ten
search was run. This note distinguishes Lean proofs, exhaustive external
computations, and timeouts.

| Law | Order | Result in this pass |
|---|---:|---|
| E63 | 14 | Lean exclusion; 1.51 MiB, 45-second certificate build |
| E1076 | 9, 11 | Lean exclusions |
| E1076 | 12 | Lean exclusion; nine compact certificates totaling 4.88 MiB |
| E1110 | 12 | Lean exclusion; separates `Spec(E167) ⊆ Spec(E1110)` |
| E1110 | 13 | Lean exclusion; refutes nine open spectrum inclusions |
| E704, E1279, E1516 | 12 | Lean exclusions |
| E467 | 12 | Lean exclusion; 419 KiB and a 17-second cached-dependency build |
| E1483 | 12 | Lean exclusion; 21.57 MiB, every individual check at most 49 seconds |
| E670, E677, E883, E1286, E1313, E1486 | 12 | Still unresolved |

The E1110 order-13 exclusion separates nine previously open inclusions into
E1110, from E167, E467, E677, E704, E1076, E1286, E1313, E1486, and E1516:
each source has a proved model of order 13. The order-12 result provides an
independent witness for the E167 separation; it is not a tenth distinct arrow.
The updated formal graph has **55 open directed spectrum inclusions**, down
from 64, and still just one possible class merge, E1483/E1485. See the
[updated inclusion inventory](spectrum_inclusion_inventory_20261011.md).
The nine separation theorems are explicit in
[`OrderThirteen/Separation.lean`](../equational_theories/Spectrum/Equation1110/OrderThirteen/Separation.lean).

Detailed checked-proof records:

* [E63 order 14](63_order14_lean.md).
* [E1110 order 12](1110_order12.md) and [order 13](e1110_order13.md).
* [E467 order 12](467_order12.md).
* [The five other small-order certificates](spectrum_positive_target_exclusions_20261011.md).

## Positive-search strategy

The first wave used CaDiCaL with 15-minute limits for unrestricted cases, and
separate idempotent and commutative probes. Finite chain-law models have
proved cancellation properties, which were included in the encoding. For
E1076, idempotence itself is a proved consequence of the law. For E1483 and
E1486, nontrivial idempotent models are impossible, so their searches instead
used row-image graphs and the normalization developed for earlier exclusions.
We also checked positive regressions at orders 4 and 9 to verify that the
encodings can still produce known models; those are not new spectrum seeds.

E1110 at order 12 received independent CP-SAT and Mace4 searches, each with a
15-minute limit. CP-SAT was tried both generally and in the subclass where
squaring is an automorphism. Neither solver found a model. A different restricted
search exhausted all principal isotopes of the five groups of order 12:
`C12`, `C6 × C2`, `A4`, the dihedral group, and the dicyclic group. These took
roughly 11–18 seconds each. The analogous search over the nonassociative
Chein loop of order 12 timed out after five minutes. These subclass results
alone are not general exclusions; the later complete squaring-permutation
argument is what settles E1110 at 12.

Associative restrictions do not offer an additional promising family here:
a finite associative quasigroup is a group and is included in the group-isotope
search. In the finite idempotent quasigroup cases, associativity or a one-sided
identity forces the singleton. Commutative E1110 magmas are automatically
idempotent, even without finiteness, by the new short algebraic Lean proof in
[Commutative.lean](../equational_theories/Spectrum/Equation1110/Commutative.lean).

## E1483 order 12: complete and checked

The original exhaustive search has been replaced by a complete Lean proof,
`Spectrum.not_order_1483_12`. The proof normalizes a minimum-rank row, excludes
constant and bijective rows using the power-of-two theorem, and uses the
edge bound `12 ≤ r(a)r(b)`. Lexicographic normalization, sharp-rank identities,
and explicit row orbits reduce the hard cases before certificate checking.
All symmetry reductions and coverage arguments are proved in Lean.

The final 68 compressed certificates total **21.57 MiB**; the largest is
**1.10 MiB**, and every individual native check completed within **49 seconds**
locally. The slower unsplit certificates have been removed. See the
[complete proof and performance note](1483_order12.md). E1485 also excludes
12, so this result does not resolve whether those two spectra coincide.

## What remains open at order twelve

The unrestricted CaDiCaL runs for E670, E677, E883, E1286, and E1313 reached
their 900-second limits. Their commutative probes refuted; the idempotent probes
for E670, E677, E1286, and E1313 remained unknown at 180 seconds. E883's
idempotent probe refuted in under a second. None of these restricted exclusions
settles the unrestricted question.

For E1486, the minimum square-row rank is 2 or 3. Four rank/image cases were
searched for 900 seconds apiece. Rank 2 with zero inside the image refuted in
670 seconds; the other three cases timed out. No order-12 existence or
nonexistence claim follows from this partial search.

## Reproduction and data

[The search record](../data/spectrum/positive_searches_20261011.json) preserves
69 runs, three positive regression tables, the initial E1110 diagonal sweep,
and hashes for the supplementary search sources. All reported SAT tables were
independently evaluated against the original equation in `data/equations.txt`.
The compact archive contains the additional CP-SAT, group-isotope, diagonal,
and Mace4 inputs; the main generator is
[`scripts/spectrum_positive_search_20261011.py`](../scripts/spectrum_positive_search_20261011.py).

Examples:

```sh
python3 scripts/spectrum_positive_search_20261011.py 1110 12 --seconds 900 --output /tmp/e1110-12
python3 scripts/spectrum_positive_search_20261011.py 1483 12 --rank 4 --fixed 0 1 2 --seed 1 --seconds 1200 --output /tmp/e1483-12-r4
python3 scripts/spectrum_positive_search_20261011.py 1486 12 --rank 3 --seconds 900 --output /tmp/e1486-12-r3
```

Every `UNSAT` status is scoped to its stated assumptions. `UNKNOWN` means a
bounded search did not decide the case. E467 at order 12 has since been fully formalized with small certificates.
E1076 and E1483 at order 12 are also now checked in Lean, with all certificate partitions justified formally.
