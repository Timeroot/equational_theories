# E1485/E1486: spectrum separations and their proof status

17 September 2026. The direction `source → target` means defining a target
operation on every source carrier. Spectra therefore satisfy
`spectrum(source) ⊆ spectrum(target)` whenever even finite FO-definability holds.

## Results and evidence

| Result | Mathematical status | Lean status |
|---|---|---|
| Every finite E168 magma has square cardinality | Knuth's theorem | Complete: explicit bijections, no computational axiom |
| E167 has no model of size 11 | Permutation-parity obstruction | Complete: only the sign of a fixed permutation is computed |
| E1486 has models of sizes 11, 13 and 21 | Explicit tables of Matthew Bolan | Complete: each table checked by `decide` in the kernel |
| E1486 → E167 and E1486 → E168 are impossible | The size-11 witness separates the spectra | Complete in D/fin, hence all eight variants |
| E1485 has no odd-prime-order model | Sharp-edge factorizations and prime translation ranks | Complete: general theorem, only standard axioms |
| E1486 → E1485 is impossible | The size-11 witness and the prime-order exclusion | Complete in D/fin, hence all eight variants |
| Exact E1485 spectrum is squares or twice squares | Conjectural | No equality theorem asserted |
| E1486 has models of size k²+2 for k ≥ 3 | Le Floch's explicit construction recovered | General proof pending, reclassified from `noteGap` to `proofAvailable` |

The E1485 exclusions at 11 and 13 were originally reported as exhaustive
Vampire/Mace4 runs without public inputs or certificates. They are now proved
by a general mathematical argument formalized in Lean; the exact spectrum
remains conjectural.

The initial central-spectrum pass reduced the board from **68 to 60 raw
completely-open pairs**, or **18 to 16 TS/all class rows**. The removed rows
were `{1486,2126} → {167}` and `{1486,2126} → {168,1487,2164}`.
After intervening term obstructions, the prime-order proof removes
`{1486,2126} → {1485,2162}`, reducing the table from **40 to 36 raw pairs**,
or **11 to 10 class rows**. All eight variants are negative on that rectangle.
The order-11/13 witnesses do not settle the reverse direction involving E1485.

## Proofs and organization

[CentralCardinality.lean](../equational_theories/Spectrum/CentralCardinality.lean)
proves the E168 cardinality theorem. Write `Row a = {a ◇ x}` and
`Col b = {x ◇ b}`. The central identity gives

- `Row a ≃ Col b`, by `u ↦ u ◇ b`, inverse `v ↦ a ◇ v`;
- `G ≃ Row a × Col a`, by `x ↦ (a ◇ x, x ◇ a)`, inverse `(u,v) ↦ u ◇ v`.

The inverse identities hold even on infinite carriers. Taking finite
cardinalities gives `|G| = |Row a|²`. Together with the existing natural
central-groupoid construction this completes the exact spectrum for E168
and its equivalent laws E1487 and E2164.

[BookendCardinality.lean](../equational_theories/Spectrum/BookendCardinality.lean)
uses `T(x,y) = (x ◇ y, y ◇ x)`. E167 says `T²` swaps the coordinates.
A square permutation is even, whereas the swap on `Fin 11 × Fin 11` has
55 transpositions and is odd. The code computes the sign of that one fixed
permutation, not any of the `11^121` possible operation tables. The general
mod-4 necessity and existence theorem remain separate pending obligations.

[Generated/CentralWitnesses.lean](../equational_theories/Spectrum/Generated/CentralWitnesses.lean)
contains the three E1486 tables. It is generated from the existing
`data/spectrum/witnesses.json` cache, with no new proof-data format. It has
lightweight imports so the definability proofs do not pull in the full spectrum
catalogue. `Definability.lean` gains one import; no existing imports are removed.
The combined build also exposed two unrelated declarations called
`Magma.transport`. The spectrum operation is now `Magma.relabel`, with
isomorphism `Magma.relabelEquiv`; the definability orbit-transport API is unchanged.
This fixes importing the two developments together.

[WeakCentralCardinality.lean](../equational_theories/Spectrum/WeakCentralCardinality.lean)
proves that two is the only possible prime order of an E1485 model. Every
element has sharp neighbors, yielding a rectangular factorization of the
carrier. Consequently each row rank divides the order. At prime order every
row is constant or bijective, and a direct algebraic argument permits at most
one element of each type. See the [full proof guide](definability_weak_central_prime.md).

[Definability/CentralSpectrum.lean](../equational_theories/Definability/CentralSpectrum.lean)
contains all three completed finite-FO negatives, with standard-axiom guards.
The historical names in
[Spectrum/PendingDefinability.lean](../equational_theories/Spectrum/PendingDefinability.lean)
and [NotePending.lean](../equational_theories/Spectrum/NotePending.lean) now
have completed proofs and `complete` status assertions. The catalogue uses
the completed exclusions directly; E1485's exact-spectrum conjecture is unchanged.

## Why the earlier spectrum check missed this

It used completed Lean proofs only. Both the nonsquare E1486 witnesses and
the E167/E168 obstructions were pending, and E1485's specific order-11/13
search results had not been recorded. Thus the earlier “no new negatives”
conclusion concerned the then-completed Lean evidence, not the literature.

The checker now evaluates completed exact/upper-bound formulas at **every
exported witness or exclusion order**, including the square formula, rather
than hard-coding orders 2–5. It still excludes reported/pending proofs and
fails explicitly on unsupported completed formula syntax. Its finite sample
of construction-family parameters is not an all-orders exhaustiveness claim.
See [the spectrum recheck](definability_spectrum_check.md).

## Sources

- [Bolan's 11- and 13-element tables, 25 November 2024](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/Austin.20pairs.html#484348920).
- [Bolan's 21-element table](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/Austin.20pairs.html#484345673).
- [Le Floch's k²+2 construction, 28 November 2024 at 15:46](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/Understanding.20Finite.201486.20Magmas.html).
- E1485 exhaustive exclusions: project-author report and clarification in this
  working session, 17 September 2026; no public search input/certificate.

## Validation and timings

All three completed definability negatives use only standard axioms. Guards
cover them, the cardinality/exclusion arguments, and all three finite witnesses.
The historical E1485 consequence also has a standard-axiom guard. The timings
below are from the initial E167/E168 pass; validation of the prime-order addition
is recorded in its [guide](definability_weak_central_prime.md).

Measured total standalone commands (`/usr/bin/time lake env lean FILE`):
BookendCardinality **9.29 s**, CentralCardinality **34.45 s**, and
Generated/CentralWitnesses (all three tables) **84.91 s**. These are full
elaboration/checking times, not solver times; the latter two ran concurrently
with the full rebuild and audit under substantial load. The corresponding
Lean jobs in the combined rebuild took 15 s, 4.6 s and 34 s respectively;
the small definability consequence module took 2.9 s.

The full combined `Definability` + `Spectrum` build passed: **16,853 jobs,
384.03 s**, including the spectrum rebuild caused by the API collision fix.
The reference-verified board audit passed in **207.63 s**, and all **21**
Python regression tests passed. The import checker retains all **13,340**
reachable local modules with **6,579** direct entry imports.
The catalogue type/axiom audit and status-regression checks passed. The broadened
spectrum scan checked 22 orders and found no further missing D/fin negatives
after this batch; all 5,172,175 detected obstructions are covered in all eight boards.
