# Spectrum obstructions versus the definability boards

Rechecked on 16 September 2026, for all E1–E4694 directed pairs, not just the
[completely-open shortlist](definability_open/completely_open.md).

**Result: no new negative cells.** The completed spectrum results obstruct
**5,172,050 distinct directed pairs**; every one is already negative in **all
eight** definability boards. In particular, none reduces the 284 completely
open pairs in the pre-Gaussian snapshot. The later
[Gaussian recovery obstructions](definability_gaussian_recovery.md) change
only TS/all negatives, not the D/fin closure or any spectrum theorem; they do
not change this no-new-spectrum-negatives conclusion.

| Obstruction | Laws with a proved source model | Laws with a proved target exclusion | Obstructed directed pairs | New D/fin negatives |
|---|---:|---:|---:|---:|
| Order 2 | 3,136 | 1,558 | 4,885,888 | 0 |
| Order 3 | 3,106 | 1,581 | 4,910,586 | 0 |
| Order 4 | 3,164 | 1,498 | 4,739,672 | 0 |
| Order 5 | 3,157 | 1,498 | 4,729,186 | 0 |
| Some order > 1, versus singleton spectrum | 3,198 | 1,496 | 4,784,208 | 0 |

Rows overlap and must not be added. Counts are after transport and products;
they count known presence/absence, not a complete size-by-size classification.
The distinct union, 5,172,050, is the comparison against each negative board.
The environment export used 3,074 full-spectrum facts, 324 concrete/family
model facts, 1,679 concrete exclusion facts, 3,618 inclusions, and 134 spectrum
equalities (these include aliases, not that many independent proofs).
It skipped 311 pending declarations or dependent aliases.

## Direction and strength

If source → target is finite-FO-definable, then
`spectrum(source) ⊆ spectrum(target)`. A proved source model of order n and a
proved absence of target models at n therefore refute **D/fin**, and hence all
eight definability variants (and implication).
Equal spectra, or compatible bounds, do not prove definability.

The bridge is already formalized as
`Law.MagmaLaw.subspectral_of_definableFin` in
[Spectrum/Definability.lean](../equational_theories/Spectrum/Definability.lean).
No new notion of definability or additional proof axiom is needed.

## What was checked

The reproducible checker is
[scripts/spectrum_definability_check.py](../scripts/spectrum_definability_check.py):

1. Run the existing Lean catalogue audit: verify the actual declaration types
   and transitive proof dependencies for every spectrum classification, exact
   formula, and UNKNOWN-case bound.
2. Inspect the imported Lean environment using
   [spectrum_definability_facts.lean](../scripts/spectrum_definability_facts.lean).
   Export completed concrete `HasModel` / `¬ HasModel` theorems, full spectra,
   spectrum inclusions, and spectrum equalities. Skip pending declarations and
   all aliases depending on them. Reject unapproved axioms; explicitly tagged
   native/BV proofs are allowed by `Spectrum.Status`.
3. Instantiate the unconditional one-natural-parameter construction families
   at 0–5, covering their relevant small orders. Include the square/odd/even
   constructions, not just the catalogue JSON's non-exhaustive witness lists.
4. Add the current D/fin positive closure to the completed spectrum-inclusion
   graph, then close transitively. Transport models forward and exclusions
   backward. Add the product of two order-2 models at order 4.
5. Cross every proved model with every proved exclusion at orders 2, 3, 4, 5,
   and compare with the existing negatives in **each** of the eight boards.
   Separately handle singleton spectra at **all orders**, without imposing a
   bounded-search cutoff.

The completed exact formulas are: 3,074 full spectra, 1,496 singleton spectra,
two spectra excluding exactly {2, 4}, and two excluding exactly {2}. The other
completed concrete exclusions occur only at orders 2–5; completed upper bounds
for UNKNOWN cases exclude only 2 and/or 3. These statements are checked against
the catalogue and live theorem export. The script fails if a new exclusion order
or completed formula needs a broader scan.

For singleton targets, the checker verifies that **every other law has a proved
nontrivial finite model**, after transport. Thus their all-order exclusions are
covered; checking just order 2 would not suffice. Beyond singleton targets,
the two larger completed exclusion bases are E474 at order 4 and E1286 at
order 5, including their consequences under spectrum inclusions.

## Evidence boundary

This is a read-only cross-check, not a Lean proof generator. Spectrum seeds
receive the transitive-axiom audit above. The definability closure is the same
source-derived board used by the [main audit](definability_open_audit.md), with
its documented extraction limitations; it is not being re-certified as one
giant Lean theorem here. Failure to find a model is never used as an exclusion.

The note's modular restrictions, square-only and power-of-two-only upper bounds,
and remaining larger ATP exclusions are **not** completed Lean proofs in this
checkout. In particular, the 24 `PROOF_AVAILABLE` exact formulas and 30
`NOTE_GAP` exact formulas are not admitted as evidence. Formalizing those may
yield further obstructions; this check makes no claim that spectrum methods
are mathematically exhausted. Nor does it assert that every possible logical
consequence of the available theorems was found.

## Reproduction

```sh
lake build equational_theories.Spectrum
OPENBLAS_NUM_THREADS=2 python3 scripts/spectrum_definability_check.py
```

The script prints model/exclusion counts, distinct obstructed pairs, coverage
by each negative board, and every newly detected D/fin negative. It does not
write a second proof-data catalogue or modify the board. Its reported source
fingerprint can be compared with the [open-cell snapshot](definability_open/snapshot.json).
