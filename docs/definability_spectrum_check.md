# Spectrum obstructions versus the definability boards

The [central-spectrum pass](definability_central_spectrum.md) formalizes evidence
that was **not admitted by the earlier check**: E1486 models at orders 11, 13 and
21, the E167 order-11 exclusion, and E168's square-cardinality theorem.
E1486 → E167 and E1486 → E168 now have checked D/fin negatives, hence negatives
in all eight variants. Eight raw completely-open pairs across two rows close.

The earlier 16 September result—5,172,050 spectrum-obstructed pairs, all already
negative—concerned the **then-completed Lean proofs only**, not everything known
in the literature. The [prime-order proof](definability_weak_central_prime.md)
now completes the E1485 exclusions at 11 and 13 without replaying the reported
Vampire/Mace4 searches. E1486 → E1485 has a checked finite-FO negative too,
removing four more completely-open pairs in all eight variants.

## Rechecked result: 18 September 2026

After integrating all three central-spectrum generators, **no further missing D/fin negatives**
were found. The scan covers **22 orders**: 2–19, 21, 25, 32 and 50.
Its **5,172,297 distinct obstructed pairs** are already negative in all eight
boards. This is 247 more detected obstructions than the old restricted scan;
twelve needed new board proofs across the three central-spectrum generators,
and the others were already known by other methods. The recheck after the finite clone-family counting certificates gives the same spectrum counts;
its source fingerprint agrees with the updated open-cell audit.

| Order | Known model laws | Known excluded laws | Obstructed pairs | Further missing D/fin |
|---|---:|---:|---:|---:|
| 11 | 3,126 | 1,502 | 4,695,252 | 0 |
| 13 | 3,161 | 1,501 | 4,744,661 | 0 |
| 21 | 3,108 | 1,499 | 4,658,892 | 0 |

The export has 3,074 full-spectrum facts, 327 concrete/sampled model facts,
1,685 exclusions, 3,622 inclusions and 134 equalities (including dependent
aliases). It skips **303 pending declarations or dependent aliases**. The completed
E1485 exclusions and their aliases are now included. The per-order counts above must not be added.

## Direction and strength

Finite-FO-definability source → target implies
`spectrum(source) ⊆ spectrum(target)`. A source model of order n and absence
of target models at n refute **D/fin**, hence all eight variants.
Compatible spectra do not prove definability.

The Lean bridge is `Law.MagmaLaw.subspectral_of_definableFin` in
[Spectrum/Definability.lean](../equational_theories/Spectrum/Definability.lean).
The new board seeds are in
[Definability/CentralSpectrum.lean](../equational_theories/Definability/CentralSpectrum.lean),
with axiom guards. The cross-check does not add board seeds by itself.

## What the checker does

[scripts/spectrum_definability_check.py](../scripts/spectrum_definability_check.py):

1. Runs the Lean catalogue audit: actual types and transitive proof dependencies
   for all 4694 classifications, exact formulas and bounds.
2. Uses [spectrum_definability_facts.lean](../scripts/spectrum_definability_facts.lean)
   to export completed concrete models/exclusions, full spectra, spectrum
   inclusions/equalities, and construction families instantiated at parameters
   0–5. Pending declarations and dependent aliases are skipped.
   Unapproved axioms are rejected; explicitly tagged native/BV proofs are allowed.
3. Considers **every exported witness or exclusion order**, not a hard-coded
   2–5 list. At these orders it evaluates completed exact formulas and upper
   bounds, including `squares`; unsupported syntax causes an explicit error.
   Upper bounds supply exclusions only, never existence claims.
4. Adds the current D/fin positive closure to the spectrum-inclusion graph.
   Models travel forwards and exclusions backwards. Products are included when
   their factor orders occur in the scan. Singleton targets are handled at all
   orders: every other law is verified to have a nontrivial finite model.
5. Crosses known presence and absence, checking each of the eight negative
   boards. It prints every additional D/fin pair found, if any.

Counts are known presence/absence after propagation, not complete size-by-size
classifications. Different orders overlap, so their counts must not be added.
The finite construction-parameter sample is not an exhaustive all-orders search.

## Evidence boundary

This is a read-only diagnostic, not a proof generator. Spectrum declarations
receive the Lean dependency audit. Definability uses the same source-derived
closure as the [main audit](definability_open_audit.md), with its documented
extraction limitations, not one giant certified Lean theorem.
Failure to find a model is never used as an exclusion.

E168's square-only spectrum is now complete. Other pending modular, Gaussian
and power-of-two classifications, and reported larger finite refutations, remain
excluded. In this pass 21 exact catalogue formulas depend on available proofs
awaiting Lean and 30 on unreconstructed note steps. Neither category means those
exact spectra are unknown to mathematics.

## Reproduction

```sh
lake build equational_theories.Spectrum equational_theories.Definability
OPENBLAS_NUM_THREADS=2 python3 scripts/spectrum_definability_check.py
```

Output includes the source fingerprint, counts by order, distinct obstructed
pairs, coverage by each negative board, and newly detected D/fin pairs.
It does not create another proof-data catalogue.
