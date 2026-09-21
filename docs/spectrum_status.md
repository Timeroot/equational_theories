# Finite spectra

The complete catalogue is in [spectrum_catalogue.md](spectrum_catalogue.md) and
`data/spectrum/catalogue.json`. All 4694 original laws are covered: **4630 exact
formulas from the PDF and proved supplements**, and **64 exact spectra still UNKNOWN
in this development**. Of the exact formulas, **4579 have complete Lean proofs**, **21
depend on available arguments/cited results awaiting Lean**, and **30 depend on
an elided step in the note that has not been reconstructed here**.
A successful build does not mean that the named `sorry` obligations are proved.

The authoritative explanation and per-theorem dependency assertions are at the
top of `equational_theories/Spectrum/Catalogue.lean`. Statuses mean:

| Lean status / JSON code | Meaning |
| --- | --- |
| `complete` / `PROVED` | No `sorry`; only standard axioms and explicitly opted-in native computations |
| `proofAvailable` / `PROOF_AVAILABLE` | A proof or reported computation exists, but is not integrated into the default catalogue; the annotation explains why |
| `noteGap` / `NOTE_GAP` | An essential step is elided/unclear in the note and not reconstructed here |
| `mathematicallyOpen` / `UNKNOWN` | The note leaves the exact spectrum open; no exact theorem asserted |
| `sourceConflict` / `DISPUTED` | Source claims conflict; no theorem asserted for the disputed claim |

In particular, a reported ATP result is **not** a claim that this repository
contains its replayable certificate. Neither kind of pending proof is the same
as a mathematically open spectrum. Bounds for an open spectrum have their own
independent proof statuses. “Open” refers to the September 10, 2026 note together
with the supplements recorded here, not a survey of all subsequent mathematical work.

Import `equational_theories.Spectrum`. Build just this development with:

```sh
lake build equational_theories.Spectrum
lake env lean scripts/check_spectrum.lean
lake env lean scripts/test_spectrum_status.lean
python3 scripts/spectrum_generate.py --check
```

The scope is the original 4694 equations (order at most four), and ordinary finite
spectra. Simple and irreducible spectra and higher-order equations are outside this
development.

## Conventions and propagation

`Law.MagmaLaw.HasModel L n` means that an operation on `Fin n` satisfies `L`.
`L.spectrum` contains **positive** such orders, following `spectrum-note.pdf`.
Every law has an empty model, but zero is excluded from `spectrum`. The existing
`FullSpectrum.EqFullSpectrum` includes the empty model; `Spectrum.full_iff_equation`
connects that API to the new one.

`L.Subspectral K` means `L.spectrum ⊆ K.spectrum`. Thus a construction of a
`K`-operation from every `L`-operation gives **spec(L) ⊆ spec(K)**. This has the
same orientation as implication. Both finite-only and unrestricted variants of
all four definability relations imply this inclusion, via
`subspectral_of_definableFin`, `subspectral_of_termStructural`, etc.

`Subspectral.hasModel` and `Subspectral.hasFullSpectrum` propagate positive results
forward; `Subspectral.not_hasModel` propagates exclusions backward. Dual equations
have equal spectra. Existing definability proofs give checked equalities for
{63,73,118,125,1692}, {115,880}, {481,1496}, {883,1323,1526}, {546,556}, and
{695,887}. Every non-full equation has a Lean-checked implication/duality path to
its PDF representative; the singleton class has 1496 members.

`HasModel.mul` proves multiplicativity by transporting coordinatewise products to
`Fin (n * m)`. `HasModel.pow` supplies powers, and `hasFullSpectrum_iff_primes`
reduces full spectrum to prime orders. Singleton models are universal.

## Coverage

Every equation has a checked full-spectrum theorem or a specific small-order
exclusion:

| Result | Equations |
| --- | ---: |
| Full spectrum | 3074 |
| No two-element model | 1558 |
| Has a two-element model, no three-element model | 62 |
| Total | 4694 |

The full-spectrum proofs consist of 3068 integer linear certificates and the
existing constructions for 1482, 1523, 1682 and their duals 2125, 2132, 1885.
`scripts/check_spectrum.lean` checks every one of the 4694 declaration types and
checks that these three classes partition the original equations.

Completed exact proofs cover 3074 full spectra, 1496 singleton spectra, the dual
pair represented by 474 with spectrum `positiveExcept {2,4}`, and the dual pair
represented by 1685 with spectrum `positiveExcept {2}`, and the three central
groupoid laws represented by 168 with spectrum `squares`, and E1485/E2162 with
spectrum `squares ∪ twiceSquares`. The other established
exact formulas (51 laws after transfer) are the mod-3 spectra of 66 and 695/887,
the mod-4 spectrum of 167, sums of two squares for 546/556, and
powers of two for 895/898. The Gaussian representation for 546/556 and the
E898-to-Boolean-group reduction are specifically `noteGap`, not merely missing
formalizations of reconstructed arguments.

The [central-spectrum pass](definability_central_spectrum.md) proves the square
obstruction by explicit row/column bijections, excludes order 11 for E167 by
permutation parity, and checks recovered E1486 tables at orders 11, 13 and 21.
The [prime-order theorem](definability_weak_central_prime.md) now excludes every
odd prime order for E1485, completing its previously reported exclusions at 11
and 13. These supplement the PDF and have `complete` catalogue status. Together
with the order-11 E1486 witness they refute E1486 → E1485 in all eight variants.

The full [E1485 spectrum theorem](1485_finite_spectrum_theorem.md) now proves the
note's squares-and-twice-squares conjecture. Its Lean entry point is
`Spectrum.WeakCentralSpectrum`: rectangular coordinates give uniform translation
fibers; an exact return matching proves degree halving; finite descent gives
`n = r² * 2^m`. The theorem and its dual E2162 use only standard Lean axioms,
with no enumeration, SAT certificates, or pending obligations.

The 64 UNKNOWN laws have formal lower/upper bounds, cofinite claims where the
note establishes them, and separate conjecture metadata. There is no exact
theorem, even with `sorry`, for an UNKNOWN/question-marked formula.

`data/spectrum/catalogue.json` records one entry per equation, theorem names, exact-spectrum
status, bound formulas, conjectures, representative equalities, and proof status.
The audit checks theorem types and transitive axioms against these records.
Its `explicit_orders` field lists selected
witnesses, **not an exhaustive list of known orders**: it omits the multiplicative
closure and the consequences of general constructions and spectrum inclusions.

Useful theorem names:

```lean
Spectrum.full_492                  -- Law492.HasFullSpectrum
Spectrum.not_two_677               -- ¬ Law677.HasModel 2
Spectrum.not_three_1485            -- ¬ Law1485.HasModel 3
Spectrum.singleton_7              -- Law7.spectrum = {1}
Spectrum.spectrum_two              -- Law2.spectrum = {1}
Spectrum.spectrum_1685             -- positive orders other than 2
Spectrum.model_63_7                -- a concrete modular model
Spectrum.Catalogue.exact_474       -- exact spectrum, complete proof
Spectrum.Catalogue.exact_168       -- square spectrum, complete proof
Spectrum.Catalogue.exact_1485      -- squares and twice-squares, complete proof
Spectrum.hasModel_1485_iff         -- exact characterization, including order zero
Spectrum.Catalogue.lower_63        -- reported finite lower bound
Spectrum.Catalogue.upper_63        -- exclusions {2,6,10}; some deferred
Spectrum.Catalogue.cofinite_63     -- Wilson/gluing obligation, deferred
```

To inspect a theorem's actual dependencies, including the source section and
missing step for every pending obligation:

```lean
import equational_theories.Spectrum
#spectrum_status Spectrum.Catalogue.exact_546
#spectrum_status Spectrum.Catalogue.upper_63
```

## Further positive results

`Spectrum.Constructions` proves the natural central-groupoid construction on
pairs, giving square orders for 167, 168, 1480, 1483, 1485, and 1486. It also proves
the note's odd-order construction for 474 and 1685 using a fixed-point-free
involution, and the four-element-core extension giving every even order at least
four for 1685. The analogous six-element-core extension for 474 and a complete
order-four exclusion prove its exact spectrum too. The extensions are defined
separately on core/core, core/new, new/core and
new/new arguments to disambiguate the overlapping conditions in the note.

`twice_square_1485` gives twice all squares. `power_two_895` and `power_two_898`
give all powers of two. `Generated.Modular` supplies 140 additional witnesses at
orders 3, 4, 5, 7, 8, 9, 11, 13, or 16 for the 45 non-full representatives of §3.1.
All these witnesses extend through products and the spectrum inclusion API.

## Proof trust and regeneration

`Basic`, `Linear`, `Finite`, `Constructions`, and `Transfer` use ordinary
kernel-checked proofs. `Generated.SmallOrder` additionally uses `native_decide`;
`Exact` inherits some of those checks. These modules contain no `sorry`.
The complete catalogue also imports explicit obligations from `NotePending.lean`
(28 pending statements) and `Generated/NoteObligations.lean` (46 finite statements).
The size-5 exclusion for E1286 is now discharged by the integrated BV proof;
the remaining 46 generated finite statements still need their formalizations.
See [spectrum_bv.md](spectrum_bv.md) for the BV infrastructure and total timings.
Each obligation has a `spectrum_pending` annotation giving its evidence category,
source section, and precise missing step. There is no redundant JSON list.

Every catalogue theorem has a `spectrum_assert` checking its actual transitive
dependency status at build time. Undocumented `sorryAx` and other unapproved
axioms fail the check. Native tactic axioms are allowed only when their owning
theorem is tagged `@[spectrum_native]`; they are not globally whitelisted.
`AxiomAudit.lean` also uses `#guard_msgs` on representative axiom lists.
The standalone audit checks the types and proof statuses of every JSON entry
against Lean, and checks the complete full/excluded partition. Import individual
constructive modules to avoid the pending-obligation modules.

The generator searches for witnesses and finite decision trees; Lean checks
every resulting certificate. Integer linear coefficients are
proved sound over every abelian group and checked by ordinary `decide`.
Order-two and order-three exclusions enumerate all 16 or 19683 multiplication
tables using `native_decide`; completeness of the entry parameterization is
proved in `Finite.lean`. A failed search for a modular model never becomes a
negative theorem.

`scripts/spectrum_negative.py` considers the implication/duality graph and 525
existing definability theorems, selects a small exclusion basis, and emits
actual Lean theorem applications in `Generated.NegativeTransfer`. It reuses the
existing representative equalities instead of duplicating all implication paths.
The original full/excluded partition now needs only **21 size-2 and 5 size-3
native checks**; the PDF's additional exclusions add **10 more size-3 checks**.
These 36 native checks, the E474 size-4 / E1286 size-5 BV proofs, and the two
E1485 prime-order exclusions, together with 31 pending larger refutations, cover
1666 individual exclusion statements. The generated finite obligations number 46;
the two formerly pending E1485 exclusions now have separate completed aliases.

For example, E63/E73/E118/E125/E1692 inherit exclusion of 2 from E1685;
E546/E556 and E898 inherit exclusion of 3 from E667. This is backward propagation
of exclusion along definability, not an implication claim between the laws.
A broader scan of 12,802 direct definability declarations also identified the
`Cover` result transferring E66 to the E880 class, removing one more size-2 check.

Timing probes on this checkout: the nine-entry size-3 native check for E1485
took about 0.3 seconds in evaluation (0.7 seconds elaboration). Two size-4 E474
`bv_decide` encodings succeeded, but the faster packed 32-bit table took about
2.7 seconds including elaboration (SAT itself about 0.25 seconds). A packed
75-bit size-5 E1286 trial timed out with a one-second solver limit. Neither
bit-vector replacement was initially retained: neither met the requested one-second
end-to-end budget. Subsequent symmetry-broken proofs now handle size 4 for E474
and size 5 for E1286 and are integrated in the default build with the user's
approval of the elaboration overhead. They take about 18–26 s and 246–276 s
to compile, respectively, plus about 34–38 s of shared squaring/encoding
infrastructure. Every SAT call still uses a one-second timeout.
The old E474 case tree is replaced, and E1286's size-five obligation is discharged.

Regenerate the certificate files and the JSON index with:

```sh
python3 scripts/spectrum_generate.py --write
```

This generator writes only spectrum files. It does not modify the definability
search or its data. `--check` verifies reproducibility without writing.

`scripts/spectrum_witnesses.py --write --timeout-ms 2000` optionally searches for
more finite witnesses (requires `z3-solver`). It also tries finite-field linear
models and existing repository tables. Z3 only selects tables; Lean checks them.
The checked-in `data/spectrum/witnesses.json` cache means ordinary regeneration
does not need Z3. Failed searches and timeouts never assert exclusions.

## Remaining work from the note

The pending proofs include the Boolean-group and Gaussian-module arguments, Mendelsohn-system existence and obstructions,
Wilson mixed-block designs and gluing, and some individual finite witnesses and
larger exclusions. Available proofs and unreconstructed note steps have separate
Lean annotations; neither is mislabeled as an UNKNOWN mathematical spectrum.

The note is a working draft. Its question-marked exact formulas remain separate
conjectures. For E1480, §3.1 includes order 3 while §3.7 excludes it; a complete
Lean native enumeration proves the exclusion, so the catalogue uses `{1} ∪ [4,18]` as the
reported finite lower bound. For E1313, §3.1 says cofiniteness is unknown while
§3.8 asserts it: the entry is marked `DISPUTED` and no cofiniteness theorem is
asserted. E883's displayed formula is a lower bound, not an equality.
