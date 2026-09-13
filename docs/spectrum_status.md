# Finite spectra

The complete catalogue is in [spectrum_catalogue.md](spectrum_catalogue.md) and
`data/spectrum.json`. All 4694 original laws are covered: **4628 exact formulas**
established in the PDF, and **66 genuinely UNKNOWN exact spectra**. Of the exact
formulas, **4574 have complete Lean proofs** and **54 have explicit proof gaps**.
A successful build does not mean that the named `sorry` obligations are proved.

Import `equational_theories.Spectrum`. Build just this development with:

```sh
lake build equational_theories.Spectrum
lake env lean scripts/check_spectrum.lean
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
represented by 1685 with spectrum `positiveExcept {2}`. The other established
exact formulas (54 laws after transfer) are the mod-3 spectra of 66 and 695/887,
the mod-4 spectrum of 167, squares for 168, sums of two squares for 546/556, and
powers of two for 895/898. Their remaining proof obligations are explicit.

The 66 UNKNOWN laws have formal lower/upper bounds, cofinite claims where the
note establishes them, and separate conjecture metadata. There is no exact
theorem, even with `sorry`, for an UNKNOWN/question-marked formula.

`data/spectrum.json` records one entry per equation, theorem names, exact-spectrum
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
Spectrum.Catalogue.exact_168       -- exact formula, deferred upper bound
Spectrum.Catalogue.lower_63        -- reported finite lower bound
Spectrum.Catalogue.upper_63        -- exclusions {2,6,10}; some deferred
Spectrum.Catalogue.cofinite_63     -- Wilson/gluing obligation, deferred
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

The constructive modules (`Basic`, `Linear`, `Finite`, `Constructions`, `Exact`,
`Transfer`, and `Generated`) have no new proof assumptions. The complete catalogue
also imports **explicit `sorry` obligations** from `NotePending.lean` and
`Generated/NoteObligations.lean`. The finite obligations are indexed in
`data/spectrum_finite_obligations.json`. The audit checks actual types and
transitive axioms for every catalogue theorem, rejects unreported `sorryAx`, and
rejects other nonstandard axioms. Import individual constructive modules to avoid
the pending-obligation modules.

The generator searches for witnesses and finite decision trees; Lean checks
every resulting certificate. Integer linear coefficients are
proved sound over every abelian group and checked by ordinary `decide`.
Order-two exclusions enumerate all 16 multiplication tables. Order-three
exclusions give complete case trees, with an explicit falsifying assignment at
every leaf. A failed search for a modular model never becomes a negative theorem.

Regenerate the certificate files and the JSON index with:

```sh
python3 scripts/spectrum_generate.py --write
```

This generator writes only spectrum files. It does not modify the definability
search or its data. `--check` verifies reproducibility without writing.

`scripts/spectrum_witnesses.py --write --timeout-ms 2000` optionally searches for
more finite witnesses (requires `z3-solver`). It also tries finite-field linear
models and existing repository tables. Z3 only selects tables; Lean checks them.
The checked-in `data/spectrum_witnesses.json` cache means ordinary regeneration
does not need Z3. Failed searches and timeouts never assert exclusions.

## Remaining work from the note

The pending proofs include Knuth's square-cardinality theorem, the Boolean-group
and Gaussian-module arguments, Mendelsohn-system existence and obstructions,
Wilson mixed-block designs and gluing, and some individual finite witnesses and
larger exclusions. These are precisely specified proof obligations, not UNKNOWN
mathematical spectra.

The note is a working draft. Its question-marked exact formulas remain separate
conjectures. For E1480, §3.1 includes order 3 while §3.7 excludes it; a complete
Lean case tree proves the exclusion, so the catalogue uses `{1} ∪ [4,18]` as the
reported finite lower bound. For E1313, §3.1 says cofiniteness is unknown while
§3.8 asserts it: the entry is marked `DISPUTED` and no cofiniteness theorem is
asserted. E883's displayed formula is a lower bound, not an equality.
