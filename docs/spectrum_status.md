# Finite spectra

The complete catalogue is in [spectrum_catalogue.md](spectrum_catalogue.md) and
`data/spectrum/catalogue.json`. All 4694 original laws are covered: **4646 exact
formulas from the PDF and proved supplements**, and **48 exact spectra still UNKNOWN
in this development**. **All 4646 exact formulas now have complete Lean proofs.**
Some bounds and cofiniteness claims for the 48 unknown spectra still have explicit
pending obligations; their proof statuses are audited independently.

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
spectrum `squares ∪ twiceSquares`, and the four laws represented by E66 with
spectrum `residues 3 {0,1} {6}`, the ten laws represented by E695/E887 with
spectrum `residues 3 {1,2} {7}`, and the 24 Gaussian laws represented by E546/E556
with spectrum `sumTwoSquares`, the twelve laws represented by E895/E898 with
spectrum `powersTwo`, and E167 with spectrum `residues 4 {0,1} ∅`.
The [Boolean-group and bookend proofs](powers_two_and_bookend_spectra.md)
completed thirteen exact-spectrum entries. The formerly missing
E898-to-Boolean-group reduction is now replayed in Lean, and all thirteen
entries use only standard axioms, with no native checks.

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

The [E66 spectrum theorem](66_finite_spectrum_theorem.md) constructs every allowed
order using idempotent Latin squares and Bose constructions. The squaring twist
reduces necessity to a directed-pair count and a checked six-point SAT certificate.
E66, E170, E177, and E281 now have complete exact-spectrum proofs.

The [E695/E887 spectrum theorem](695_finite_spectrum_theorem.md) adjoins or removes
the identity of a semisymmetric loop, reducing the spectrum to the completed
Mendelsohn result. The [Gaussian spectrum theorem](546_gaussian_spectrum_theorem.md)
reconstructs an abelian group and the full Gaussian-integer module structure from
E546, including on infinite carriers. A sign argument on characteristic Sylow
subgroups proves the finite cardinality obstruction. This closes the former
representation gap for E546, E949, and their entire 24-law spectrum family.

The [quasigroup spectrum proofs](quasigroup_spectra.md) settle ten more laws:
E115/E873/E880 and their duals have spectrum `positiveExcept {2,6}`, and
E481/E1496 and their duals have spectrum `positiveExcept {3,6}`. Explicit
cyclic seeds, products, and invariant-subset extensions give all allowed orders.
The order-six exclusions use checked BV/LRAT certificates.

E1719 and its dual E1888 have spectrum `positiveExcept {2}`. The
[complete proof](1719_finite_spectrum_theorem.md) is formalized through a Bose
construction with two shared points and a semisymmetric twist. The exact theorem
uses only Lean's standard axioms, with no native-check dependencies.

E1489 and its dual E2098 have spectrum `positiveExcept {2,4}`. The
[complete proof](1489_finite_spectrum_theorem.md) constructs idempotent models
at every allowed order, using explicit seven-group transversal designs with
two groups truncated. The existence theorem and all finite seed checks use
only standard Lean axioms; the exclusions reuse two native-checked certificates.

E1480 and its dual E2089 have spectrum `positiveExcept {2,3}`. The
[complete proof](1480_finite_spectrum_theorem.md) uses four-point and five-point
cores with indexed pairs, giving every order `4+2m` and `5+2m`. The construction
identities hold on arbitrary index types, using ordinary kernel proofs.

The 48 UNKNOWN laws have formal lower/upper bounds, cofinite claims where the
note establishes them, and separate conjecture metadata. Of their 96 lower and
upper bounds, 76 have complete Lean proofs. E1719/E1888, E1489/E2098, and
E1480/E2089 are now exact. There is no exact theorem, even with `sorry`, for an
UNKNOWN/question-marked formula.

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

`TwistedGaussian.lean` proves `odd_sums_467`: every odd sum of two squares is
an E467 model order. On a module with a rotation `J² = -1`, use
`x ◇ y = -(x + J x)/2 + J y`. The identity follows by expansion. The standard
sum-of-two-squares factorization `n = a²*b` supplies the models: a rotation on
`(ZMod a)²` and a square root of minus one in `ZMod b`. Both factors have odd
order, so division by two is defined. Products give the desired cardinality.
This proof uses no native checks or pending obligations.

`QuasigroupBounds.lean` also completes the loop-family lower bounds for E667
and E883, and the Mendelsohn-family lower bound for E1719. Their general
constructions likewise have no native dependencies. The finite witnesses in
`Generated.NoteWitnesses` now include E1480 at order 10 and E1489 at orders 6
and 18; the latter is the product of the order-3 and order-6 tables.

## Proof trust and regeneration

`Basic`, `Linear`, `Finite`, `Constructions`, and `Transfer` use ordinary
kernel-checked proofs. `Generated.SmallOrder` additionally uses `native_decide`;
`Exact` inherits some of those checks. These modules contain no `sorry`.
The complete catalogue also imports explicit obligations from `NotePending.lean`
(11 pending statements) and `Generated/NoteObligations.lean` (5 finite exclusions;
no finite witness obligations remain). The recent passes completed four infinite-family
obligations, 24 finite exclusions, seven finite witnesses, and the exact E1719
and E1489 spectra, followed by the exact E1480 spectrum. E1489's former
cofiniteness obligation is also proved. The general E1480 construction discharges
the final seven missing finite witnesses. The remaining exclusion orders are
E63/10, E670/7, E704/9, E1279/9, and E1483/7.
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
These 36 native checks, the E474 size-4 / E1286 size-5 BV proofs, the
E481/E873 order-six certificates, the two E1485 prime-order exclusions, and
24 further checked certificates in `SmallCertificates.lean`, together with five
pending larger refutations, cover 1666 individual exclusion statements.

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

The pending proofs concern bounds and cofiniteness for unknown exact spectra:
the `k²+2` construction for E1486, Wilson mixed-block designs and gluing,
and the remaining individual finite witnesses and larger exclusions. Available proofs and unreconstructed note steps have separate
Lean annotations; neither is mislabeled as an UNKNOWN mathematical spectrum.

The note is a working draft. Its question-marked exact formulas remain separate
conjectures. For E1480, §3.1 includes order 3 while §3.7 excludes it; a complete
Lean native enumeration proves the exclusion, so the catalogue uses `{1} ∪ [4,18]` as the
reported finite lower bound. For E1313, §3.1 says cofiniteness is unknown while
§3.8 asserts it: the entry is marked `DISPUTED` and no cofiniteness theorem is
asserted. E883's displayed formula is a lower bound, not an equality.
