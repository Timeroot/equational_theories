# Finite clone-family counts: a second pass on partially resolved cells

The 18 September 2026 pass following the
[broader linear/table count pass](definability_partial_counting.md) supplies
**158 Lean declarations covering 234 previously open TS/fin class cells**.
Every obstruction has a finite witness, so it refutes term-structural
recoverability over both finite and arbitrary magmas.

| Board | Newly refuted equation pairs | Newly refuted class cells | Remaining equation pairs | Remaining class cells |
|---|---:|---:|---:|---:|
| TS/fin | 1,234 | 234 | 21,239 | 4,264 |
| TS/all | 1,234 | 242 | 23,355 | 4,768 |

The class counts differ because the two boards have different positive
equivalences. No positive classes merge. The completely-open inventory stays
at **32 equation pairs / 9 class rows**; these are improvements to partially
resolved cases. No additional one-way term or first-order negative is claimed.

## The common argument

Fix a finite carrier A and a finite, injectively parametrized family of binary
operations on A. Suppose that family contains both projections and is closed
under composition. Take the product of all its operations satisfying the source
law, one coordinate for each source parameter. The product satisfies the source
law. Every term-defined target operation still acts coordinatewise within the
family, and each coordinate satisfies the target law.

If two coordinates acquire the same target parameter, every recovery term
preserves equality between those coordinates. On constant input tuples this
forces the original source operations to agree. Injectivity of the
parametrization then forces the source parameters to be equal. Thus term
recovery would inject the source parameters into the target parameters.
Having more sources than targets is impossible.

[CloneFamilyCounting.lean](../equational_theories/Definability/CloneFamilyCounting.lean)
formalizes this as `not_termStructuralFromFin_of_cloneFamily_count`. Terms may
depend on the entire product magma. No uniform term across separate source
magmas is assumed, and no product carrier or product clone is enumerated.

## Families and certificates

| Family | Search range | Candidate class cells | Generating declarations |
|---|---|---:|---:|
| Scalar affine operations | `ZMod n`, 2 ≤ n ≤ 200 | 65 | 41 |
| Matrix affine operations | two-dimensional spaces over F₂ and F₃ | 10 | 10 |
| Cyclic-translation-equivariant operations | orders 4–7 | 32 | 22 |
| Prescribed permutation or unary-map symmetries | carriers of sizes 3–5 | 55 | 46 |
| Preserved binary relations | one or two relations on three points | 72 | 39 |

The generating declarations cover all candidate cells by the existing positive
closure. The saved data record these reductions and the source fingerprint
before the pass. All declarations are imported through
[AffineCountingCatalogue.lean](../equational_theories/Definability/AffineCountingCatalogue.lean).

**Scalar affine operations** have the form `a*x + b*y + c`.
[AffineCounting.lean](../equational_theories/Definability/AffineCounting.lean)
extends the earlier linear-product argument to triples. The constant term is
recovered at `(0,0)`, then the linear coefficients at `(1,0)` and `(0,1)`.
For example, over `ZMod 59` there are 177 affine E115 operations but only 119
E1036 triples passing the necessary zero/basis tests. This refutes E115 → E1036.
The two largest certificates count whole source families via
[AffineFamilyCounting.lean](../equational_theories/Definability/AffineFamilyCounting.lean),
avoiding long explicit arrays of factors.

**Matrix affine operations** allow two independent linear maps instead of two
scalars. [MatrixAffineCounting.lean](../equational_theories/Definability/MatrixAffineCounting.lean)
proves injectivity and composition algebraically. There are 1,024 affine binary
operations on F₂² and 59,049 on F₃². For E861 → E11, their counts on F₂² are
29 versus 17. On F₃², E633 → E1239 has counts 73 versus 55. These distinctions
were missed by the scalar counts.

**Cyclic translations** give the family `x + f(y - x)` for arbitrary functions
f. Both projections belong to the family, and composition corresponds to
`d ↦ g(d) + f(h(d) - g(d))`.
[TranslationCounting.lean](../equational_theories/Definability/TranslationCounting.lean)
proves these facts over `ZMod n`. At order six there are 12 compatible E690
operations but only 11 E65 operations. E690 → E65 is therefore refuted; the
imported generators also settle several neighboring target classes. The order
seven pass checks all 823,543 parameter functions.

**Unary symmetries** need not be invertible. Operations commuting with a fixed
unary map form a clone family, as proved in
[UnaryMapCounting.lean](../equational_theories/Definability/UnaryMapCounting.lean).
For example, the map `0 ↦ 0, 1 ↦ 0, 2 ↦ 1` admits five compatible E1042
operations but only four E1253 operations. Larger permutation families have
compact parametrizations in
[FixedPointCycleCounting.lean](../equational_theories/Definability/FixedPointCycleCounting.lean)
and [FreeOrbitCounting.lean](../equational_theories/Definability/FreeOrbitCounting.lean).
These respectively describe a cyclic orbit plus a fixed point, and two free
orbits of an involution. The latter has 65,536 compatible operations on four
points, far fewer than all `4^16` operation tables.

The E1253 → E843 candidate is also now certified: the permutation fixing
0 and 1 and swapping 2 and 3 gives counts 239 versus 235. The general
[fixed-points/orbit parametrization](../equational_theories/Definability/FixedPointsOrbitCounting.lean)
handles that family. E1051 → E1063 instead uses two unary maps simultaneously,
the constant maps to 0 and 1. Its 48 source operations outnumber 44 targets.
[UnaryMapFamilyCounting.lean](../equational_theories/Definability/UnaryMapFamilyCounting.lean)
formalizes preservation of the whole map family. No saved candidate in this
pass remains pending.

**Binary relations** provide a further family without assuming linearity or a
symmetry. An operation preserves R when two input pairs in R always produce
an output pair in R. Both projections preserve R, and composition preserves
this property. The same is true for any fixed list of relations.
[RelationCounting.lean](../equational_theories/Definability/RelationCounting.lean)
and [RelationFamilyCounting.lean](../equational_theories/Definability/RelationFamilyCounting.lean)
instantiate the general counting theorem with these families.

All 512 binary relations on three points were tested. They determine 260
distinct compatible-operation families and give 48 additional candidate cells.
Intersections of two such families give another 24 cells; 39 generating
certificates cover all 72. For example, E1263 → E843 has five compatible source
operations versus four targets under relation codes 79 and 161. Code bits use
index `3*x+y`; the saved data and checker fully specify the relations.
The follow-up search through triples of relations reaches 36,604 distinct
compatible-operation families and adds no further cell in the remaining inventory. These finite search bounds make no claim about all possible
clone invariants or larger carriers.

## Checks and trust

The core injection argument and the family-closure proofs use only standard
Lean axioms. Every final declaration has an explicit transitive axiom guard.
Of the 158 declarations, **18 use only standard axioms** and **140 also use one
explicitly guarded native-computation axiom**. The native checks are finite
counting computations; no external solver result is assumed.

Python independently reproduces the scalar coefficient triples and the complete
small-carrier operation tables. It checks every variable assignment for every
table surviving earlier assignments; a table is discarded only after a concrete
failure. The symmetry table generator uses pair-orbit enumeration independently
of the Lean parametrizations. Source and target counts, uniqueness, and generated
Lean text are checked. The 24-test regression suite includes comparisons of
affine coefficient counting with full evaluation over both fields and composite
rings.

The full Definability build passed with every certificate imported (16,692
incremental jobs). All five independent certificate checkers and all 24 tests
passed. The final board audit checked all ten closures against the full-matrix
reference and regenerated all 14 artifacts in 202.40 seconds. The other eight
boards are unchanged. The source fingerprint and bounded-search summaries are
saved in [the pass summary](../data/definability_counting_pass_summary.json).

The executable certificate checks are:

```sh
python3 scripts/definability_affine_counts_check.py
OPENBLAS_NUM_THREADS=2 python3 scripts/definability_matrix_counts_check.py
OPENBLAS_NUM_THREADS=2 python3 scripts/definability_translation_counts_check.py
OPENBLAS_NUM_THREADS=2 python3 scripts/definability_symmetry_counts_check.py
OPENBLAS_NUM_THREADS=2 python3 scripts/definability_relation_counts_check.py
lake build equational_theories.Definability
python3 scripts/definability_imports.py --check
OPENBLAS_NUM_THREADS=2 python3 -m unittest discover -s scripts -p 'test_definab*.py'
OPENBLAS_NUM_THREADS=2 python3 scripts/definability_audit.py --write --date 2026-09-18 --verify-closure
```

Each certificate checker accepts `--write` to regenerate its Lean files.
The data are in `data/definability_{affine,matrix,translation,symmetry,relation}_counts.json`.
The scalar search remains available through
`python3 scripts/definability_affine_counts.py --max-modulus 200`;
use `--pair SOURCE TARGET` to rediscover an already settled pair.

## Stronger-negative audit

The [19 September upgrade audit](definability_counting_upgrades.md) finds that
all 234 target laws accept a projection, so none of these pairs can become a
one-way term-definability negative. FO structurality remains open for 203 of
the pairs on finite carriers and 226 on arbitrary carriers; the automorphism
searches recorded there found no stronger negative.
