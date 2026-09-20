# Further counting certificates for high-value open cells

19 September 2026. This pass adds **36 Lean declarations covering 39 previously
open TS/fin class pairs**. The witnesses are finite, so every certificate also
refutes term-structural definability over arbitrary carriers. These are new
results beyond the preceding [234-pair pass](definability_affine_counting.md).

The preceding [upgrade audit](definability_counting_upgrades.md) found no
FO-structural upgrade and showed that every target in that earlier batch
already accepts a projection term. The present pass follows the request to
return to other high-value open cells.

## Certificates

| Method | New candidate class pairs | Generating declarations |
|---|---:|---:|
| One fixed point and a five-cycle, on six elements | 31 | 31 |
| Linear operations modulo 343 and 529 | 7 | 4 |
| A ternary relation on three elements | 1 | 1 |
| Total | 39 | 36 |

The six-element family consists of all **279,936** operations commuting with
the permutation `(1 2 3 4 5)`, which fixes `0`. All source and target laws were
checked on every variable assignment. Examples include E420 → E4268, with
eight new raw cells, and E56 → E1023. The source and target counts, selected
declarations, and closure coverage are recorded in the
[symmetry data](../data/definability_extended_symmetry_counts.json).

Over `ZMod 343`, E115 has 15 linear coefficient pairs, whereas E1038 has nine
and E1635 and E1684 each have 12. Three certificates cover those targets from
both E115 and E873. Over `ZMod 529`, E1279 has 24 linear coefficient pairs and
E640 has three; four distinct source factors suffice for that certificate.
The [linear data](../data/definability_large_linear_counts.json) contains the
actual factors. Composite moduli are valid: the argument uses a commutative
ring, without requiring a field.

The ternary-relation certificate refutes **E3265 → E310**. Among all 19,683
three-element operations, exactly 23 preserve the saved relation, 11 of those
satisfy E3265, and ten satisfy E310. Their product therefore has no term-defined
E310 companion admitting term recovery. The relation and its counts are in the
[relation data](../data/definability_finite_relation_counts.json).

[FiniteRelationCounting.lean](../equational_theories/Definability/FiniteRelationCounting.lean)
extends the existing binary-relation construction to any finite arity. An
operation preserves a relation when applying it coordinatewise to two members
produces another member. Projections preserve the relation, and composition of
preserving operations preserves it, so the general clone-family counting
theorem applies. Only the small operation family is enumerated; the product
magma itself is never enumerated.

## Board impact

| Board | New raw negatives | New class negatives | Remaining raw open | Remaining class open |
|---|---:|---:|---:|---:|
| TS/fin | 176 | 39 | 21,063 | 4,225 |
| TS/all | 176 | 42 | 23,179 | 4,726 |

The two boards use different positive equivalence classes. The arbitrary-carrier
quotient additionally lists E880 → E1038, E1635, and E1684; finite positive
equivalences absorb these into the E115 row. The same 176 raw pairs are newly
closed on both boards. The other eight boards and the
completely-open inventory are unchanged. The latter remains 32 raw pairs in
nine TS/all class rows. These counting arguments do not establish one-way
term-definability or FO-structural negatives.

## Search boundaries and trust

The ternary search tested all operation graphs and their complements, all
relations with three through six tuples, and a deterministic sample of larger
relations. Its larger run visited 1,429,609 distinct relations and found just
the E3265 → E310 candidate. The four-variable relation search tested 59,750
relations built from operation kernels and graphs of three-variable terms,
without finding an additional candidate. These exploratory searches are not
exhaustive over all higher-arity relations.

The symmetry scan also checked all 1,250,000 operations commuting with a
three-cycle and two fixed points, on five elements, without another candidate.
The scalar scan checked every prime from 211 through 503 and every proper prime
power strictly between 200 and 1,025; the successful new moduli were 343 and 529.

Every declaration has an explicit axiom guard for the three standard Lean
axioms and its single native-count computation axiom. The source identities in
the linear certificates are proved algebraically. Independent Python checkers
recompute all counts and reproduce the generated Lean text. Solver output and
search-family fingerprints are not used as proof facts.

All 36 declarations and the full Definability entry point compiled successfully.
All 24 regression tests passed. The refreshed audit checked every class rectangle
and matched all ten closure computations against the full-matrix reference;
collection and generation took 144.56 seconds. The saved source fingerprint and
all 14 generated audit outputs were checked afterward.

## Reproduction

```sh
python3 scripts/definability_finite_relation_counts_check.py
python3 scripts/definability_large_linear_counts_check.py
OPENBLAS_NUM_THREADS=2 python3 scripts/definability_extended_symmetry_counts_check.py
lake build equational_theories.Definability
python3 scripts/definability_imports.py --check
OPENBLAS_NUM_THREADS=2 python3 -m unittest discover -s scripts -p 'test_definab*.py'
OPENBLAS_NUM_THREADS=2 python3 scripts/definability_audit.py --write --date 2026-09-19 --verify-closure
```

Each of the three certificate checkers accepts `--write` to reproduce its
generated Lean files. The summary and verification results are recorded in
[the pass data](../data/definability_high_value_pass_summary.json).
