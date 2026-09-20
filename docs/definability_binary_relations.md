# Compatible relations obstruct E1482

17 September 2026. **E1480 → E1482 is negative for term-definability on finite
carriers**, hence also for term-definability on arbitrary carriers and both
term-structural variants. Its four FO variants remain open.

This removes `{1480,2089} × {1482,2125}` from the completely-open inventory:
**44 → 40 raw pairs**, or **12 → 11 class rows**. No positive classes merge.

The proof is in
[BinaryRelationObstruction.lean](../equational_theories/Definability/BinaryRelationObstruction.lean),
with its finite certificate in
[Generated/Relation1482.lean](../equational_theories/Definability/Generated/Relation1482.lean).
The conclusion has an axiom guard listing only `propext`, `Classical.choice`,
and `Quot.sound`.

## The source and its relations

The source operation on `{0,…,7}` is

```
2 6 6 6 2 3 6 1
7 3 7 7 2 3 0 7
4 4 0 4 4 3 0 1
5 5 5 1 2 5 0 1
4 4 0 4 4 3 0 1
5 5 5 1 2 5 0 1
2 6 6 6 2 3 6 1
7 3 7 7 2 3 0 7
```

Lean checks E1480 on this table. It also checks preservation of each relation
below: if `(a,b)` and `(c,d)` belong to the relation, then so does
`(a*c,b*d)`.

| Relation | Pairs |
|---|---|
| R₀ | (7,7) |
| R₁ | (4,6) |
| R₂ | (5,7) |
| R₃ | (4,1), (4,3), (4,5), (4,7) |
| R₄ | (0,3), (2,1), (4,7), (6,5) |
| R₅ | (0,0), (1,3), (2,2), (3,1), (4,4), (5,7), (6,6), (7,5) |
| R₆ | (0,1), (1,0), (2,3), (3,2), (4,5), (5,4), (6,7), (7,6) |
| R₇ | (1,0), (1,4), (3,2), (3,4), (5,4), (7,0), (7,2), (7,4), (7,6) |

Every binary term preserves each relation. The projections do, and composing
two preserving operations with the source operation preserves it again.
This gives a clone invariant without computing the source's full clone.

No operation on the carrier both preserves these eight relations and
satisfies E1482. Therefore no binary term of the source can define an E1482
operation, even when the term is allowed to depend on the source model.

## The finite certificate

The search uses all 64 ground instances of

```
(y*x)*(x*(y*y)) = x
```

and all 244 preservation instances for the eight relations. Known inner
products force an outer product through a law instance. Known coordinates
in a relation can force another product or show a contradiction. Otherwise
the search splits a table entry into all eight possible values.

The complete tree has **665 nodes and 83 splits**, with maximum split depth
seven. Its Lean translation uses ordinary equation rewrites, complete finite
case splits, and kernel `decide` for implications about the displayed finite
relations. It uses no `native_decide`, `bv_decide`, solver axiom, or pending
assumption.

The relations were found by testing subalgebras of the square of the source.
The final proof needs only their displayed membership tables and their checked
closure. It does not trust the discovery procedure or a report of solver
unsatisfiability.

## Reproduction

```sh
python3 scripts/definability_relation_check.py --check
lake build equational_theories.Definability
OPENBLAS_NUM_THREADS=2 python3 scripts/definability_audit.py --write --date 2026-09-17 --verify-closure
OPENBLAS_NUM_THREADS=2 python3 -m unittest discover -s scripts -p 'test_definab*.py'
python3 scripts/definability_imports.py --check
```

Use `--write` to regenerate the finite Lean proof. The checker verifies the
source and all eight relations and reconstructs the entire tree, without an
external solver or a historical model bank. The board extracts the theorem
from the imported Lean source; this document and the Python search do not
provide board facts.

The finite proof built in about 62 seconds, and the source/invariant wrapper
in 19 seconds. The full imported Definability build passed (16,650 jobs), as
did all 21 regression tests and the import check (6,582 direct imports;
13,348 reachable local modules). Audit regeneration passed in 185.88 seconds,
including agreement of all ten negative propagations with full-matrix
recomputation. Exactly four raw statuses changed on each of TD/all, TD/fin,
TS/all, and TS/fin; the other boards were unchanged.
