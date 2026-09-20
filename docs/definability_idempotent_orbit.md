# An idempotent orbit obstructs E1485

17 September 2026. **E1483 → E1485 is negative for term-definability on finite
carriers**, hence also for term-definability on arbitrary carriers and both
term-structural variants. The four FO variants remain open for this pair.

The completely-open inventory falls **48 → 44 raw pairs**, or **13 → 12 class
rows**. The removed rectangle is `{1483,2163} × {1485,2162}`. There are no new
positive equivalences. This result does not address the separate reported
order-11/order-13 exclusions for E1485.

The proof is in [IdempotentOrbit.lean](../equational_theories/Definability/IdempotentOrbit.lean),
with its finite refutation in
[Generated/Idempotent1485.lean](../equational_theories/Definability/Generated/Idempotent1485.lean).
The conclusion has an axiom guard permitting only `propext`, `Classical.choice`,
and `Quot.sound`.

## The invariant

The source is the following operation on `{0,…,7}`:

```
0 3 1 0 3 1 4 4
2 1 5 4 5 1 4 2
7 0 2 0 7 4 4 2
4 1 1 4 1 1 4 4
7 3 5 0 6 1 4 2
2 4 2 4 2 4 4 2
4 4 4 4 4 4 4 4
0 0 4 0 0 4 4 4
```

Lean checks E1483 directly on this table. It also checks that the permutation
`σ=(0 1 2)(3 5 7)`, fixing `4` and `6`, commutes with the operation.
The element `0` is idempotent. Every binary term operation `f` therefore has

```
f(0,0) = 0
f(σx,σy) = σ(f(x,y)).
```

Both projections have these properties, and composition with the source
preserves them. This is the entire clone invariant used in the proof. In
particular, `1` and `2` remain idempotent as well.

No operation on this eight-element carrier can satisfy E1485 together with
these two conditions. Thus even a forward term defining an E1485 operation
is impossible; no recovery assumption is needed.

## The finite proof

The certificate uses E1485 and its already-proved dual:

```
(y*x)*(x*(z*y)) = x
((y*z)*x)*(x*y) = x.
```

Starting with `f(0,0)=0`, it propagates assigned cells around the three-cycle.
Whenever a ground law instance has known inner products, its outer product
is forced. A conflicting value closes the branch. Otherwise the proof splits
an unassigned table entry into its eight possible values.

The complete tree has **441 nodes, 55 splits, and maximum split depth six**.
The count includes 48 immediate orbit contradictions in addition to the 393
nodes entered by the recursive search. Each leaf exhibits a specific
contradiction; the proof covers all eight children of every split.

The Python program only chooses the tree and emits ordinary Lean proofs.
Lean checks every propagation, every equation instance, every split, and every
contradiction. The proof does not use `native_decide`, `bv_decide`, a SAT axiom,
or an unverified report that a search found no model. Its closed numeric
checks use kernel `decide`.

This is a finite obstruction for this particular permutation and idempotent
orbit. It does not assert a general cardinality bound for idempotents in
weak central groupoids.

## Reproduction

```sh
python3 scripts/definability_idempotent_check.py --check
lake build equational_theories.Definability
OPENBLAS_NUM_THREADS=2 python3 scripts/definability_audit.py --write --date 2026-09-17 --verify-closure
OPENBLAS_NUM_THREADS=2 python3 -m unittest discover -s scripts -p 'test_definab*.py'
python3 scripts/definability_imports.py --check
```

Use `--write` to regenerate the finite Lean proof. The generator checks the
displayed source table, reconstructs the entire refutation, and needs no
historical model bank or external solver. The board obtains the negative
from the imported Lean declaration, not from this document or Python output.

The generated finite proof built in about 61 seconds. The full imported
Definability build passed (16,648 jobs), as did all 21 regression tests and
the import check (6,581 direct imports; 13,346 reachable local modules).
Audit regeneration passed in 195.23 seconds, including agreement of all ten
negative propagations with full-matrix recomputation. Exactly four raw statuses
changed on each of TD/all, TD/fin, TS/all, and TS/fin; the other boards were unchanged.
