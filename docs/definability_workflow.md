# Working on definability

The [open-cell audit](definability_open_audit.md) gives the complete remaining
inventory, evidence labels, finite/all distinctions, and regeneration commands.
The [completely-open inventory](definability_open/completely_open.md) isolates
pairs unresolved in all eight definability variants. For the independent
[spectrum-obstruction recheck](definability_spectrum_check.md), run
`lake build equational_theories.Spectrum` followed by
`OPENBLAS_NUM_THREADS=2 python3 scripts/spectrum_definability_check.py`.
The [central-spectrum pass](definability_central_spectrum.md) records the checked
E1486 separations. The [prime-order theorem](definability_weak_central_prime.md)
now completes the E1485 exclusion without relying on the reported searches.
The dated [status report](definability_status.md) is a historical snapshot, not
the current open-question list. The old `defwork/` search workspace is not part
of this checkout. The maintained reporting commands are:

```sh
lake build equational_theories.Definability
OPENBLAS_NUM_THREADS=2 python3 scripts/definable.py --query 56 50 --query 440 414
OPENBLAS_NUM_THREADS=2 python3 scripts/definable.py --open structural all --limit 20
OPENBLAS_NUM_THREADS=2 python3 scripts/definable.py --verify-closure
python3 scripts/test_definable.py
python3 scripts/definability_imports.py --check
```

Pairs are printed **source → target**; Lean writes the target first:
`Law50.StructuralFrom Law56`. Queries show all five relations in both the
arbitrary-carrier and finite-carrier flavours. Open lists use one representative
per positive-equivalence class. Use `--verbose` to see individual certificate
rectangles; the default report omits hundreds of repetitive family lines.

## What counts as a proof

The board is source-derived bookkeeping, not a theorem prover. It extracts
declarations and computes consequences of the proved relation hierarchy. It now
rejects definability declarations and certificate families that are absent from
the import closure of `Definability.lean`. This prevents an unimported scratch
proof from silently improving coverage, but **reachability does not establish
that a proof compiles**. Run the Lean build as well. An `OPEN` cell means not
settled by the current extracted facts, not necessarily unknown in mathematics.

Structural definability means mutual, parameter-free first-order definability
of the operations. Equality of automorphism groups is a necessary invariant,
not the definition on arbitrary infinite structures. Term-structural
definability asks for mutual term definitions; the terms in the definition may
depend on the source magma. A single uniform witness, when available, is stronger.

## FO compactness and column repair: 21 September 2026

The [compactness counting pass](definability_fo_compactness_counting.md) proves
that unrestricted FO-structural interpretation forces a uniform multiplicative
bound on finite model counts. Explicit row and diagonal counts refute several
priority arrows, including E8 → E3, E8 → E326, E11 → E109, and E3253 → E8.
The final straight-line counting argument completes the unrestricted E1 source
row. There are 35 negative generators in this pass. These are arbitrary-carrier
negatives; the finite FO variants remain open.

The [cube-column repair](definability_cube_column_repair.md) supplies five
reversible quantifier-free constructions into E108, valid on arbitrary carriers.
Together these FO results reduce the unrestricted equivalence inventory from
1,094 to 1,001 unresolved class pairs, closing 638 unrestricted and 184 finite
FO cells. The finite FO inventory still has 1,049 unresolved equivalence pairs.

## Confluence and endomorphisms: 21 September 2026

The [confluence pass](definability_confluence_recovery.md) proves nine more
unrestricted term-structural negatives, settling 60 directed raw cells. Four
close equivalence questions: E115 → E880, E477 → E1492, E680 → E1695, and
E481 → E1496. This leaves **28** unrestricted equivalence questions; the finite
classification remains complete at 716 classes. These confluence results add
no FO or one-way term-definability claim.

## Unary-cycle separations: 21 September 2026

The [unary-cycle pass](definability_unary_cycles.md) refutes E65 → E1491 and
E1648 → E124 for unrestricted term-structural interpretation. Every unary term
of either target is a permutation; the countable source witnesses have
noninjective square maps. Both conclusions have standard-axiom guards.
This leaves 32 unrestricted equivalence questions; the finite classification
remains complete with exactly 716 classes.

## Finite clone-family counting: 18 September 2026

The [follow-up counting pass](definability_affine_counting.md) adds 158 guarded
Lean declarations covering 234 finite term-structural class cells. Scalar and
matrix affine families, cyclic translations, unary symmetries, and preserved
binary relations yield 1,234
newly refuted equation pairs on each TS board. The completely-open inventory
remains 32 pairs / nine rows. All finite counterexamples also refute the
arbitrary-carrier claim.

## Counting partially resolved cells: 18 September 2026

The [broader counting pass](definability_partial_counting.md) supplies 137
linear-product certificates and 17 certificates counting every three-element
operation. It addresses open TS/fin cells outside the completely-open shortlist.
This closes 978 raw TS/fin pairs (191 class cells) and 902 raw TS/all pairs
(192 class cells), without changing the nine completely-open rows.
The general operation-count theorem handles terms chosen separately for each
source magma. Certificate checkers independently reproduce the counts and the
Lean files; the full Lean build and board audit complete validation.

## Residual candidate families: 18 September 2026

The [subalgebra obstruction](definability_subsets.md) now refutes E3352 → E4408
in TS/fin and TS/all. This closes the four raw pairs
`{3352,4164} → {4408,4479}`, reducing the completely-open inventory from
**36 raw / 10 class rows** to **32 raw / 9 class rows**. Reproduce the source,
relations, and finite coverage check with
`python3 scripts/definability_subset_check.py --check`, then build
`equational_theories.Definability.SubsetObstruction`.

The [residual candidate report](definability_residual_candidates.md) also records
kernel-checked exclusions for three families with arbitrarily many square
iterations and for every unary postprocessor on the E3352 model. Those narrower
certificates remain useful for the unresolved term-construction questions.

## Weak central prime orders: 17 September 2026

[WeakCentralCardinality.lean](../equational_theories/Spectrum/WeakCentralCardinality.lean)
proves that an E1485 model of prime order has order two. Sharp neighbors give
rectangular decompositions, so every translation rank divides the order.
At prime order every row is constant or bijective, and the identity permits
at most one row of each kind. The existing eleven-element E1486 witness then
refutes E1486 → E1485 in D/fin, hence all eight variants. This reduces the
completely-open table from **40 raw / 11 class rows** to **36 raw / 10 class rows**.
The exclusions at 11 and 13 and their formerly pending consequence now have
completed proofs. See [the argument and checks](definability_weak_central_prime.md).
The remaining reverse direction E1485 → E1483 has a reproducible
[twisted Boolean search](definability_weak_central_reverse.md), with its limits
explicitly separated from the checked board results.

## Compatible binary relations: 17 September 2026

[BinaryRelationObstruction.lean](../equational_theories/Definability/BinaryRelationObstruction.lean)
refutes E1480 → E1482 in TD/fin, hence TD/all and both TS variants. Every binary
term of an eight-element E1480 model preserves eight relations on pairs of
elements. A complete finite case proof excludes E1482 under this invariant.
The conclusion has a standard-axiom guard. This reduces the completely-open table
from **44 raw / 12 class rows** to **40 raw / 11 class rows**.
See [the relations, proof, and reproduction instructions](definability_binary_relations.md).

## Idempotent orbit obstruction: 17 September 2026

[IdempotentOrbit.lean](../equational_theories/Definability/IdempotentOrbit.lean)
refutes E1483 → E1485 in TD/fin, hence TD/all and both TS variants. Every term
of the eight-element witness preserves its idempotent at `0` and its order-three
automorphism. A complete finite case proof excludes E1485 under those conditions.
The conclusion has a standard-axiom guard. This reduces the completely-open table
from **48 raw / 13 class rows** to **44 raw / 12 class rows**.
See [the proof and reproduction instructions](definability_idempotent_orbit.md).

## Twisted finite recovery obstructions: 17 September 2026

[TwistedRecovery.lean](../equational_theories/Definability/TwistedRecovery.lean)
proves finite term-structural negatives E1076 → E1313, E1516 → E1489, and
E1685 → E3548. A shared family of twisted operations is closed under terms;
every target companion loses its twist and preserves a section that the source
does not. The three conclusions have standard-axiom guards, with all finite
checks performed by kernel `decide`.
See [the construction and board impact](definability_twisted_recovery.md).
The independent checker `python3 scripts/definability_twisted_check.py`
evaluates the full laws and all family members without the historical model bank.

## Counting and integrality: 16 September 2026

The [counting-and-integrality guide](definability_counting_recovery.md) explains
the next pass. `LinearCounting.lean` turns a surplus of linear source operations
over a finite ring into a finite term-recovery obstruction by taking a product.
Ten small certificates use this shared argument; finite equivalences avoid four
redundant generators. `IntegralRecovery.lean` supplies four E467 obstructions:
the source has a non-integral coefficient, whereas every linear target has
algebraic-integer coefficients. Every new conclusion has an axiom guard.

For reproducible candidate discovery, run
`python3 scripts/definability_linear_counts.py --max-modulus 100`, or specify
`--pair SOURCE TARGET`. This checks finite coefficient counts, not the full
product magmas. It writes no facts and never treats an unsuccessful search as
a positive result. Run all 20 bookkeeping/search tests with
`python3 -m unittest discover -s scripts -p 'test_definab*.py'`.

## Gaussian recovery obstructions: 16 September 2026

The [Gaussian-integer guide](definability_gaussian_recovery.md) gives three
arbitrary-carrier term-structural negatives: E1496 cannot term-structurally
define E1113, E680, or E1682. A single infinite source `i(x−y)` forces every
term-defined target into one of three families closed under terms, none of
which contains the source. `GaussianRecovery.lean` shares the forward-linearity
and recovery arguments; each target contributes only its coefficient check.
All three conclusions have standard-axiom guards. These are not finite or
FO obstructions, and removing their consequences from the completely-open
inventory does not settle the other seven variants.

## Reversible companions and cleanup: 16 September 2026

The [reversible-companion guide](definability_reversible.md) explains the new
shared inverse machinery, six finite-to-arbitrary structural upgrades, and the
replacement of large guard replays by normal forms. Start with
`Reversible.lean` for reusable infrastructure and `SquareSwap.lean` for the
source-law arguments. The historical module paths and theorem names remain
available; `Definability.lean`'s import list is unchanged in this pass.

The subsequent [argument-swap pass](definability_argument_swap.md) supplies
47 more arbitrary-carrier structural generators. Its proof-recovery tactic
reuses the unrestricted target-law part of old finite certificates and replaces
only the recovery argument. All 47 conclusions have axiom checks. The new
catalogue gathers 38 existing proof imports, preserving every old module.

## Two new structural constructions: 14 September 2026

[RowCycle.lean](../equational_theories/Definability/RowCycle.lean) proves
`Equation50_structuralFrom_Equation56_rowCycle` and
`Equation414_structuralFrom_Equation440_rowCycle` over **all** magmas. Both
directions are quantifier-free definitions, with explicit recovery of the source
operation. Their axiom lists are guarded: only `propext`, `Classical.choice`, and
`Quot.sound`; no `sorry`, ATP certificate, or native computation.

For E56, put `d(x) = x*x` and `c(x) = x*d(x)`. The law says every `c(y)` is a
right identity. Thus the row at `x` has a distinguished cycle
`x → d(x) → c(x) → x`, either three distinct points or one point. Postcompose
the whole row with that cycle. The new operation satisfies

```
x □ x = c(x),   x □ c(y) = d(x),   x □ d(x) = x.
```

These give E50: `x □ (x □ (y □ y)) = x`. Recover `c(x)` and `d(x)` using
the first two identities, then undo the output permutation. Off-cycle outputs
are unchanged, so no part of the original operation is forgotten.

For E440, the distinguished orbit is
`x → p(x) → q(x) → r(x) → x`, where every `r(y)` is a right identity.
Postcompose each row with its half-turn, swapping `x` with `q(x)` and `p(x)`
with `r(x)`. The orbit may have period two or one; the proof includes those
degenerate cases. The new row reverses the orbit and yields E414. Its diagonal
and the next two iterates recover `r(x), q(x), p(x)`, after which the same
half-turn recovers the original row.

These resolve structural questions, **not** the stronger term-structural ones,
which remain open on the board. Neither construction assumes bijective rows.

Through existing closure, the two declarations settle 14 reduced structural
cells over all magmas (42 raw pairs) and 17 reduced finite structural cells
(54 raw pairs). The two flavours overlap and should not be added as independent
mathematical discoveries. The new proof module compiled in 3.2 seconds with
dependencies cached (about 4.8 seconds including standalone command overhead).
The final incremental Definability build took 72.2 seconds including Lake's
dependency planning; this is not a cold-project build measurement.

## Keeping the entry point and closure small

`scripts/definability_imports.py --write` removes redundant entry-point import
edges while checking that every reachable local module is retained. It removes
no proof files, theorem names, or certificate families. The first pass reduced
the entry point from 10,011 imports to 6,613, retaining all 13,325 local modules.
This is a reduction in redundant imports and maintenance burden, **not** a claim
that 3,398 fewer proof modules need to be compiled.

Negative propagation is computed on the much smaller quotient by mutual positive
definability, then expanded back to equation numbers. A negative at *any* member
of a class rectangle is retained, not just negatives at its representative.
Regression tests compare both algorithms with direct reference calculations,
including sentinel indices, nonrepresentative negatives, and random preorders.
Import tests cover nested comments, diamond dependencies, and orphan rejection.
Positive closure retains the dense BLAS implementation: a packed-integer
Warshall experiment matched the answers but was slower on the full board and
was not retained.

On the full current board, with `OPENBLAS_NUM_THREADS=2`, closure took 62.82 s
versus 84.91 s for the original algorithm, excluding source parsing. All ten
positive and ten negative matrices agreed entry-for-entry. These are observed
local timings, not guarantees. `--verify-closure` retains a reproducible check
of quotient-based negative propagation against the full-matrix calculation.

For new work: add a focused mathematical module with a documented construction
or obstruction; build it; add its import; then rerun the board and compare
reduced cells as well as raw cells. Do not present overlapping closure counts as
independent discoveries.
