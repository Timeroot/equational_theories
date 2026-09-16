# Working on definability

The [open-cell audit](definability_open_audit.md) gives the complete remaining
inventory, evidence labels, finite/all distinctions, and regeneration commands.
The [completely-open inventory](definability_open/completely_open.md) isolates
pairs unresolved in all eight definability variants. For the independent
[spectrum-obstruction recheck](definability_spectrum_check.md), run
`lake build equational_theories.Spectrum` followed by
`OPENBLAS_NUM_THREADS=2 python3 scripts/spectrum_definability_check.py`.
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
