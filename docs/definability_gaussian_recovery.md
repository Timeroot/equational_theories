# Gaussian-integer obstructions to term recovery

16 September 2026. The high-impact completely-open table led to three new
refutations in [GaussianRecovery.lean](../equational_theories/Definability/GaussianRecovery.lean):

- E1496 → E1113 is not term-structural on arbitrary carriers.
- E1496 → E680 is not term-structural on arbitrary carriers.
- E1496 → E1682 is not term-structural on arbitrary carriers.

Lean names these `EquationTARGET_not_termStructuralFrom_Equation1496_gaussian`.
All three have transitive axiom guards allowing only `propext`, `Classical.choice`,
and `Quot.sound`. There is no `sorry`, native computation, or external solver.

These are **infinite-carrier** obstructions. They do not refute the finite
variants, FO structural definability, or term definability without recovery.
Removing a pair from the completely-open inventory does not settle its other
seven variants.

## Board impact

After the existing transitivity, hierarchy, and duality closure, these three
proofs settle **104 previously completely-open raw pairs**, represented by
**18 TS/all class pairs**. The progress metric drops **284 → 180 raw pairs**
and **61 → 43 class pairs** (a 36.6% raw reduction). No positive equivalence
classes merge. TS/all's total open count drops 25,743 → 25,639; every other
board's statuses are unchanged.

Here is the complete list of affected class pairs, grouped by source. Each
target in a row is a separate class pair; raw counts include all class members.
Class memberships are in the [TS/all inventory](definability_open/termStructural_all.md).

| Source representative | Target representatives | Newly refuted raw pairs |
|---:|---|---:|
| 477 | 680, 1073, 1113, 1695 | 24 |
| 481 | 680, 1073, 1113, 1682, 1695 | 28 |
| 1492 | 680, 1073, 1113, 1695 | 24 |
| 1496 | 680, 1073, 1113, 1682, 1695 | 28 |

In particular, `477 → 1073` and `1492 → 1073`, previously the highest-impact
positive targets, are impossible in the strongest variant. Their finite-FO
questions remain open. All 104 pairs change profile from `NNOOOOOOOO` to
`NNNOOOOOOO`, in the audit's order `I/all, I/fin, TS/all, TS/fin, S/all, S/fin,
TD/all, TD/fin, D/all, D/fin`.

The [remaining inventory](definability_open/completely_open.md) recomputes all
four impact columns against the remaining 180 pairs. The largest positive
impact is now 32, at `1276 → 692`; the largest negative impact is 24.

## The source and the forward restriction

Work on the Gaussian integers with `x ◇ y = i(x − y)`, where `i² = −1`.
Squares are zero, and

```text
(y ◇ x) ◇ (y ◇ (z ◇ z)) = i(i(y − x) − iy) = x.
```

Thus this is an E1496 model. Every binary term operation is Gaussian-linear,
`x □ y = ax + by`. The proof reuses the existing `lin_isCloneInvariant` with
coefficient modulus −1; only its linearity conclusion is needed here.

Evaluating the target equation at `(x,y)=(1,0)` and `(0,1)` gives:

| Target | Coefficient conditions |
|---|---|
| E1113 | `(ab)² = 1`, `(a+b²)(1+ab) = 0` |
| E680 | `ab = 1`, `a + b²(a²+ab+b) = 0` |
| E1682 | `ab(1+a+b) = 1`, `a²+b² = 0` |

Each forces both coefficients to be units. A Gaussian unit has norm 1, hence
is one of `1, −1, i, −i`. The formal proof proves this classification by integer
arithmetic, then checks the sixteen coefficient pairs with ordinary kernel
`decide`. It is an exhaustive algebraic reduction, not a bounded search for terms.

For context, the coefficient pairs satisfying these equations are:

| Target | Gaussian-linear coefficient pairs `(a,b)` |
|---|---|
| E1113 | `(1,−1)`, `(−1,1)`, `(−1,−1)`, `(i,i)`, `(−i,−i)` |
| E680 | `(−1,−1)` |
| E1682 | `(−1,i)`, `(−1,−i)`, `(i,−1)`, `(−i,−1)` |

The Lean proof only needs, and checks, that each admissible pair lies in one
of the following three traps.

## Why no companion recovers the source

If `a` and `b` are real integers, `□` preserves the real axis `ℤ ⊂ ℤ[i]`.
Every term built from `□` preserves it too. The source does not: `1 ◇ 0 = i`.
This excludes recovery from all the real-coefficient candidates.

For each remaining candidate, one of the two residue maps
`φ : ℤ[i] → ℤ/5ℤ`, sending `i` to 2 or 3, has `φ(a+b)=1`.
Every binary term of `□` has coefficients `u,v` with

```text
u + v = 1 + (a + b − 1)w
```

for some Gaussian integer `w`. Reducing modulo `φ` gives `φ(u+v)=1`.
But the source's coefficient sum is zero. Equivalently, evaluating a supposed
recovery term at `(1,1)` would give `0=1` in `ℤ/5ℤ`.

This is a recovery obstruction, not an assertion that the target has no
term-defined realization. For example, applying the source operation to
`(x ◇ y, x ◇ x)` gives `y−x`, which satisfies E1113 but loses the ability to
multiply by `i` using terms. Finite quotients do not retain this real-axis
argument: a residue of `i` can become an ordinary integer scalar.

## Organization

`Trapped` is the common three-way cover; `no_recovery` handles the reverse
definition once; `not_termStructural` combines it with the source and forward
linearity. Each target only supplies its coefficient conditions and unit check.
The module is imported by the main `Definability.lean` entry point. The
[open-cell audit](definability_open_audit.md) and all impact columns are regenerated
from these declarations, not manually changed statuses.

## Verification and timings

With dependencies already built, standalone checking of `GaussianRecovery.lean`
took **6.07 seconds total**; Lake reported **6.5 seconds** for building the new
module. The full incremental `lake build equational_theories.Definability`
completed in **139.53 seconds** (16,631 jobs including cached dependencies and
entry-point planning). These were concurrent local runs, not cold-build or
isolated performance benchmarks. All 15 closure/import/audit regression tests
passed. The import-minimization check retained all 13,330 reachable local modules
with 6,577 direct entry-point imports; no existing proof imports were removed.
Full audit regeneration, including agreement of all ten optimized negative
closures with the full-matrix reference, took **202.90 seconds**.
