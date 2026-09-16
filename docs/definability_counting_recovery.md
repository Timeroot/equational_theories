# Counting and integrality obstructions to term recovery

16 September 2026. Two new arguments attack the 43-row, 180-raw-pair
completely-open inventory left by the [Gaussian pass](definability_gaussian_recovery.md).
The proof modules are:

- [LinearCounting.lean](../equational_theories/Definability/LinearCounting.lean):
  a general finite-product counting theorem, with a standard-axiom guard.
- [LinearCountingCatalogue.lean](../equational_theories/Definability/LinearCountingCatalogue.lean):
  ten finite term-structural negative generators, each with a guard explicitly
  listing its two native-computation axioms and the standard axioms.
- [IntegralRecovery.lean](../equational_theories/Definability/IntegralRecovery.lean):
  four arbitrary-carrier term-structural negatives, all with standard-axiom guards.

There are no `sorry`s, pending mathematical hypotheses, or unverified solver
certificates in these proofs. Native computation checks finite source models and
finite coefficient counts; it does not search or enumerate the huge product magmas.
Neither argument refutes term-definability without recovery or FO structural
definability.

## Board impact

**25 of the 43 old rows are settled**, reducing completely-open pairs
**180 → 68 raw** and **43 → 18 class pairs**. This is a 62.2% raw reduction in
this pass; combined with the Gaussian pass, the original 284 have fallen to 68.

| Source representative | Newly refuted target representatives | Raw pairs | Strength proved |
|---:|---|---:|---|
| 467 | 667, 917, 1086, 1729 | 16 | TS/all only |
| 704 | 504, 870, 910, 917, 1086, 1722, 1729 | 28 | TS/fin, hence TS/all |
| 1276 | 680, 692, 707, 1316, 1695 | 32 | TS/fin, hence TS/all |
| 1279 | 504, 870, 910, 917, 1086, 1722, 1729, 3345, 3548 | 36 | TS/fin, hence TS/all |

The table lists all 25 affected TS/all class pairs, grouped by source; class
memberships remain in the [TS/all inventory](definability_open/termStructural_all.md).
No positive classes merge. TS/all open raw cells fall 25,639 → 25,527;
TS/fin open raw cells fall 23,583 → 23,487. The latter are 11 finite-class
pairs, not 21: the finite quotient identifies more equations.
Every other board's statuses are unchanged.

All 112 pairs started at profile `NNOOOOOOOO`. The 96 finite refutations now
have profile `NNNNOOOOOO`, while the 16 integrality refutations have
`NNNOOOOOOO`, in the audit order `I/all, I/fin, TS/all, TS/fin, S/all, S/fin,
TD/all, TD/fin, D/all, D/fin`. Removal from this inventory is not a resolution
of all eight variants.

The [remaining 18-row inventory](definability_open/completely_open.md) is
complete and has newly computed impact columns. Its largest hypothetical
positive impact is 24 raw pairs (`1486 → 168`); its largest negative impact is
18 (`1486 → 1479`). These are conditional bookkeeping counts, not predictions
that the positive or negative hypothesis is true.

## 1. Counting linear models, despite magma-dependent witnesses

Fix a finite commutative ring R. Suppose a source law has k distinct linear
operations `aᵢx+bᵢy` over R, and the target law has fewer than k linear operations.
Take their product on `Rᵏ`, with the i-th factor using `(aᵢ,bᵢ)`.

Any term-defined companion on this product is coordinatewise linear, say
`uᵢx+vᵢy`. If it satisfies the target law, each of these k coefficient pairs
must be one of the target's linear models. Some two coordinates i,j have the
same pair. The companion then preserves the relation “coordinate i equals
coordinate j,” so every term built from it preserves that relation too.

But the original operation cannot preserve it: evaluating at the constant
vectors `(1,0)` and `(0,1)` would force `aᵢ=aⱼ` and `bᵢ=bⱼ`, contrary to the
distinctness of the source pairs. Hence no companion can recover the source.

This does **not** assume a single witness works for all source magmas. The
witnesses may depend on the entire product magma, just as in the definition.
A term on that one product nevertheless has to act coordinatewise, and its
recovery term must preserve equality wherever the companion does.

In Lean, `Magma.LinearTest` tests six basis assignments. Satisfaction implies
this test, which is all the negative theorem needs; it makes no claim about
sufficiency for arbitrary laws using variables outside this range. Source
satisfaction is checked separately in full. The proof constructs an injection
from the k source factors into the finite set of passing target coefficient
pairs, then contradicts the cardinality bound.

### The finite certificates

The following are the ten generators, grouped when they use the same source
product. Target counts are counts over the small coefficient space `R²`.

| Source | Target generators | Field | Source factors used | Target linear models | Product order |
|---:|---|---:|---:|---:|---:|
| 1276 | 680 | 5 | 2 | 1 | 25 |
| 1276 | 707 | 23 | 2 | 1 | 529 |
| 704 | 504, 917 | 47 | 2 | 1 | 2,209 |
| 704 | 870 | 83 | 4 | 3 | 47,458,321 |
| 1279 | 504, 917 | 67 | 3 | 2 | 300,763 |
| 1279 | 870, 3345 | 29 | 3 | 2 | 24,389 |
| 1279 | 3548 | 17 | 3 | 2 | 4,913 |

For the smallest example, on `F₅²` use
`(x₁,x₂) ◇ (y₁,y₂) = (x₁+3y₁, 4x₂+4y₂)`.
Both factors satisfy E1276. The only linear E680 operation over F₅ is `−x−y`.
Any linear E680 companion therefore uses the same operation in both coordinates,
and cannot recover the source's two different operations.

Existing finite equivalences save four additional generator proofs:
`504`, `910`, and `1722` belong to one TS/fin class; `917`, `1086`, and `1729`
to another. Likewise `680` and `1695` coincide in TS/fin, as do `707` and `1316`.
These are finite equivalences, not assertions about TS/all.

## 2. E467 cannot recover its non-integral coefficient

On the complex numbers put `A = −(1+i)/2` and `x ◇ y = Ax+iy`.
This satisfies E467. Moreover `−A(A+1)=1/2`, so A is not an algebraic integer:
if it were, 1/2 would be integral over the integers, but an integral rational
number must be an integer.

Every term-defined companion is complex-linear. The four target laws force
both coefficients to be algebraic integers:

- E667 gives `a=−b³` and the monic equation `b⁸−b⁶−b⁴−1=0`.
- E917 gives `ab²=1` and `a+a²b+ab²+b³=0`. These imply
  `b⁶+b³+b+1=0` and `a=(b⁵+b²+1)²`, so both coefficients are integral.
- E1729 reduces to the same two coefficient conditions by multiplication and
  substitution.
- E1086 reduces to those conditions with the coefficients interchanged.

An operation with integral coefficients preserves algebraic integers, as does
every term of that operation. The source does not: `1 ◇ 0=A`.
This refutes `467 → 667, 917, 1086, 1729` in TS/all. The finite versions remain
open; the integrality argument is genuinely an infinite-carrier argument.

## 3. What the searches did not establish

The maintained [linear-count search](../scripts/definability_linear_counts.py)
tries every modulus from 2 through 100, including composite moduli. It finds the
21 class-pair candidates sourced at E704, E1276, and E1279. It finds no scalar
count obstruction for the other 22 old rows; the integrality proof settles four
of those by a different method. Five regression tests compare the search with
full small-table evaluation and check the concrete certificates. In particular,
an equation such as E4405, whose linear condition is simply `a=b`, must not be
mistaken for having no models because it has no univariate elimination constraint.

Exploratory affine counts over prime fields through 101, and matrix-linear
counts over `Mat₂(F₂)`, `Mat₂(F₃)`, and `Mat₂(F₅)`, gave no further counting
obstruction for those other rows. These are bounded unsuccessful searches, not
positive proofs, impossibility theorems for these methods, or claims about
mathematical openness.

The residual central-groupoid question `1486 → 168` has a particularly concrete
spectrum route: an E1486 model of nonsquare order would conflict with Knuth's
square-cardinality theorem for E168. The square upper bound is explicitly
`PROOF_AVAILABLE` but still pending Lean formalization in
[NotePending.lean](../equational_theories/Spectrum/NotePending.lean).
That pending theorem is **not** counted as a proof here. This is different from
a question for which no mathematical route is known. The note's claimed
E1486 models of orders 13 and 21 also remain `PROOF_AVAILABLE` obligations in
[NoteObligations.lean](../equational_theories/Spectrum/Generated/NoteObligations.lean).

## Verification and timings

The final counting catalogue checked standalone in **18.44 seconds total**;
the integrality module checked in **8.46 seconds total**. The final incremental
Definability build passed in **98.97 seconds**, covering 16,634 jobs including
cached dependencies. These are concurrent local runs, not cold-build benchmarks.
All **20 regression tests** passed. The import check keeps all **13,333** reachable
local modules with **6,578** direct entry imports. It removed just one redundant
edge, `CloneProd`, now reached through `LinearCountingCatalogue → LinearCounting`;
no existing proof module or theorem was removed.
Full audit regeneration took **197.31 seconds**, including agreement of all
ten optimized negative closures with the full-matrix reference calculation.

## Reproduction

```sh
lake build equational_theories.Definability
OPENBLAS_NUM_THREADS=2 python3 scripts/definability_audit.py --write --date 2026-09-16 --verify-closure
OPENBLAS_NUM_THREADS=2 python3 -m unittest discover -s scripts -p 'test_definab*.py'
python3 scripts/definability_linear_counts.py --pair 1276 680 --pair 704 870 --max-modulus 100
```

The search only prints candidates. It never changes Lean, proof facts, the
snapshot, or the board. The [current inventory](definability_open/completely_open.md)
is regenerated from checked declarations and the existing closure, with all
four impact columns recomputed against the remaining completely-open pairs.
