# FO-structural obstructions from compactness and model counts

Date: 2026-09-21.

This pass supplies 35 Lean-proved generators refuting unrestricted
FO-structural interpretation. The final nine complete the E1 source row: no
nontrivial law in the catalog can recover every magma by mutual FO definitions.

The individual generators are:

| Source | Target | Lean declaration |
|---|---|---|
| E8 | E3 | [`Equation3_not_StructuralFrom_Equation8_compactness`](../equational_theories/Definability/EightRowCounting.lean#L177) |
| E8 | E326 | [`Equation326_not_StructuralFrom_Equation8_compactness`](../equational_theories/Definability/SquareColumnCounting.lean#L160) |
| E3253 | E8 | [`Equation8_not_StructuralFrom_Equation3253_compactness`](../equational_theories/Definability/EventualRowCounting.lean#L189) |
| E1 | E8 | [`Equation8_not_StructuralFrom_Equation1_compactness`](../equational_theories/Definability/UnrestrictedRowCounting.lean#L73) |
| E11 | E109 | [`Equation109_not_StructuralFrom_Equation11_compactness`](../equational_theories/Definability/RightIdentityCounting.lean#L281) |
| E3659 | E3253 | [`Equation3253_not_StructuralFrom_Equation3659_compactness`](../equational_theories/Definability/DiagonalTableCounting.lean#L231) |
| E151 | E3253 | [`Equation3253_not_StructuralFrom_Equation151_compactness`](../equational_theories/Definability/DiagonalTableCounting.lean#L239) |
| E3659 | E151 | [`Equation151_not_StructuralFrom_Equation3659_compactness`](../equational_theories/Definability/IdempotentDiagonalCounting.lean#L111) |
| E1 | E3659 | [`Equation3659_not_StructuralFrom_Equation1_compactness`](../equational_theories/Definability/IdempotentMapCounting.lean#L132) |
| E47 | E326 | [`Equation326_not_StructuralFrom_Equation47_compactness`](../equational_theories/Definability/CycleThreeCounting.lean#L257) |
| E3253 | E47 | [`Equation47_not_StructuralFrom_Equation3253_compactness`](../equational_theories/Definability/CycleThreeCounting.lean#L260) |
| E151 | E47 | [`Equation47_not_StructuralFrom_Equation151_compactness`](../equational_theories/Definability/CycleThreeCounting.lean#L272) |
| E3659 | E47 | [`Equation47_not_StructuralFrom_Equation3659_compactness`](../equational_theories/Definability/CycleThreeCounting.lean#L279) |
| E411 | E8 | [`Equation8_not_StructuralFrom_Equation411_compactness`](../equational_theories/Definability/CycleFourCounting.lean#L317) |
| E411 | E47 | [`Equation47_not_StructuralFrom_Equation411_compactness`](../equational_theories/Definability/CycleFourCounting.lean#L320) |
| E151 | E411 | [`Equation411_not_StructuralFrom_Equation151_compactness`](../equational_theories/Definability/CycleFourCounting.lean#L333) |
| E3659 | E411 | [`Equation411_not_StructuralFrom_Equation3659_compactness`](../equational_theories/Definability/CycleFourCounting.lean#L340) |
| E3253 | E411 | [`Equation411_not_StructuralFrom_Equation3253_compactness`](../equational_theories/Definability/EventualRowExactCounting.lean#L184) |
| E8 | E4470 | [`Equation4470_not_StructuralFrom_Equation8_compactness`](../equational_theories/Definability/SquareBalancedCounting.lean#L183) |
| E47 | E4470 | [`Equation4470_not_StructuralFrom_Equation47_compactness`](../equational_theories/Definability/SquareBalancedCounting.lean#L187) |
| E151 | E4470 | [`Equation4470_not_StructuralFrom_Equation151_compactness`](../equational_theories/Definability/SquareBalancedCounting.lean#L191) |
| E3659 | E4470 | [`Equation4470_not_StructuralFrom_Equation3659_compactness`](../equational_theories/Definability/SquareBalancedCounting.lean#L198) |
| E3253 | E3319 | [`Equation3319_not_StructuralFrom_Equation3253_compactness`](../equational_theories/Definability/LeftCubeColumnCounting.lean#L334) |
| E411 | E3319 | [`Equation3319_not_StructuralFrom_Equation411_compactness`](../equational_theories/Definability/LeftCubeColumnCounting.lean#L338) |
| E151 | E3319 | [`Equation3319_not_StructuralFrom_Equation151_compactness`](../equational_theories/Definability/LeftCubeColumnCounting.lean#L342) |
| E3659 | E3319 | [`Equation3319_not_StructuralFrom_Equation3659_compactness`](../equational_theories/Definability/LeftCubeColumnCounting.lean#L349) |

| E1 | E99 | [`Equation99_not_StructuralFrom_Equation1_compactness`](../equational_theories/Definability/UnaryIdentityCounting.lean#L205) |
| E1 | E614 | [`Equation614_not_StructuralFrom_Equation1_compactness`](../equational_theories/Definability/UnaryIdentityCounting.lean#L213) |
| E1 | E817 | [`Equation817_not_StructuralFrom_Equation1_compactness`](../equational_theories/Definability/UnaryIdentityCounting.lean#L221) |
| E1 | E1020 | [`Equation1020_not_StructuralFrom_Equation1_compactness`](../equational_theories/Definability/UnaryIdentityCounting.lean#L229) |
| E1 | E1223 | [`Equation1223_not_StructuralFrom_Equation1_compactness`](../equational_theories/Definability/UnaryIdentityCounting.lean#L237) |
| E1 | E1426 | [`Equation1426_not_StructuralFrom_Equation1_compactness`](../equational_theories/Definability/UnaryIdentityCounting.lean#L245) |
| E1 | E1629 | [`Equation1629_not_StructuralFrom_Equation1_compactness`](../equational_theories/Definability/UnaryIdentityCounting.lean#L253) |
| E1 | E3456 | [`Equation3456_not_StructuralFrom_Equation1_compactness`](../equational_theories/Definability/UnaryIdentityCounting.lean#L261) |
| E1 | E4380 | [`Equation4380_not_StructuralFrom_Equation1_compactness`](../equational_theories/Definability/UnaryIdentityCounting.lean#L269) |

These results concern arbitrary, possibly infinite magmas. **They do not refute
the finite FO-structural versions.** Each exported conclusion has an axiom guard
containing only `propext`, `Classical.choice`, and `Quot.sound`.

## Why finite counts can obstruct unrestricted interpretation

Write `N_A(n)` for the number of labeled binary operation tables on `Fin n`
satisfying A. The general theorem
[`FORecoveryCompactness.bounded_counts`](../equational_theories/Definability/FORecoveryCompactness.lean)
proves

```text
B.StructuralFrom A  ⇒  ∃ K, ∀ n > 0, N_A(n) ≤ K N_B(n).
```

A pair of parameter-free formulas defining the target and recovering the source
has a first-order witness sentence. The sentence asserts that the forward
formula defines a total binary operation satisfying B and that the translated
recovery formula defines the original operation.

If every A-model admits such a pair, compactness supplies a finite collection
of pairs covering every nonempty A-model. For each fixed pair, one B-table can
recover at most one A-table on the same labeled carrier. Summing over the finite
collection gives the bound.

The formulas in the definition of structural interpretation may depend on the
source magma. The argument does not assume a uniform formula pair: obtaining a
finite cover is the compactness step. A hypothesis restricted to finite models
does not supply that step.

## The counting bounds

For n ≥ 2, put `I = n^(n−1)` and `J = (n−1)n^(n−2)`.

* [`EightRowCounting.lean`](../equational_theories/Definability/EightRowCounting.lean)
  proves `N_3(n) = I^n` and `N_8(n) = (I+J)^n`. In an E8 row at a,
  either a is fixed or a lies in a two-cycle. Bernoulli's inequality gives
  `n N_3(n) ≤ N_8(n)`.
* [`SquareColumnCounting.lean`](../equational_theories/Definability/SquareColumnCounting.lean)
  proves `N_326(n) ≤ 2 N_3(n)`. Once the diagonal is fixed, a nonidentity
  square map identifies two columns. Each row then has at most n−2 independent
  entries. The identity-diagonal part contributes exactly `N_3(n)`, and the
  nonidentity part contributes at most another `N_3(n)`.
* [`EventualRowCounting.lean`](../equational_theories/Definability/EventualRowCounting.lean)
  proves `N_3253(n) ≥ (I+2J)^n`: besides E8 rows, include rows where a reaches
  a distinct fixed point in one step. The two families are disjoint.
  Consequently `n N_8(n) ≤ 3 N_3253(n)`.
* [`UnrestrictedRowCounting.lean`](../equational_theories/Definability/UnrestrictedRowCounting.lean)
  counts all operation tables and proves `n N_8(n) ≤ N_1(n)` for n ≥ 4.

Each comparison has an unbounded ratio in the refuted direction. The E8 → E326
result subsumes E8 → E3 through existing implications; the separate E3 theorem
records the initial application and its simpler count.

The current [FO equivalence inventory](definability_structural_equivalence_gaps.md)
and [open-cell audit](definability_open/summary.md) include propagated consequences.

## Right identities

[`RightIdentityCounting.lean`](../equational_theories/Definability/RightIdentityCounting.lean)
proves E11 → E109 false. In an E109 magma, squares are right identities and
rows indexed by right identities take values among the right identities. For a
fixed set S of k right identities, encode the entries in those rows, the
remaining diagonal entries, and the remaining off-diagonal entries. There are
at most

```text
k^((k+1)(n−k)) n^((n−k)(n−k−1))
```

codes. For n ≥ 8 this is at most `n^((n−1)(n−2))`, uniformly over nonempty S.
Summing over at most `2^n` subsets bounds `N_109(n)`.

E11 admits at least `n^(n−1) n^((n−1)(n−2))` tables: fix one right identity,
make every square equal to it, and leave all other permitted entries arbitrary.
For n ≥ 8, this gives `n N_109(n) ≤ N_11(n)`.

## Square maps and diagonal freedom

For E151 and E3659 the square map is, respectively, involutive or idempotent;
every off-diagonal entry is unrestricted.

[`EventualRowUpperCounting.lean`](../equational_theories/Definability/EventualRowUpperCounting.lean)
proves `N_3253(n) ≤ 4^n I^n`. The four possible row-orbit shapes each supply at
most I rows. [`DiagonalTableCounting.lean`](../equational_theories/Definability/DiagonalTableCounting.lean)
constructs two larger families:

* Idempotent square maps fixing five distinguished points and sending every
  other point into them supply `5^(n−5) I^n` E3659 tables.
* On k blocks of 128 points, a permutation matching the two 64-point halves
  defines an involution. Independent choices give `(64!)^k I^(128k)` E151
  tables. The checked inequality `64! ≥ 2·4^128` gives an unbounded ratio.

These refute E3659 → E3253 and E151 → E3253.

[`InvolutionCounting.lean`](../equational_theories/Definability/InvolutionCounting.lean)
encodes each involution by its smaller two-cycle endpoints and their partners.
There are at most `2^n n^floor(n/2)` such codes.
[`IdempotentDiagonalCounting.lean`](../equational_theories/Definability/IdempotentDiagonalCounting.lean)
compares this with the `m^(3m)` idempotent maps on 4m points obtained by fixing
m points and mapping the other 3m into them. The ratio is unbounded, refuting
E3659 → E151.

Finally, [`IdempotentMapCounting.lean`](../equational_theories/Definability/IdempotentMapCounting.lean)
bounds idempotent maps by the local condition `f(f(a))=f(a)` at one point.
There are at most `2 n^(n−1)` such functions, versus `n^n` unrestricted square
maps. This refutes E1 → E3659.

Some listed generators have become redundant through these later results. They
retain shorter independent arguments; their closure effects must not be added
as if they were disjoint discoveries. E326 versus E3 remains unresolved by this
method.

## Three-cycles, four-cycles, and eventual cycles

For `J_k = (n−1)⋯(n−k+1) n^(n−k)`, the exact table counts are

```text
N_47(n)   = (I + J_3)^n,
N_411(n)  = (I + J_2 + J_4)^n,
N_3253(n) = (I + 2 J_2 + J_3)^n.
```

[`CycleThreeCounting.lean`](../equational_theories/Definability/CycleThreeCounting.lean),
[`CycleFourCounting.lean`](../equational_theories/Definability/CycleFourCounting.lean), and
[`EventualRowExactCounting.lean`](../equational_theories/Definability/EventualRowExactCounting.lean)
prove these formulas and the required inequalities directly. The comparisons
separate E3253 from E411, E411 from E8 and E47, and E47 from E326. The shared
diagonal-family bounds also separate E151 and E3659 from E47 and E411.

## Commuting squares and invariant left-cube columns

[`SquareBalancedCounting.lean`](../equational_theories/Definability/SquareBalancedCounting.lean)
proves `N_4470(n) ≤ 2 N_3(n)`. Fix the square map s. If `s(a)≠a`, the identity
`f(x,s(y))=f(s(x),y)` determines the row at s(a) from the row at a, and forces
`f(a,s(s(a)))=s(s(a))`. Moreover `s(s(a))≠a`; otherwise the two diagonal values
would force `s(a)=a`. Removing the determined row and fixed entries leaves at
most `n^(n(n−2))` tables for each nonidentity s. The identity case is idempotence.
This separates E8, E47, E151, and E3659 from E4470.

[`LeftCubeColumnCounting.lean`](../equational_theories/Definability/LeftCubeColumnCounting.lean)
proves `N_3319(n) ≤ 2 (2I)^n ≤ 4 N_8(n)`. For a nonidentity left-cube map,
two columns coincide. Collapse those columns to a domain of size n−1. A row
then has the form `g(p(g(u)))=v`; splitting according to whether `g(u)=v`
leaves at most `2 n^(n−2)` possibilities. The identity-cube case satisfies E8.
A Bernoulli inequality over the integers supplies the comparison with N_8.
These bounds separate E3253, E411, E151, and E3659 from E3319.

## Completing the unrestricted E1 row

[`StraightLineCounting.lean`](../equational_theories/Definability/StraightLineCounting.lean)
formalizes a collision bound for evaluating a short program in an arbitrary
binary operation. A program starts at one fixed element and reads r distinct
syntactic input pairs, using previously computed values as arguments.

Until two intermediate values coincide, the program reads distinct table
entries. If the first collision occurs at step k+1, there are at most `n^k`
prefixes, at most r earlier values to collide with, and `n^(n²−k−1)` tables
extending each specified prefix and collision. Summing over at most r steps
bounds the number of tables with a collision, for `n² ≥ r`, by

```text
r² n^(n²−1).
```

[`UnaryIdentityCounting.lean`](../equational_theories/Definability/UnaryIdentityCounting.lean)
gives explicit programs of three or four multiplications for E99, E614, E817,
E1020, E1223, E1426, E1629, E3456, and E4380. Each equation forces two of the
intermediate values to agree. Since there are `n^(n²)` unrestricted tables,
the ratio is unbounded. These were the final nine open targets from E1 on the
unrestricted FO board; the finite FO questions remain open.

The general theorem does not rely on random experiments or a search certificate.
Its Lean proof counts partial tables and chooses the first collision in a
finite evaluation trace.

## Reporting the scope correctly

Finite carriers in a compactness counting proof are counting domains, not
finite counterexamples. The source parser now suppresses its finite-witness
heuristic for proofs invoking the compactness counting lemmas. A regression
test checks this distinction while retaining finite facts backed by ordinary
finite witnesses or explicit `StructuralFromFin` statements. The regenerated
finite FO board receives no negative facts from this counting pass.

## Audited impact and validation

The unrestricted FO inventory falls from **1,094 to 1,001 unresolved class
pairs**: 93 potential equivalences are now separated. The proved partition
still has 737 blocks. Its unresolved raw unordered pairs fall from 12,822 to
12,416. The finite FO inventory remains at 1,049 unresolved pairs across 712
proved blocks; the new finite positives settle directions without a new merger.

The unrestricted term-structural inventory falls from **32 to 28** unresolved
class pairs (152 to 136 raw unordered pairs), with 739 proved blocks. The finite
term-structural classification remains complete at 716 classes.

Relative to the checkpoint before this sustained pass, the 35 counting
generators and [five cube-column constructions](definability_cube_column_repair.md)
have the following combined effects. These are closure totals, so overlapping
consequences of different generators are counted once.

| Board | New proved arrows | New refuted arrows | Raw open cells closed | Quotient open cells closed |
|---|---:|---:|---:|---:|
| FO-structural, arbitrary | 232 | 406 | 638 | 127 |
| FO-structural, finite | 184 | 0 | 184 | 26 |
| Term-structural, arbitrary | 0 | 60 | 60 | 10 |
| Term-structural, finite | 0 | 0 | 0 | 0 |

The term-structural changes come from the separate
[confluence pass](definability_confluence_recovery.md). The other six relation
boards are unchanged at this checkpoint. The earlier unary-cycle results were
already included in the starting checkpoint and are not counted again here.

The full `equational_theories.Definability` build passes (17,028 jobs), the 20
bookkeeping tests pass, and every new exported result has a standard-axiom
guard. All 13,686 reachable local modules are retained by the pruned entry-point
imports. Each of the 35 counting declarations above links to its source line.

All ten quotient propagations match the independently computed full matrices.
The audit source fingerprint is
`a422c65b6e784b35bc789a2861a8aaa3e78b0684ecf1d2a622ec6bc448f107a1`
(14,964 files). Both regenerated equivalence inventories carry this same fingerprint.

The next [symmetry-counting argument](definability_fo_counting_followup.md) is
recorded separately as unformalized work. Its proposed conclusions are excluded
from every proved total in this report.
