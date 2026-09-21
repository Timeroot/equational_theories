# Definability research pass, 20 September 2026

The requested run lasted **12 hours 42 minutes**, from **02:47:45 UTC**
to **15:30:42 UTC**. The machine-readable checkpoint is
[`definability_twelve_hour_progress.json`](../data/definability_twelve_hour_progress.json).
No commits were made.

Every new declaration is listed with its data and Lean source in the
[certificate index](../data/definability_twelve_hour_certificates.json).

## Verified table checkpoint

The tenth completed checkpoint contains **285 new declarations**: 175 finite
FO-structural negatives, 99 finite term-structural counting negatives, and eleven
finite one-way FO-definability negatives. The first two E677 one-way declarations share
one generating obstruction: the existing positive arrow E1117 → E4369 lets the
E677 → E4369 negative propagate to E677 → E1117.

Relative to the start of this run, the exact reductions in open cells are:

| Board | Raw cells closed | Quotient cells closed |
|---|---:|---:|
| Structural, arbitrary carriers | 1351 | 267 |
| Structural, finite carriers | 1351 | 262 |
| Term-structural, arbitrary carriers | 912 | 153 |
| Term-structural, finite carriers | 912 | 149 |
| Term-definable, arbitrary carriers | 44 | 11 |
| Term-definable, finite carriers | 44 | 11 |
| FO-definable, arbitrary carriers | 44 | 11 |
| FO-definable, finite carriers | 44 | 11 |

These are separate boards; their numbers should not be added as if they were
distinct equation pairs. At this checkpoint the completely open inventory is
**28 raw pairs / 8 class pairs**.

The full Definability import builds. All 26 regression tests, the import audit,
the independent checks of the new certificates, and all ten comparisons with
the full-matrix closure reference passed. Every new native computation used by
a theorem has an explicit axiom guard.

## Stronger one-way obstruction

[`Field83NoTarget.lean`](../equational_theories/Definability/Generated/Field83NoTarget.lean)
proves E677 → E4369 and E677 → E1117 impossible even for finite FO definability.
On the 83-element field, translations and multiplication by nonzero squares
admit exactly 6,889 compatible binary operations. A nonlinear operation in this
family satisfies E677; none satisfies either target law. The saved table and
complete compatible family are checked independently and in Lean.

The [next finite-field certificates](definability_finite_field_negatives.md)
add eight one-way FO negatives: E677 → E335, E3352, E3558, E3748,
E4290, E4408, and E670 → E4290, E4408. Their carriers have 97 and 49
elements, respectively. All eight passed their guarded Lean builds and the
full table audit.

The other certificates use cyclic groups, nilpotent rings, and noncommutative
groups. Complete compatible-operation counts obstruct mutual term recovery;
automorphism-pattern obstructions give the stronger FO-structural negatives.
A finite counterexample refutes the corresponding claim over arbitrary
carriers as well.

## Order-eleven E1483 separation: optional certificates

The full E1483 order-eleven exclusion and
**E1486 → E1483 finite-FO negative** passed Lean, including explicit axiom guards.
This was a local certificate-enabled build. The 734 MiB bundle is now excluded
from Git: the default exclusion is registered as `proofAvailable` with `sorry`,
and its definability consequence is disabled. Thus the four raw pairs
`{1486,2126} → {1483,2163}` are no longer counted as checked. Current totals are
in the [generated inventory](definability_open/completely_open.md).

The [proof guide](definability_1483_order_eleven.md) describes the mathematical
normalization, propositional encoding, and certificate checks. Its distinction
between ordinary mathematical proofs and the sixteen native LRAT computations
is explicit. The exact E1483 spectrum remains open.

The later batches in this checkpoint include nine additional FO-structural
negatives from noncommutative groups and two counting negatives using
four-ary relations: E647 → E1256 and E3265 → E3256. The fourth checkpoint
also upgrades E1432 → E3259 from term-structural to FO-structural, adds five
group-counting negatives, and adds six other FO-structural negatives.
The fifth checkpoint adds E1441 → E323 by counting on a 27-element
Heisenberg group, and the FO-structural negatives E839 → E838 and
E1447 → E1451 from monomial actions on 49 points. The exact automorphism
scans found no stronger obstruction for the E1441, E48, and E1235 counting
witnesses. Longer searches continue.

The sixth checkpoint adds E162, E1461, and E1469 → E3334. Congruence actions
on symmetric three-by-three matrices over the two-element field give a complete
family of 64 operations on 64 points. Each source has four models in the
family, and the target has three. The independent counts, guarded Lean build,
root import, and full board audit passed. Exact automorphism analysis found no
FO-structural upgrade for these witnesses.

The seventh checkpoint adds 53 FO-structural and 14 term-structural negatives.
Most of the structural gains use affine permutation actions with additional
fixed points; ordered-pair actions of symmetric and alternating groups supply
other witnesses. The counting certificates include E1052 → E1039,
E1230 → E1234, E1235 → E1032, E1250 → E100, and E1645 → E1122,
E1731, E3278. For actions with multiple point orbits, the proofs test every
assignment or prove that testing one representative from each point orbit is
sufficient. The independent checker tests every assignment in either case.
All 67 new declarations passed their guarded builds and the full board audit.


The eighth checkpoint adds 22 FO-structural and 30 term-structural negatives.
Projection-compatible families supply the counting obstructions, including
E58 → E3258, E3464, E4284; E124 → E1109, E1322, E1728;
E1370 → E3518; E827 → E3318; E1443 → E3521, E4314;
and E418 → E621. The last uses a noncommutative group on the first factor.

The exact automorphism analysis upgrades E690 → E3321, E3323, E3520,
E3523, E3524 to FO-structural negatives. Every one of the 80,621,568
operations compatible with the source automorphisms was checked independently;
the five Lean certificates passed their axiom guards. The E124, E1370,
E827, and E418 witnesses have matching target automorphism groups.
The E1446 source yields four further FO-structural negatives, targeting
E3321, E3323, E3520, and E4362. A broader exact-automorphism search
adds ten more certificates from 24- and 49-element models. The remaining
counting additions include E690 → E4275, E1033 → E1027, and E446 → E3258.

Seven symmetry certificates use compiled interval evaluation, including the
additional E1096 → E1278 obstruction on sixteen elements. Lean
checks the tables and proves the parameter decoding and symmetry bridges;
all generated native sources reproduce exactly from their certificate data.
The E1033 → E828 and E446 → E3258 counts use compiled counters with
proved cardinality bridges. The audit fingerprint includes both native libraries and the build
configuration. The 27-element E4415 → E3537 symmetry certificate adds a
further negative.
All 52 declarations in this checkpoint passed the full board audit.

## Ninth checkpoint: noninvertible endomorphisms

Seven further term-structural negatives passed independent full-assignment
checks and initial Lean builds: E1055 → E3458; E418 → E422, E618;
E1233, E1235, E1236 → E1026; and E1235 → E828. These use complete
left-translation families also preserved by noninvertible endomorphisms.
The [endomorphism proof guide](definability_endomorphism_negatives.md) describes
the witnesses. A coordinate-coverage theorem proves completeness without enumerating every
unary function on the carrier. Their integrated guarded builds, root import, and all ten board comparisons
passed. The exact automorphism comparisons found no FO-structural
upgrade for these witnesses.

## A failed route to the E1483 cardinality bound

An existing eight-element E1483 model rules out the auxiliary claim that the
rank of multiplication by an idempotent is at most the number of idempotents.
Its idempotents are `{0,1,2}`, whereas the image of left multiplication by `0`
is `{0,1,3,4}`. Thus even an arbitrary injection from that image into the
idempotents is impossible. The
[Lean check](../scripts/check_definability_1483_rank_idempotents.lean) proves
the source law, both cardinalities, and absence of an injection using ordinary
axioms only; the [saved table](../data/definability_1483_rank_idempotent_counterexample.json)
is also checked independently. This does not refute the broader proposed
bound `|M| ≤ |Idem(M)|²`: this example has `8 ≤ 3²`.

The E1483 → E1479 candidate still passes the saved finite models, but remains
unproved universally. Its diagonal formula `candidate(x,x)=q³(x)` now has an
ordinary axiom-free proof in `scripts/check_definability_central_candidate.lean`.
The conjecture `q³=q` survived external countermodel searches through order nine;
orders ten, twelve, and sixteen returned unknown after thirty minutes apiece.
Two one-hour Vampire attempts and a ground-congruence search with over eight
million terms found no proof. These exploratory results are recorded in
`data/definability_1483_diagonal_search.json` and add no table facts.

## E1485 → E1483: all search cases excluded externally

The last necessary-condition case to finish returned UNSAT after 13,075 seconds.
Cases 1, 2, and 3 had already returned UNSAT. The conditions include rotation,
compatible binary relations, the exact idempotent set, local clone restrictions,
and preservation of generation under mutual term recovery. The four results
use generation requirements that are independently verified for the source.

This is **not yet a Lean certificate or a table negative**. The exact DIMACS
inputs can be reproduced using
[`definability_weak_central_export.py`](../scripts/definability_weak_central_export.py).
The [research manifest](../data/definability_weak_central_unsat_search.json)
records the completed external searches and the remaining proof obligations.
In particular, the free-orbit symmetry normalization and the auxiliary-variable
encoding still need formal justification.

The generic generation-order argument is now proved in
`equational_theories/Definability/GenerationOrder.lean`, including its converse
and preservation under term recovery. Its five axiom guards pass with ordinary
axioms. This supplies one ingredient of the model-to-CNF translation; it does
not certify the exploratory UNSAT reports.

`WeakCentralSource.lean` also verifies the concrete 32-element source, its
rotation, five idempotents, and four generating sets with ordinary axiom
guards. All four proof-logging reruns stopped at the 2 GiB free-space limit
without complete proofs; their inputs and result records are retained.

`WeakCentralRestrictions.lean` proves that the two selected closed subsets
have only two possible E1483 term restrictions each, so the four local cases
are exhaustive. All seven guards use ordinary axioms. The accompanying
restriction-family checker reproduces its tables and proofs exactly.

`WeakCentralRelations.lean` certifies preservation of all 174 non-universal
compatible relations, with 189,717 pairs of relation members checked by native
evaluation. Its three axiom guards and exact source reproduction pass.
Free-orbit normalization and the exact SAT encoding are still unproved.

`WeakCentralNecessary.lean` bundles these facts: any finite term-structural
positive answer supplies a 32-point E1483 operation satisfying all preservation
conditions and all four generation constraints. Its two guards pass. This is
a necessary-condition theorem, not an inconsistency proof.

`WeakCentralSymmetries.lean` checks the five free-orbit generators: inverse
permutations, pointwise fixation of the seventeen small points, commutation
with rotation, and invariance of all 174 compatible relations. It also proves
that relabeling preserves the relations. The finite relation check uses native
evaluation; the other data guards use ordinary axioms. This does not prove
that the lexicographic symmetry-breaking clauses preserve satisfiability.

The largest compiled counting certificates use separate imported axiom-guard
modules, with private names printed explicitly. Their mathematical proof
modules, native sources, and guard modules are all reproduced from the data.
This avoids rebuilding an expensive proof merely to add its expected axiom
message. A completed native-counting certificate verified this guard path.
The largest counters also prove the representative-operation and law-test
bridges abstractly before instantiating their concrete tables. This keeps large
arrays out of kernel conversion checks; the 53-point certificate rebuilds in
seven seconds. The counter verifier now checks auxiliary probe inverses as well
as the generator inverses, even though the counts themselves use only generators.

## Tenth checkpoint: projective geometry

Thirty-five FO-structural declarations and twelve counting declarations passed
the full checkpoint. On 52 flags of the projective plane over the three-element
field, a complete 216-operation family gives seven certificates covering eleven
E4416 directions. The two 21-point Fano witnesses each have only 45 operations
compatible with their full automorphism group; they prove E1353 and E1453 →
E653, E1633, E3264, E3460, and E3317 → E1230, E3460.

The counting negatives are E1033 → E1032 (140 > 134 on 22 points),
E1033 → E824 (84 > 80 on 53 points), and E1233 → E1236
(199 > 195 on 117 points). The last uses a compiled counter with proved
cardinality and operation bridges.

The follow-on witnesses add E1446 → E1312 on thirty ordered pairs,
E3669 → E3414 and E3676 → E452, E655, E1061, E3414 on
52 flags plus a fixed point, and six structural negatives on fifteen
Fano points, lines, and a fixed point. Fano duality also gives
E1245 → E1259 by a 17 > 16 count.

The projective line over the nine-element field adds E332 and E3751 → E3556,
covering seven raw directions. Ninety nonisotropic symplectic planes plus a
fixed point give E1253 → E818 by 981 > 900. The late S4 conjugation witnesses
add E633 → E427, E1239, E1242 and E1046 → E427 on 24 points, using
144-operation complete families.

The final projective-line batch adds seven counting negatives:
E1322 → E1109; E1050 → E1239, E3259; E1252 → E1248;
E1253 → E819, E1225; and E1255 → E1227. All forty-seven declarations passed independent
checks, guarded Lean builds, exact source reproduction, and the full audit.

## Current completely open class pairs

E1483 → E1479; E1485 → E1483; E1486 → E1479, E1480, E1483;
E3342 → E4405; E3545 → E3342, E4405.
The [completely open table](definability_open/completely_open.md) contains
the corresponding 28 raw equation pairs. E3342 → E3545 has since been proved
negative. E1486 → E1483 is now pending in the checked inventory because its
large certificate bundle is not distributed, not because its proof is unknown.
