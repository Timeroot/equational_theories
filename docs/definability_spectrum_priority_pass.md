# Spectrum and term-structural priority pass

Date: 2026-09-20.

**E629 → E52 and E854 → E433 are now refuted for finite term-structural
interpretations, and hence for unrestricted term-structural interpretations.**
Their forward arrows were already ordinary implications. The proofs settle two
of the three remaining finite equivalence questions.

The subsequent [27-element product obstruction](definability_cube_focus.md)
refutes **E3342 → E3545** in both term-structural variants, settling the third
finite equivalence question. The updated
[equivalence inventory](definability_term_structural_equivalence_gaps.md)
has **no finite gaps** and **34 unrestricted gaps**, after the later
[unary-permutation separations](definability_equivalence_priority_pass.md).
There are exactly **716 finite term-structural equivalence classes**.
The reverse arrow E3545 → E3342 remains open.

The strict-implication separations added 12 negative raw cells to each
term-structural variant; the E3342 separation adds another four in each.
Neither changes the positive classes. The E3342 separation reduces the
completely-open inventory from 28 to **24 raw pairs**, or from eight to
**seven class pairs**.

Those checkpoint counts included the local E1483/order-11 certificate proof.
With that large bundle now omitted, four pairs are pending again: the current
[checked inventory](definability_open/completely_open.md) has **28 raw pairs /
8 class pairs**. The E3342 separation itself remains fully proved.

## Why strict ordinary implication is enough here

The new [general theorem](../equational_theories/Definability/StrictImplicationCounting.lean)
uses the existing product model-count argument without enumerating any operation
space. Suppose A implies B, and some finite B-model fails A. On that carrier,
the A-operations form a proper subset of the B-operations, so there are strictly
fewer A-operations.

Take the product of **all** B-operations on that carrier. A term-defined
A-companion acts coordinatewise. If the original operation can be recovered by
a term, different B-coordinates must give different A-operations: otherwise the
recovery term cannot distinguish them. This would inject the larger finite set
into the smaller one, a contradiction. Choosing one product also handles the
fact that the defining and recovery terms may depend on the source algebra.

The [applications](../equational_theories/Definability/StrictImplicationSeparations.lean)
use existing ordinary countermodels:

| Ordinary implication | Countermodel to its reverse | New term-structural negative |
|---|---:|---|
| E52 → E629 | 4 elements | E629 ↛ E52 |
| E433 → E854 | 11 elements | E854 ↛ E433 |

The small countermodels establish strictness. **They are not asserted to be
term-structural countermodels themselves**; the argument uses the finite product.
Both conclusions and the general theorem have guards listing only `propext`,
`Classical.choice`, and `Quot.sound`. No native-computation axiom is used in these
separations. They make no new FO-structural or term-definable negative claim.

## What the spectra establish

The requested comparisons run into inclusions in precisely the directions
still completely open:

* **E1479 already has full spectrum**, proved by `Spectrum.full_1479` in
  [Linear1001.lean](../equational_theories/Spectrum/Generated/Linear1001.lean).
  The construction is `x ◇ y = −x −y` on any cyclic group. Thus neither
  E1483 → E1479 nor E1486 → E1479 can be refuted by a missing finite order.
* **E1483 has every square and twice-square order.** Squares were already
  proved. Multiplying a square-order model by its two-element model gives
  order `2k²`. The now-proved E1485 square/twice-square characterization puts
  its spectrum inside E1483's. This prevents a spectrum
  refutation of E1485 → E1483.
* **E1486 has no three-element model**, in addition to its existing two-element
  exclusion. If the proposed E1480 spectrum `{1} ∪ {n ≥ 4}` is correct, it
  contains E1486's spectrum. That would prevent a spectrum refutation of
  E1486 → E1480.

[CentralComparisons.lean](../equational_theories/Spectrum/CentralComparisons.lean)
proves the new twice-square construction and the order-three exclusion. It also
proves the two conditional inclusions **with upper bounds retained as
hypotheses**; the E1485 hypothesis is now discharged by
`Spectrum.spectrum_1485` in
[WeakCentralSpectrum.lean](../equational_theories/Spectrum/WeakCentralSpectrum.lean).
The E1480 hypothesis remains conjectural. The order-three exclusion uses an explicitly tagged native
check of all 19,683 labeled tables. These additional bounds are imported by the
spectrum root, and the generated catalogue includes the proved E1485 formula.

The ordinary-axiom spectral negatives remain in the board. E1486 → E1483 at
order 11 is now excluded from checked counts because its large LRAT bundle is
not distributed; see the [proof status](definability_1483_order_eleven.md).
This pass adds no new completely-open negative from spectra. All six
laws in the three requested equivalence pairs have full spectrum.

## E3342/E3545: further searches

The [focused pass](definability_cube_focus.md) now contains the complete
E3342 → E3545 term-structural separation. The earlier searches below explain
why the separate factors and several natural families were insufficient.
They also produced uniform mutual recovery on a larger successor-and-group
family, with a 16-leaf recovery term.

The [model counter](../scripts/definability_cube_counts.cpp) finds identical
labeled model counts for the two laws:

| Order | Models of each law |
|---:|---:|
| 2 | 6 |
| 3 | 149 |
| 4 | 37,076 |
| 5 | 164,783,215 |

These are exploratory exact computations, not Lean cardinality theorems.
The counter groups cells using `m(x,y) = m(y,f(x))` for each possible cube map
`f`, then verifies that `f` is the appropriate actual cube map. The identity-map
case is counted separately using symmetric tables and their diagonals.
Orders two and three agree with independent exhaustive table enumeration.

Reversing the operation fails on known nine-element examples. A search against
18 models in each direction, including earlier candidate counterexamples,
examined one million distinct signatures in each direction without finding a
common target term. This is a bounded search, not a clone-exhaustion result.

A subsequent guided search found a 98-leaf E3342 → E3545 candidate, reduced to
42 leaves, that passed all 18 source models. A fresh eight-element model refutes
it. The [saved counterexample](../data/definability_3342_second_candidate_counterexample.json)
and [Lean check](../scripts/check_definability_3342_second_candidate.lean) preserve
this failure. The opposite operation satisfies E3545 on that countermodel, so
it does not refute the whole definability direction.

A further search used that new eight-element model and a nine-element model
where the opposite operation fails. It found E3545 companion operations with
exactly the same generated binary subalgebras, both within each factor and
between the factors. There are respectively 30, 2, and 4 distinct generated
relations. An [independent Python check](../scripts/definability_priority_check.py)
exhausts all pairs of generators and verifies these equalities. The
[saved companions](../data/definability_3342_mixed_companions.json) are not known
to admit common defining and recovery terms. The binary-relation test therefore
supplies neither a positive nor a negative general definability result.

## Validation

The complete definability and spectrum roots build. The two new separation
axiom guards, spectrum status assertions, and rejected-candidate guard pass.
The independent finite-data checker passes. The table audit was regenerated
with all ten closure propagations compared against the full-matrix reference.
The equivalence-gap matrices were rebuilt separately and matched the audited
source fingerprint.

```sh
lake build equational_theories.Definability equational_theories.Spectrum
lake env lean scripts/check_definability_3342_second_candidate.lean
OPENBLAS_NUM_THREADS=2 python3 scripts/definability_priority_check.py
OPENBLAS_NUM_THREADS=2 python3 scripts/definability_audit.py --check --verify-closure
g++ -O3 scripts/definability_cube_counts.cpp -o /tmp/cube_counts
/tmp/cube_counts 5
```
