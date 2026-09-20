# Finite symmetry and ring obstructions

20 September 2026. This pass returns to the open structural cells and to
possible upgrades of earlier term-structural negatives. Its strongest result is
**E1076 → E1313 is false even for one-way, parameter-free first-order
definability on finite carriers**. This also refutes term definability and both
structural relations, on finite and arbitrary carriers.

The pass adds **173 generating declarations**, all checked in Lean:

| Method | Negative relation | Declarations |
|---|---|---:|
| Rectangular and product symmetries | FO-structural | 22 |
| Finite-field symmetries | FO-structural | 116 |
| The 49-element zero-target family | One-way FO-definable | 1 |
| Matrix rings and a congruence subring | Term-structural | 5 |
| Truncated-polynomial rings | Term-structural | 26 |
| Complete invariant operation families | Term-structural | 3 |

The exact closure totals and validation results are recorded in the
[pass data](../data/definability_finite_symmetry_pass_summary.json)
along with every generating theorem and every newly closed class pair.

## The one-way FO upgrade

The two laws are

\[
\begin{aligned}
\mathrm{E1076}:&\quad x=y*((x*(x*y))*y),\\
\mathrm{E1313}:&\quad x=y*(((y*x)*x)*y).
\end{aligned}
\]

The [earlier twisted-recovery argument](definability_twisted_recovery.md)
separated them only in the term-structural boards. The new witness has
49 elements. Its operation is of the form
\(x*y=x+f(y-x)\) over \(\mathbb F_7[t]/(t^2+1)\), where
\(f(au)=af(u)\) for every nonzero cube \(a\).
This homogeneity condition does not require \(f\) to be linear.
With elements encoded as \(a+bt\), an explicit choice is
\(f(0)=0\), \(f(1)=6+6t\), \(f(2)=2+2t\), and \(f(3)=5t\).
The three nonzero cube cosets have representatives 1, 2, and 3, so these values
and cube homogeneity specify the entire function.

Translations and multiplication by nonzero cubes are automorphisms of the
source. A parameter-free definable operation must commute with them. There are
exactly **117,649** compatible binary operations: the value on the diagonal is
forced, and there are 49 choices on each of three nonzero difference orbits.
**None satisfies E1313**, while the saved source satisfies E1076.
Consequently even a target operation without recovery is impossible.

The proof is
[Field49NoTarget.lean](../equational_theories/Definability/Generated/Field49NoTarget.lean),
with an explicit operation table and orbit certificate in
[the witness data](../data/definability_orbit_field49_no_target.json).
Lean verifies the permutations, transport words, stabilizers, exhaustive
allowed-value lists, source law, and target exclusion. The field description
explains how the witness was found; the formal theorem depends only on the
checked finite certificate.

## Structural obstructions from symmetry

For mutual FO definability, the source and target must have the same
automorphisms. The method fixes some automorphisms of a source and enumerates
every operation commuting with them. If every target-law operation then has
an additional permutation as an automorphism, and the source does not, mutual
definability is impossible. Several probes can be used together when one
permutation does not distinguish all target operations.

[FiniteSymmetry.lean](../equational_theories/Definability/FiniteSymmetry.lean)
proves the general classification and obstruction. The classification uses
orbits of ordered pairs, transport words in explicit generators, and the
common fixed points of stabilizers. It does not assume that a search program
has found the full automorphism group. Every coverage claim is checked in Lean.

The successful families include rectangular structures on 16 elements,
products of cyclic structures, and translation-invariant operations over
finite fields. The first field batch provides 92 generating declarations
covering 142 candidate structural/finite class pairs. Its
[selection data](../data/definability_field_symmetry.json) records the source
operations and closure coverage. Further witnesses establish E727 → E4406 and
E635, E1447, E4438 → E838.
The later 125-element field witness adds E907 → E513; its stronger source
symmetries reduce the compatible family to 125 operations, with four target
models, all possessing the forbidden automorphism.

The independent checker normalizes a variable to zero only after checking
translation invariance. For four-coordinate witnesses, its reduction of
assignments also checks the required coordinate permutations. The Lean target
exclusions quantify over all assignments.

## Counting in rings and invariant families

A finite family of operations containing the two projections and closed under
composition forms a suitable family for term interpretation. If it has more
source-law operations than target-law operations, the finite product of its
source models cannot admit a target term operation with term recovery.
[CloneFamilyCounting.lean](../equational_theories/Definability/CloneFamilyCounting.lean)
provides this general argument. Counting is over the small operation family;
the resulting product magma need not be enumerated.

The new matrix and truncated-polynomial families are implemented in
[MatrixFamilyCounting.lean](../equational_theories/Definability/MatrixFamilyCounting.lean),
[TruncatedPolynomialRing.lean](../equational_theories/Definability/TruncatedPolynomialRing.lean),
and [ScalarFamilyCounting.lean](../equational_theories/Definability/ScalarFamilyCounting.lean).
The coefficient tests are proved equivalent to the original laws. The scalar
count reduces the constant coefficient to a multiplication-kernel size.
Strict cached coefficient arrays make the larger finite checks practical;
compiler rewrites have equality proofs.

Examples include E898 → E667 over three-dimensional vectors over \(\mathbb F_2\),
with **49 > 46** linear operations, and E690 → E55, E632, E642 over
\((\mathbb Z/4)^2\), with **528 > 205, 409, 205** affine operations.
Truncated-polynomial certificates use degrees up to eight, including
\(\mathbb F_2[\varepsilon]/(\varepsilon^8)\).

E1632 → E1045 uses the 729 matrices over \(\mathbb Z/9\) that are diagonal
modulo three. Among the **531,441** linear operations on \((\mathbb Z/9)^2\),
the source count is **3,564** and the target count is **3,133**. The full matrix
ring first revealed the obstruction; the proper subring gives a smaller
certificate. [CongruenceMatrixFamily.lean](../equational_theories/Definability/CongruenceMatrixFamily.lean)
represents its diagonal entries in \(\mathbb Z/9\) and its off-diagonal entries
as three times an element of \(\mathbb Z/3\). Four finite scalar identities
establish closure by ordinary matrix algebra. The independent checker also
verifies closure directly for every matrix pair.
[CongruenceMatrixFastTest.lean](../equational_theories/Definability/CongruenceMatrixFastTest.lean)
proves that coefficient evaluation in these four coordinates agrees with the
matrix law test, and supplies the faster decision procedure used in the counts.

Three further counts use complete families of operations commuting with
specified permutations. These are closed under composition without requiring
an affine description:

| Source → target | Carrier size | Family size | Source count | Target count |
|---|---:|---:|---:|---:|
| E48 → E1022 | 13 | 28,561 | 1,549 | 1,318 |
| E412 → E3254 | 13 | 28,561 | 2,197 | 1,549 |
| E618 → E3318 | 11 | 161,051 | 1,481 | 1,121 |

[InvariantFamilyCounting.lean](../equational_theories/Definability/InvariantFamilyCounting.lean)
proves closure using the complete symmetry classification. Its count test fixes
one variable to zero, with a proof that translations make this equivalent to
the full law.

## Board impact

| Board | New raw negatives | New class negatives | Remaining raw open | Remaining class open |
|---|---:|---:|---:|---:|
| S/fin | 1,068 | 231 | 407,722 | 53,749 |
| S/all | 1,068 | 231 | 443,472 | 60,352 |
| TS/fin | 414 | 72 | 20,649 | 4,153 |
| TS/all | 414 | 74 | 22,765 | 4,652 |
| TD/fin | 4 | 1 | 2,286 | 226 |
| TD/all | 4 | 1 | 1,302 | 267 |
| D/fin | 4 | 1 | 3,507 | 328 |
| D/all | 4 | 1 | 3,978 | 658 |

The same 1,068 raw pairs close on both S boards, and the same 414 on both TS
boards. The finite and arbitrary TS quotients have different positive
classes, explaining the 72 versus 74 class counts. No positive classes merge.
These figures overlap across relations and must not be added as independent
questions. The implication boards are unchanged.

The completely-open inventory and its closure-impact columns remain unchanged:
**32 raw pairs in nine TS/all class rows**. The one-way upgrade concerns a row
that the earlier twisted-recovery pass had already settled in TS.

The previous 234-pair and 191-pair counting batches retain their recorded
statuses. In particular, the strong E1076 → E1313 upgrade is outside those
batches; the projection obstruction to TD-negative upgrades of the 234-pair
batch still applies.

## Search boundaries

The finite-field searches checked complete translation-and-multiplier families,
including 1,048,576 operations over the 16-element field at multiplier index
five, and 262,144 over the 64-element field at index three. Further index-two
searches on 121, 125, and 169 elements found the additional E907 → E513 witness
at order 125. The other new hits in these larger searches were already covered
by this pass's certificates. Only the 49-element family supplied a new
zero-target obstruction.

The separate exact-automorphism search completed 41 families. Its order-31,
multiplier-index-three run was stopped without a result. The faster field
searches use selected permutation probes and do not claim to classify every
automorphism group. Their successful witnesses are justified by the exhaustive
orbit certificates, not by an assumption that the probes find every symmetry.

Larger truncated-ring searches also tested degrees ten and eleven over
\(\mathbb F_2\), degree seven over \(\mathbb F_3\), degree five over
\(\mathbb Z/4\), and degree three over \(\mathbb Z/8\) and \(\mathbb Z/9\).
They found no additional counting pairs beyond those already selected.

## Reproduction and scope

The independent Python checkers evaluate the laws directly and reproduce the
generated Lean certificate text. Native finite computations are named in
explicit axiom guards; the general mathematical reductions use the standard
Lean axioms. The congruence-subring reduction additionally uses its explicitly
guarded small scalar checks. The three largest symmetry modules have their
guards in
[LargeSymmetryAxioms.lean](../equational_theories/Definability/Generated/LargeSymmetryAxioms.lean).
Search output alone is never treated as a proof of a negative.

All **173** declarations and axiom guards passed, and the full Definability
entry point built successfully (**16,764 jobs**). All six independent
certificate checkers and **24 regression tests** passed. The audit matched all
**ten** closure computations against the full-matrix reference in 195.71 seconds.
The current source fingerprint, all **14** generated audit outputs, and all
**58** generated Lean files were verified afterward. The earlier counting-batch
upgrade audit also reproduced against the refreshed source fingerprint.

```sh
OPENBLAS_NUM_THREADS=2 python3 scripts/definability_orbit_certificates_check.py
OPENBLAS_NUM_THREADS=2 python3 scripts/definability_rectangular_symmetry_check.py
OPENBLAS_NUM_THREADS=2 python3 scripts/definability_ring_counts_check.py
OPENBLAS_NUM_THREADS=2 python3 scripts/definability_scalar_counts_check.py
OPENBLAS_NUM_THREADS=2 python3 scripts/definability_invariant_counts_check.py
OPENBLAS_NUM_THREADS=2 python3 scripts/definability_congruence_matrix_check.py
lake build equational_theories.Definability
python3 scripts/definability_imports.py --check
OPENBLAS_NUM_THREADS=2 python3 -m unittest discover -s scripts -p 'test_definab*.py'
OPENBLAS_NUM_THREADS=2 python3 scripts/definability_audit.py --write --date 2026-09-20 --verify-closure
```

These finite obstructions also apply to arbitrary-carrier definability. The
finite and arbitrary boards use different positive equivalence classes, so
their class-cell changes must be computed separately. Failed searches in the
listed families do not establish positive definability or rule out other
obstructions.
