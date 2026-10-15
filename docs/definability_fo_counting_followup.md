# Compactness counts with prescribed symmetries

Updated 2026-10-13. **Status: formalized in Lean.** This completes and extends
the 2026-09-21 pen-and-paper proposal. The catalogue directly refutes 63 arrows
that were open in the 2026-10-12 unrestricted FO-structural audit; the full
propagated impact is recorded below.

## The uniform compactness bound

[FOInvariantCompactness.lean](../equational_theories/Definability/FOInvariantCompactness.lean),
`FORecoveryCompactness.bounded_restricted_counts`, extends the existing finite-cover
argument to any family of operation tables preserved by parameter-free FO
definitions. If B is FO-structural from A on arbitrary magmas, there is a constant
K such that, for every nonempty finite carrier G and every such family P,

```text
#(A-tables on G satisfying P) ≤ K · #(B-tables on G satisfying P).
```

K is chosen before either G or P. Compactness supplies finitely many pairs of
forward/recovery formulas covering all A-models. Forward definability retains
membership in P, and each recovery formula recovers at most one source table
from a given target table. This gives the required injection into K copies of
the restricted target family.

In particular, P can prescribe any collection of automorphisms: parameter-free
FO definitions preserve them. The number of prescribed automorphisms may grow
with the carrier.

## Independent swaps of pairs

Take G = I × Bool, where I has m elements, and prescribe all independent swaps
of the Boolean coordinate in each pair. Let s(x) denote the partner of x.

An invariant operation can output only an element of an input's pair: swapping
an unrelated output pair would move the output while fixing both inputs. On
each pair, two bits determine the diagonal and partner entries. Its local
operation has the form

```text
f(a,b) = a XOR (d if a=b else p).
```

Equivariance determines the other entries in that pair. On an ordered pair of
distinct blocks, there are exactly four choices: x, s(x), y, or s(y). Consequently
the cross-block data have 4^(m(m−1)) independent choices.

Every term involving only one variable stays in its starting pair. If a unary
law admits c of the four Boolean local tables, its exact invariant-table count
is therefore

```text
c^m · 4^(m(m−1)).
```

[PairSwapCounting.lean](../equational_theories/Definability/PairSwapCounting.lean)
proves the full parameterization and its inverse (`invariantEquiv`), the exact
count (`invariant_count`), and the general separation criterion
(`not_structural`). `LocalHolds` checks both constant Boolean valuations; the
`unaryLaw` condition ensures these checks suffice for arbitrary valuations in
the assembled magma. Restriction to one pair proves the converse.

Here are the local counts for all unary laws, grouped by the existing
unrestricted FO-structural equivalence classes:

| Local count c | Representatives |
|---:|---|
| 2 | E3, E47, E614, E817, E3659, E4380 |
| 3 | E8, E99, E411, E1020, E1223, E1426, E3456 |
| 4 | E1, E151, E1629, E3253 |

A strict decrease in c refutes unrestricted FO structure. The shared
cross-block factor cancels, and no fixed K bounds (c_source/c_target)^m.
The Lean proof uses the binomial inequality and the explicit choice
m = K·c_target + 1, so this step needs no limits or asymptotic estimates.

## Newly refuted arrows

All arrows below are **source → target**, in the **unrestricted FO-structural**
sense. Every entry was open in the previous audit. Each is stated explicitly in
[PairSwapCountingCatalogue.lean](../equational_theories/Definability/PairSwapCountingCatalogue.lean),
with name `Equation<Target>_not_StructuralFrom_Equation<Source>_pairSwaps`.

| Source | Newly refuted targets |
|---:|---|
| E8 | E47, E614, E817, E3659, E4380 |
| E99 | E3, E47, E614, E817, E3659, E4380 |
| E151 | E99, E614, E817, E1020, E1223, E1426, E3456, E3659, E4380 |
| E411 | E614, E817, E3659, E4380 |
| E1020 | E614, E817, E3659, E4380 |
| E1223 | E3, E47, E614, E817, E3659, E4380 |
| E1426 | E3, E47, E614, E817, E3659, E4380 |
| E1629 | E99, E411, E614, E817, E1020, E1223, E1426, E3456, E3659, E4380 |
| E3253 | E99, E614, E817, E1020, E1223, E1426, E3456, E3659, E4380 |
| E3456 | E614, E817, E3659, E4380 |

This is not a finite-magma counting obstruction to model-dependent formulas:
each finite carrier can use different formulas, without a uniform bound on their
number. Compactness of the class of all A-models is essential. These proofs
therefore do **not** refute finite FO structure or one-way FO definability.

## Verification and audit

The three new Lean files total approximately 39 KiB. All 63 named negatives
have axiom guards allowing only `propext`, `Classical.choice`, and `Quot.sound`.
There are no `sorry`s, native-decide axioms, or SAT certificates in these proofs.
The only enumerations are of the four local Boolean operation tables.

The generic counting module built in 5.2 seconds and its catalogue in 25 seconds
in this workspace, with imported dependencies already built. These are observed
build times, not machine-independent performance claims.

Compared with the 2026-10-12 audit, the new negative generators and their
transitive consequences have this deduplicated impact:

| Unrestricted FO-structural measure | Before | After | Resolved |
|---|---:|---:|---:|
| Open raw directed equation pairs | 441,195 | 440,912 | 283 |
| Open directed pairs of current classes | 59,878 | 59,785 | 93 |
| Possible equivalence-class mergers | 991 | 904 | 87 |

There remain 737 proved unrestricted FO-structural classes. The 87 settlements
are separations of pairs that could previously still have merged, not class
collapses. All other relation boards, including finite FO structure, are
unchanged; the new unrestricted term-structural consequences were already known.
The completely-open inventory remains 20 raw pairs / six class pairs.

The full `lake build equational_theories.Definability` passed (17,249 jobs).
`definability_audit.py --write --verify-closure --date 2026-10-13` passed all ten
comparisons with full-matrix propagation and found no positive/negative clashes.
The regenerated audit fingerprint is
`4a69b7bf6eedf5133ecd921d0d2d3ad352429227acb252fd3b1a147e8307597f`.
The updated [FO equivalence inventory](definability_structural_equivalence_gaps.md)
records the remaining pairs.


The subsequent [finite-group and shared-fixed-point extension](definability_block_symmetry_counting.md)
adds 79 further explicit negatives, and completes separation among the 17
unrestricted FO-structural classes represented by one-variable laws. The totals
above record the earlier pair-swap checkpoint and exclude that later pass.
