# Finite FO transfers and open spectra: 28 September 2026

Here `B → A` means that every finite B-magma has a parameter-free
FO-definable A-operation on the same carrier. A positive result would imply
`Spec(B) ⊆ Spec(A)`. A negative result does not by itself refute that spectrum
inclusion.

## Four proved FO negatives

All four statements below are proved in Lean with standard axioms only.

| Source B | Target A | Finite source witness | Lean module |
|---|---|---|---|
| E467 | E63 | `4x+32y` on F41², order 1681 | `Definability.GLTwoE467` |
| E704 | E63 | `21x+27y` on F29², order 841 | `Definability.GLTwo704` |
| E1110 | E63 | `6x+28y` on F29², order 841 | `Definability.GLTwoE1279` |
| E1279 | E63 | `4x+11y` on F29², order 841 | `Definability.GLTwoE1279` |

Every invertible linear map preserves each source. The shared theorem in
`Definability.GLTwoE63` proves that an E63 operation commuting with those
maps would force a root of `t⁵+t⁴+1`. This polynomial has no root in F29 or
F41. The argument allows nonlinear behavior on collinear pairs; it does
not assume that an equivariant operation is globally linear.

The negatives also settle the unrestricted FO directions and all stronger
interpretation variants. They rule out four proposed routes for transferring
spectrum information involving E63. Neither 841 nor 1681 is a spectrum
separation: E63 has models at these square orders.

Source-derived closure reduces the number of open finite FO directions
between classes from 318 to 314, and unrestricted FO directions from 648 to
628. These counts use the existing 88 finite and 108 unrestricted positive
FO-equivalence classes. No new positive equivalences or spectrum bounds are
claimed.

Detailed proofs, reductions, and reproducible search limits:

- [E467 and E1516](fo_467_1516_research.md)
- [E704 and E467](fo_704_467_research.md)
- [E1279 transfers and the shared obstruction](fo_1279_transfers_research.md)

## Main target: E1483 to E1485

**E1483 and E1485 are now separated as FO-structural equivalence classes,
both finite and unrestricted.** The theorem
`Definability.Cyclic1483.Equation1485_not_structuralFromFin_Equation1483` in
[Cyclic1483Structural.lean](../equational_theories/Definability/Cyclic1483Structural.lean)
uses an eight-element cyclic NAND source. Its coordinate rotation is an
automorphism, whereas three explicitly given reflections are not. Every
E1485 operation invariant under that rotation preserves at least one of
the reflections. Forward FO-definability preserves the rotation; backward
FO-definability would preserve that extra reflection in the source, a
contradiction.

The finite symmetry statement is checked by `bv_check` against a saved
15 MiB LRAT certificate. The final axiom guard lists the standard three
axioms and exactly one native BV checker axiom. There is no `sorry` or
unchecked external solver assertion. This proof is independent of the
unfinished conceptual classification of constant-row E1485 models.

This closes four raw directed cells, one class direction, on each
FO-structural board. The unresolved FO-structural equivalence-pair counts
decrease from 1049 to 1048 (finite) and 1001 to 1000 (unrestricted). The four
GL negatives above additionally close one finite and five unrestricted
FO-structural class directions between classes already known to differ.

**The one-way finite FO-definability direction remains open.**
A [32-element example](1483_fo_untwist_research.md)
now proves that universal cubic-automorphism untwisting is impossible.
Its full automorphism group is C2, so the only automorphism with cube equal
to the identity is the identity itself; the original operation fails E1485.
Nevertheless this source admits a different FO-definable E1485 companion.
Both assertions are proved in Lean in `Spectrum.Equation1483.NoCubicUntwist`.

Thus the counterexample rejects a construction strategy, not the desired
FO transfer or the square/twice-square conjecture for E1483.
The positive direction for every finite E1483 magma with a constant row is
now stated explicitly as `Spectrum.E1483.Constant.untwist_definable`, also
with a Lean proof using only standard axioms. The uniquely determined
constant in that construction does not act as a named parameter.

## Original positive-transfer targets still open

The searches did not settle E467 → E1516, E704 → E467, or E1279 →
E467/E704/E1110/E1516. The reductions and bounded failures are recorded in
the linked notes. In particular, exhaustion of a restricted algebraic
family or a solver timeout is not a nonexistence proof for the relevant
order or a refutation of FO-definability.

## Checks

```
lake build equational_theories.Definability equational_theories.Spectrum.Equation1483.NoCubicUntwist
lake build equational_theories.Spectrum.Equation1483.ConstantDefinability
python3 scripts/definable.py --query 1483 1485 --query 467 63 --query 704 63 --query 1110 63 --query 1279 63
python3 scripts/test_definable.py
python3 scripts/definability_imports.py --check
python3 scripts/spectrum_1483_untwist_obstruction.py
python3 scripts/definability_fo_1279_transfers.py
python3 scripts/fo_467_1516_research.py --scalar-only
python3 scripts/fo_704_467_research.py
```

The generated website bundle has not been regenerated in this research pass.
