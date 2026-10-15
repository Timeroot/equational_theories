# Reversible companions and pointed counts, 14 October 2026

This pass follows the [pointed identity counts](definability_pointed_identity_counts.md).
All arrows described as results below have Lean proofs. The counting arguments
concern unrestricted FO-structural recovery. The positive constructions work on
arbitrary carriers, so they also settle the corresponding finite arrows.

## Audited effect of this pass

The [machine-readable progress record](../data/definability_reversible_rounds.json)
compares the source fingerprints and all ten boards. The pass adds
**202 positive structural declarations** and **137 negative
structural declarations**. After taking closure with the existing results:

| Board | Open arrows before | Open arrows after | Arrows resolved | Proved classes before → after |
|---|---:|---:|---:|---:|
| Unrestricted FO-structural | 436,615 | 421,886 | **14,729** | **737 → 735** |
| Finite FO-structural | 406,129 | 404,841 | **1,288** | 711 → 711 |

The unrestricted gain consists of 7,076 newly positive and 7,653 newly negative
raw arrows. All 1,288 finite gains are positive. These are directed equation
pairs, excluding the diagonal; the two rows overlap and should not be added as
though they were distinct equation pairs. The other eight relation boards,
including term-structural and FO-definable, are unchanged.

The two proved class mergers are witnessed by E310 → E4272 and
E311 → E4300, together with the previously known reverse arrows. Unrestricted
possible class mergers fall from 707 to 604. The finite inventory still has
1,047 possible class mergers; its proved partition has not changed.

The full `lake build equational_theories.Definability` passed, including the
new standard-axiom guards. The independent reference-closure comparison passed
for all ten boards, and all 20 parser/closure regression tests passed. The Python
enumerator separately reproduced all 137 new local count gaps and the preceding 139 pointed-identity certificates.

## Constant unary terms give another counting obstruction

[ConstantTermBlockCounting.lean](../equational_theories/Definability/ConstantTermBlockCounting.lean)
handles laws of the form `s(x) = t(y)`. Use one common root and independent
regular group orbits. Require both unary terms to land at the root. Products
between different orbits remain completely free, so a local count can be
amplified to arbitrarily many orbits.

For example, with a two-element local group, E40 has 27 permitted local source
tables, whereas the necessary E3256 local tests admit only 26. With `m` orbits,
the common factor for cross-orbit products cancels, leaving a ratio `(27/26)^m`.
Compactness supplies a uniform finite bound on the number of formula pairs that
could recover the source from a companion. The growing ratio exceeds that
bound. This proves **E40 does not admit unrestricted FO-structural recovery
through E3256**.

The new constant-term families use E40, E316, E3282, E3485, E4276, and E4389.
Cyclic local groups of orders two, three, and four, and the Klein four group,
contribute 112 negative generators. Extending the preceding right-identity
construction to the cyclic group of order five contributes another 25.
The [137 certificates](../data/definability_constant_block_counts.json) are
reproduced by [the counting script](../scripts/definability_constant_block_counts.py)
and assembled in
[BlockCountingRoundTwoCatalogue.lean](../equational_theories/Definability/BlockCountingRoundTwoCatalogue.lean).

These are not finite FO-structural counterexamples: compactness is essential to
the uniform formula bound. The C2 arithmetic is kernel evaluated; the larger
local groups use `native_decide`. None of these certificates contains a `sorry`.

## Moving the diagonal into a zero row

[ZeroRowEncoding.lean](../equational_theories/Definability/ZeroRowEncoding.lean)
proves E4390 → E3485 and E4484 → E3473. Each source has a definable constant
`c` that is a left zero. Replace the diagonal by `c`, put the original square
of `y` in entry `(c,y)`, and keep every other entry. The new diagonal identifies
`c`, so the old diagonal can be read back from its row. The old zero row itself
is already known. Both directions of this encoding are quantifier-free.

The source laws force the additional identities needed for the indicated
targets. These constructions supply FO-structural positives even though their
finite term-structural counterparts were already refuted.

## Output permutations that preserve squares

[SquareColumnSwap.lean](../equational_theories/Definability/SquareColumnSwap.lean)
proves E310 → E4272 and E311 → E4300. Swap the square values `x*x` and `y*y`
in the output of `x*y`. This preserves the square map and is its own inverse.
The reverse arrows were already proved, so these settle two unrestricted
FO-structural class mergers. Their finite equivalences were already known.

[SquareSwapRecoveryCatalogue.lean](../equational_theories/Definability/SquareSwapRecoveryCatalogue.lean)
adds 15 generators by reusing existing target-law proofs. The old certificates
already proved the target law on arbitrary carriers; only recovery relied on
finiteness. The new
[recovery tactic](../equational_theories/Definability/SquareSwapRecovery.lean)
checks that the target-law proof is closed, checks the exact companion, and
replaces finite recovery with the proved involution. The resulting theorems
have standard-axiom guards.

The more general
[DiagonalOutputSwap.lean](../equational_theories/Definability/DiagonalOutputSwap.lean)
keeps the diagonal unchanged and swaps two output labels chosen from

```
x, y, x*x, y*y, (x*x)*(x*x), (y*y)*(y*y).
```

These labels depend only on the preserved square map. Consequently the swap
can be undone exactly, without cancellation or finiteness assumptions. An
optional opposite operation is undone by reversing the arguments in the label
expressions. Two or three such swaps compose, with the inverses applied in
reverse order; this is formalized in
[ComposedDiagonalSwaps.lean](../equational_theories/Definability/ComposedDiagonalSwaps.lean).
The intermediate magma need not satisfy another catalogue law.

This supplies new finite arrows as well as unrestricted upgrades.
Examples include E105 → E3456, E107 → E3456, E109 → E622, and E4381 → E643.
The last example leaves the **reverse finite arrow** open; the reverse
unrestricted arrow was already refuted. It does not establish a class merger.
The [saved proof data](../data/definability_diagonal_swaps.json) records the exact
swap sequence and proof for each selected generator. The
[emitter](../scripts/definability_diagonal_swaps.py) reproduces the
[Lean catalogue](../equational_theories/Definability/DiagonalSwapCatalogue.lean).

## A small unary submagma explains two harder cases

[CollapsedUnaryProducts.lean](../equational_theories/Definability/CollapsedUnaryProducts.lean)
proves that in an E4439 or E4476 magma, the submagma generated by any `x` has at
most the three elements `x`, `q = x*x`, and `c = q*q`:

| `*` | `x` | `q` | `c` |
|---|---|---|---|
| `x` | `q` | `c` | `c` |
| `q` | `c` | `c` | `c` |
| `c` | `c` | `c` | `c` |

Some of these elements may coincide. For E4439, all product rows with the same
left argument agree. Comparing the rows of the mixed cube and the square of
the square forces those two values to coincide. For E4476, eight instances of
the defining identity determine this table.

Only the two mixed-cube identities `x*q = q*x = q*q` are needed for the
E1426 construction. First swap `x` with the square of `y` in the output; then
swap `y` with the square of `x`, always preserving the diagonal. The resulting
operation sends both `(x,q)` and `(q,x)` to `x`, which proves E1426. This gives
E4439 → E1426 and E4476 → E1426 with short structural proofs, rather than large
case-search replays.

The E1224 → E3456 proof uses a different useful observation: every element
occurs in its own row. Applying the defining law to such a row witness proves
`x*((x*x)*x) = x`, which finishes the two-swap argument.

## Two further row-idempotence constructions

[AbsorptionRows.lean](../equational_theories/Definability/AbsorptionRows.lean)
proves E327 → E323. Write `q = x*x` and `t = x*y`. E327 gives
`x*t = q`, `x*q = q`, and `x*(y*y) = t`. Three output swaps simplify to

```
x ⋆ y = q                  if x = y,
        y                  if x*y = q,
        q                  if x*y = x,
        x*y                otherwise.
```

Each output is fixed by the new row. The construction keeps the original
square map, and the three swaps supply its inverse, so the result is
FO-structural on arbitrary carriers, including finite ones.

[ProductColumns.lean](../equational_theories/Definability/ProductColumns.lean)
proves E3363 → E323. Here the central observation is that a product `p = a*b`
has a constant column: `z*p = p*p`. Indeed, E3363 gives
`z*p = p*(b*(z*p))`, and its other instance gives `b*(z*p) = p`.
Three different output swaps make every product `p` a fixed point of each
new row other than its own. A short case analysis handles the diagonal and
shows that every row value is fixed. The public structural theorem, including
recovery, again has a standard-axiom guard.

## Search scope and verification

For each candidate examined, the permutation search checked every operation
table of orders two and three, then screened against the saved model archive
of orders four through twenty. This is not an exhaustive search over definable
constructions or all source–target pairs. The latter archive is not exhaustive. Vampire was used
to discover target-law proofs; its output is not trusted by the catalogue.
Source-only algebraic lemmas are replayed in Lean by superposition, and Lean
checks the final case analysis. Every public positive theorem has an axiom
guard admitting only `propext`, `Classical.choice`, and `Quot.sound`.

A countermodel to a proposed companion only rejects that companion, not the
FO-structural arrow. Unsuccessful searches and ATP proofs not ported to Lean
are not inserted as resolved arrows.

[LocalCountNormalization.lean](../equational_theories/Definability/LocalCountNormalization.lean)
reduces counting work by translating the first non-root variable to the group
identity. It proves this reduction for arbitrary groups. Expanding each target
law before evaluation also removes unused variables and repeated term
interpretation. For the same C5 module, these changes reduced the observed
build time from 2,259 seconds to 206 seconds. A later full rebuild, running
alongside the audits, took 282 seconds for C5. The count values are unchanged.

See the [current audit totals](definability_open/summary.md),
[FO equivalence gaps](definability_structural_equivalence_gaps.md), and
[term-structural equivalence gaps](definability_term_structural_equivalence_gaps.md)
for current totals and source fingerprints.

## Leads that did not reach a checked result

The three-swap search also found ATP proofs for E960 → E323 (hence E3306).
These have not been added as new facts: replaying their unrestricted algebraic
argument is still unfinished. E960 already implies E364,
`(y*x)*x = x*x`, and its square map is injective. The first identity makes most
of the prospective companion's outputs fixed. Those two facts alone did not
finish the collision cases involving `y*y`; a further consequence of E960 is still
needed. The tested recipe first takes the opposite operation and then swaps
output labels `(x*x,x)`, `(x,y*y)`, and `(y*y,y)`, preserving the diagonal at
every step. This is a useful small remaining proof task, rather than a new negative
result or a completed construction.

The finite equivalence question E4381 versus E643 also remains worthwhile:
the new construction proves E4381 → E643, but finite recovery in the reverse
direction is open. The unrestricted reverse direction is already refuted, so
any successful reverse proof must use finiteness.
