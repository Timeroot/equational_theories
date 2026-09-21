# Confluence and unary endomorphisms

Date: 2026-09-21. Arrows are source → target.

Nine new unrestricted term-structural negatives are proved in Lean:

| Source | Target | Effect | Lean declaration |
|---:|---:|---|---|
| 115 | 880 | Separates a remaining possibly-infinite equivalence pair  [`Equation880_not_termStructuralFrom_Equation115_confluence`](../equational_theories/Definability/Confluence115Recovery.lean#L324) |
| 477 | 1492 | Separates a remaining possibly-infinite equivalence pair  [`Equation1492_not_termStructuralFrom_Equation477_confluence`](../equational_theories/Definability/Confluence477Recovery.lean#L204) |
| 680 | 1695 | Separates a remaining possibly-infinite equivalence pair  [`Equation1695_not_termStructuralFrom_Equation680_confluence`](../equational_theories/Definability/Confluence680Recovery.lean#L221) |
| 115 | 4273 | Closes another finite-positive, unrestricted-open cell  [`Equation4273_not_termStructuralFrom_Equation115_confluence`](../equational_theories/Definability/ConfluenceCrossedInverse.lean#L188) |
| 477 | 4273 | Closes another finite-positive, unrestricted-open cell  [`Equation4273_not_termStructuralFrom_Equation477_confluence`](../equational_theories/Definability/ConfluenceCrossedInverse.lean#L191) |
| 680 | 4273 | Closes another finite-positive, unrestricted-open cell  [`Equation4273_not_termStructuralFrom_Equation680_confluence`](../equational_theories/Definability/ConfluenceCrossedInverse.lean#L194) |
| 481 | 1496 | Separates a remaining possibly-infinite equivalence pair  [`Equation1496_not_termStructuralFrom_Equation481_confluence`](../equational_theories/Definability/Confluence481Recovery.lean#L204) |
| 481 | 1492 | Closes another finite-positive, unrestricted-open cell  [`Equation1492_not_termStructuralFrom_Equation481_confluence`](../equational_theories/Definability/Confluence481Recovery.lean#L212) |
| 481 | 4273 | Closes another finite-positive, unrestricted-open cell  [`Equation4273_not_termStructuralFrom_Equation481_confluence`](../equational_theories/Definability/Confluence481Recovery.lean#L215) |

All nine directions remain positive for finite term-structural interpretation.
These results make no new FO-structural or one-way term-definability claim.

The unrestricted equivalence inventory falls from 32 to **28 class pairs**,
and from 152 to **136 raw unordered equation pairs**. The proved class counts
remain 739 unrestricted and 716 finite. Closure adds **60 directed raw
negatives in ten class cells**: the nine displayed cells and E873 → E4273.
At this TS-only checkpoint, the other nine relation boards were unchanged.
The subsequent [FO counting pass](definability_fo_compactness_counting.md) and
[column repair](definability_cube_column_repair.md) add separate structural results.

## The normal-form obstruction

The existing confluent constructions for E115, E477, and E680 give magmas of
normal-form binary trees. For these models, a unary term that is also an
endomorphism must be the identity.

The key comparison evaluates the same unary term at two distinct generators
`a,b` and at their product `a*b`. Substitution of a generator by a single leaf
or by the pair of distinct leaves commutes with normalization. Consequently,
all three evaluations have the same unary normal-form shape `t`.

If the unary term preserves multiplication, substitution of `a*b` into `t`
equals the product of the copies of `t` in `a` and in `b`. A nontrivial shape
would put both leaf labels on one side of this equality and only one on the
other. The rewrite rules cannot erase this mismatch. Thus `t` is a variable.
The endomorphism then fixes every tree because it fixes the generators.

[Confluence115Recovery.lean](../equational_theories/Definability/Confluence115Recovery.lean)
contains the elementary tree-substitution lemmas and the first application.
[ConfluenceTermEndomorphism.lean](../equational_theories/Definability/ConfluenceTermEndomorphism.lean)
packages the argument for the other normal-form models. The result concerns
endomorphisms given by unary terms; it does not classify arbitrary or
first-order-definable endomorphisms.

In E880, squaring is an endomorphism. A reversible interpretation would make
it an endomorphism of the E115 source too. Squaring would therefore fix a
source generator. Every term of that companion fixes this generator on the
diagonal, contradicting the source's nonidempotence.

## Cubing and homomorphic images

In E1492, left cubing `x*(x*x)` is an endomorphism. In E1695, right cubing
`(x*x)*x` is an endomorphism. E4273, the right crossed-inverse law, also makes
left cubing an endomorphism. The same normal-form argument makes these maps
identities. The resulting companions satisfy the semisymmetric law E14.

[TermRecoveryHom.lean](../equational_theories/Definability/TermRecoveryHom.lean)
proves that reversible term interpretations pass to surjective homomorphic
images. Both defining terms are retained, and surjectivity transfers the
target law. Evaluating the normal-form trees onto suitable algebraic models
therefore gives a contradiction:

* For E477, use the existing Gaussian model `x*y = i*(x-y)`. An E14 companion
  also satisfies E680, and the earlier Gaussian recovery obstruction excludes it.
* For E680, use rational dual numbers, with `ε²=0`, and
  `x*y = (-1+ε)*x + (-1-ε)*y`. Every linear E14 operation has coefficients
  `-1,-1`; it preserves the rational subring, whereas the source does not.
* For the E115 crossed-inverse application, use dual numbers over `ZMod 7`,
  with coefficients `a=-(5+ε)²` and `b=5+ε`. Every linear E14 companion has
  zero ε-coefficients and preserves the constant subring. The source does not.

The last model has 49 elements. It is an algebraic image used inside an
infinite-source argument, so it does not refute any of the nine finite positive
directions in the table.

The main modules are
[Confluence477Recovery.lean](../equational_theories/Definability/Confluence477Recovery.lean),
[Confluence680Recovery.lean](../equational_theories/Definability/Confluence680Recovery.lean),
and [ConfluenceCrossedInverse.lean](../equational_theories/Definability/ConfluenceCrossedInverse.lean).
The auxiliary algebraic obstructions are in
[DualNumberRecovery.lean](../equational_theories/Definability/DualNumberRecovery.lean)
and [DualSevenRecovery.lean](../equational_theories/Definability/DualSevenRecovery.lean).
Each exported negative has a transitive axiom guard allowing only `propext`,
`Classical.choice`, and `Quot.sound`.

## The pointed E481 extension

E481 has a common square, so its normal forms need a distinguished constant
leaf. The three rules are `y*(x*(y*0)) → x`, `0*(x*0) → x`, and `x*x → 0`.
[PointedConfluence481.lean](../equational_theories/Definability/PointedConfluence481.lean)
checks the model and the substitution argument with this constant retained.
At a chosen generator, a unary term endomorphism must return that generator
or the constant. A variable-free normal form reduces to the constant; a normal
form containing the variable gives the same two-label contradiction as above.

The [recovery application](../equational_theories/Definability/Confluence481Recovery.lean)
uses the Gaussian quotient again. In a linear companion `a*x+b*y`, left cubing
at 1 is `a+b*(a+b)`, so it must be 0 or 1. E1496's coefficient equations exclude
both cases. For E1492 and E4273, the allowed coefficients are real; the companion
then cannot term-recover the source operation `i*(x-y)`.

The quotient-transfer API retains the actual companion homomorphism, which is
needed to transfer the value of cubing at the chosen generator. The rewrite-rule
macro also now handles branches closed by constant-pattern discrimination.
The full root build checks all existing users of that macro.

## Validation

At the TS-only checkpoint, the full 16,991-job `Definability` build passed,
all ten quotient closures matched the full-matrix reference, and the 19
bookkeeping tests passed. The [combined report](definability_fo_compactness_counting.md)
records the final validation after the FO additions. The before/after
audit comparison confirmed the 60 new negatives with no other relation changes
at that checkpoint.

No result is inferred from an ATP timeout. The preliminary square-endomorphism
probes for E910, E1729, E1323, E1526, E1722, E917, E883, E125, E714, E1316,
E1692, E476, E503, and E118 timed out. E504 and E1086 admit counterexamples to
that particular square-endomorphism identity. These probes did not change the
boards.
