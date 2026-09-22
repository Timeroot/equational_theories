# E546, E949, and affine Gaussian modules

The positive finite spectrum is exactly

\[
\{a^2+b^2>0:a,b\in\mathbb N\}.
\]

`Spectrum.exact_546` in `Spectrum/Equation546.lean` proves both directions.
The existing implication and parastrophic equivalences transport it to E556,
E749, E775, E949, E962, E1098, E1131, E1301, E1355, E1764, E1790, E1913, E1967,
E2370, E2383, E2511, E2586, E2722, E2776, E2928, E2982, E3128, and E3185.
All 24 catalogue entries are now complete. The former Gaussian representation
gap is resolved, including for infinite carriers.

## Reconstructing the module

For any E546 operation, choose an anchor `a` and put `e=a◇a`. Define

\[
x+y=(x\mathbin\diamond a)\mathbin\diamond
       (a\mathbin\diamond(y\mathbin\diamond e)),\qquad
J(x)=(e\mathbin\diamond e)\mathbin\diamond x.
\]

`Spectrum/GaussianRepresentation.lean` proves that this addition makes the
carrier an abelian group, with zero `e` and negation `J²`. The map `J` is additive,
invertible, and satisfies `J²(x)=-x`. The original operation is recovered as

\[
x\mathbin\diamond y=-x+J(y)+c,\qquad c=e\mathbin\diamond e.
\]

The full `Module GaussianInt G` structure is defined by
`(r+s*i) • x = r • x + s • J(x)`. Thus this is a formal module reconstruction,
not an assumption that every model is affine. No finiteness assumption is used.

`Spectrum/GaussianIdentities.lean` contains the algebraic derivations needed for
the reconstruction. Vampire selected the derivations; Lean replays each step.
Building the repository requires no external prover for these identities.

## Necessity by permutation parity

Let `p≡3 (mod 4)` be prime. The Sylow `p` subgroup of a finite abelian group is
characteristic, so `J` restricts to it. Write its order as `p^v`.

Inversion on this odd-order subgroup fixes only the identity and exchanges the
other elements in pairs. Its sign is therefore `(-1)^((p^v-1)/2)`. Inversion is
also the square of the permutation `J`, so its sign is positive. Consequently
`p^v≡1 (mod 4)`, forcing `v` to be even. Mathlib's sum-of-two-squares criterion
then proves that the whole group order is a sum of two squares.

This argument is formalized in `Spectrum/GaussianCardinality.lean`. It avoids a
classification of finite Gaussian modules or a calculation of ideal norms.

## Existence

Mathlib proves that a sum of two squares can be written `a²*b`, where `-1` is a
square modulo `b`. On `(ZMod a)²`, use the rotation `J(x,y)=(-y,x)`. On `ZMod b`,
use multiplication by a chosen square root of `-1`. In both cases, `-x+J(y)`
satisfies E546. Their product gives the desired order `a²*b`.

`Spectrum/GaussianModels.lean` checks these operations and cardinalities.
The representation, construction, and cardinality arguments use only standard
Lean axioms: no `sorry`, native computation, or SAT certificate is needed.

## Validation

```sh
lake build equational_theories.Spectrum
lake env lean scripts/check_spectrum.lean
lake env lean scripts/test_spectrum_status.lean
python3 scripts/spectrum_generate.py --check
```
