# The finite spectrum of E66

`Spectrum.exact_66` in `equational_theories/Spectrum/Equation66.lean` proves

\[
\operatorname{Spec}(E66)=\{n>0:n\equiv0\text{ or }1\pmod3,\ n\ne6\}.
\]

Both directions are complete in Lean. The catalogue also propagates this result
to E170, E177, and E281. No external design-existence theorem is assumed.

## Existence

`Spectrum/IdempotentLatin.lean` constructs an idempotent Latin square of every
positive order other than two. For odd order, use `L(x,y)=2x-y` on `ZMod n`.
For even order, start with the odd order `m=n-1` and adjoin a point `∞` along
the off-diagonal transversal `(x,x+1,x-1)`:

- `L'(∞,∞)=∞`;
- `L'(x,∞)=x-1`;
- `L'(∞,y)=y-2`;
- `L'(x,y)=∞` when `y=x+1`, and `2x-y` otherwise.

`Spectrum/Mendelsohn.lean` implements Bose constructions on `Q × Fin 3` and
`Option (Q × Fin 3)`. For each distinct `a,b` and level `i`, use the directed
triple `((a,i),(b,i),(L(a,b),i+1))`. Latin cancellation ensures that these triples
cover each directed pair between different fibres exactly once. Fill each
three-point fibre with a Mendelsohn system, or fill it together with the common
extra point using the four-point system. The Lean proof verifies the operations
directly using the Latin square's two divisions.

This gives orders `3k` and `3k+1` for `k=1` or `k≥3`. The universal singleton
and the existing modular E66 model of order seven fill the remaining orders.
Every idempotent semisymmetric operation satisfies E66 by substitution.

## Necessity

For any E66 operation, finite or infinite, the squaring twist
`b(x,y)=(x◇y)◇(x◇y)` is idempotent and satisfies `b(y,b(x,y))=x`.
`Mendelsohn.ofEquation66` proves this directly from E66.

On a finite carrier, the map `(x,y) ↦ (y,b(x,y))` has cube equal to the identity.
Its fixed pairs are exactly the diagonal. Counting fixed points modulo three
gives `n²≡n (mod 3)`, hence `n≡0` or `1`.

`Spectrum/MendelsohnSix.lean` excludes order six. A packed bit-vector table
represents every idempotent six-element operation; its entries are clipped to
the six-element carrier. The semisymmetry constraints are inconsistent, as
certified by `bv_decide`. The encoding lemmas connect this certificate to an
arbitrary Mendelsohn operation, so the argument does not rely on a search
failure or an unverified enumeration.

The finite certificate uses Lean's native LRAT checker. Its native computations
are explicitly registered with the spectrum audit, following the repository's
existing trust convention. The other arguments use ordinary Lean proofs.
`spectrum_assert exact_66 complete` checks that no pending proof or undocumented
axiom enters the exact theorem.

## Validation

```sh
lake build equational_theories.Spectrum
lake env lean scripts/check_spectrum.lean
lake env lean scripts/test_spectrum_status.lean
python3 scripts/spectrum_generate.py --check
```
