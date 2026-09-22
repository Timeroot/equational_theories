# E695 and semisymmetric loops

The positive finite spectra of E695 and E887 are exactly

\[
\{n>0:n\equiv1\text{ or }2\pmod3,\ n\ne7\}.
\]

`Spectrum.exact_887` in `Spectrum/SemisymmetricLoop.lean` proves the formula for
E887. The existing `Spectrum.spectrum_695_eq_887` transports it to E695; the
catalogue proves the same formula for E1384, E1537, E1710, E1993, E2105, E2319,
E2755, and E3008. All ten exact-spectrum entries have `complete` status.

## Reduction to Mendelsohn systems

On a finite E887 magma, the identity gives surjective left translations and
hence cancellation. All squares are equal to an element `e`; substitution then
proves that `e` is a two-sided identity and `y◇(x◇y)=x`.

Remove `e`, keep the operation on distinct inputs, and set `x*x=x`. Cancellation
ensures that this operation stays in the smaller carrier. It is an idempotent
semisymmetric operation, hence a Mendelsohn quasigroup. Its order is `n-1`.
The directed-pair count gives `n-1≡0` or `1` modulo three, and the checked
six-point obstruction excludes `n=7`.

Conversely, adjoining a new identity to a Mendelsohn quasigroup and sending every
square to that identity produces an E887 magma. The completed E66 construction,
followed by its squaring twist, supplies every required Mendelsohn order. The
one-element model is handled separately.

There are no pending proof dependencies. The exceptional-order obstruction uses
the registered native LRAT checks from the E66 development; all other arguments
use ordinary Lean proofs.

## Validation

```sh
lake build equational_theories.Spectrum
lake env lean scripts/check_spectrum.lean
lake env lean scripts/test_spectrum_status.lean
python3 scripts/spectrum_generate.py --check
```
