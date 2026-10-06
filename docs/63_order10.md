# E63 has no model of order ten

The completed theorem is [`Spectrum.not_order_63_10`](../equational_theories/Spectrum/Equation63/OrderTen/Exclusion.lean).
It has no `sorry`. The proof has three mathematical reductions and one small
finite refutation. No model search runs during a Lean build.

## Mathematical reduction

Suppose a finite operation `◇` satisfies E63,
`y ◇ (x ◇ (x ◇ y)) = x`. Every left translation is surjective and hence
bijective. Define `x*y` by left division: `x ◇ (x*y) = y`. Then
`x*y = y ◇ (y ◇ x)`, and substitution gives

```
(x * (x * y)) * x = y.                 (E229)
```

This new operation is a quasigroup. Its left translations are injective by
the displayed identity; its right translations are surjective, hence
injective by finiteness. Writing them as `Lₓ` and `Rₓ`, the identity says
`Rₓ = Lₓ⁻²`. Two useful consequences have short proofs:

* `Lₓ³(x)=x`: cancel the right translation in E229 at `(x,x*x)`.
* There are no two-cycles of `Lₓ`. If `x*y=z` and `x*z=y`, E229 gives
  `y*x=y`. Since `Lᵧ³(y)=y`, left cancellation gives `y*(y*y)=x`.
  E229 at `(y,y)` now gives `x*y=y`, so `z=y`.

These are ordinary Lean proofs in
[`OrderTen/Basic.lean`](../equational_theories/Spectrum/Equation63/OrderTen/Basic.lean).

## Symmetry breaking without permutation enumeration

If some element is non-idempotent, label one such element 0; otherwise all
elements are idempotent. Thus we may assume the conditional rule
`0*0=0 → ∀x, x*x=x`.

Now label the cycles of `L₀` consecutively, starting with the cycle containing
0. The resulting first row satisfies `(0*i).val ≤ i.val+1`. The proof of this
normalization works for functions on `Fin n` at every size, not just
permutations of ten points. Inductively, if `f(i)>i+1`, swap the labels `f(i)`
and `i+1`. All earlier inputs and outputs are at most `i`, so this preserves
every previously established inequality and fixes 0. Conjugating the entire
operation preserves both E229 and the conditional diagonal rule.

[`OrderTen/Normalization.lean`](../equational_theories/Spectrum/Equation63/OrderTen/Normalization.lean)
proves both steps. There is no exhaustive check of permutations and no list
of canonical row cases to trust or replay.

## Finite certificate and trust boundary

The 1,000 Boolean atoms encode `x*y=z` for ten possible values of each
variable. The clauses express the Latin property, E229, the two translation
consequences above, and the two normalization rules. Cancellation supplies
two redundant propagation clauses for each E229 instance. After removing
tautologies there are **45,525 clauses**.

[`OrderTen/Encoding.lean`](../equational_theories/Spectrum/Equation63/OrderTen/Encoding.lean)
proves, for arbitrary operations, that every normalized model satisfies this
CNF. CaDiCaL refutes it in about three seconds on the development machine.
The trimmed LRAT proof is stored as a **4.7 MB gzip file**. Lean's proved
`LRAT.check_sound` turns successful certificate checking into unsatisfiability.
The checker is evaluated by `native_decide`, explicitly tagged
`@[spectrum_native]`, following the repository's existing trust policy.
Thus this is a complete Lean proof with a declared native-computation
dependency, not a kernel-reduction-only proof and not a trusted UNSAT claim
from the external solver. Gzip decompression merely supplies the proof data.

The certificate module took about **6 seconds** to rebuild in the local timing
probe (including imports and elaboration). Ordinary builds replay that saved
certificate; they do not rerun CaDiCaL or its proof trimmer. The generator
records hashes in both the JSON metadata and generated Lean source, so
regenerating the certificate invalidates the corresponding Lake cache.

Reproduce or verify the saved materials with:

```sh
python3 scripts/spectrum_63_ten_certificate.py         # check hashes / render
python3 scripts/spectrum_63_ten_certificate.py --solve # optional new SAT run
lake build equational_theories.Spectrum.Equation63.OrderTen.Separation
```

## Spectrum consequence

E115 has a model of order 10 by its proved spectrum `positiveExcept {2,6}`.
[`OrderTen/Separation.lean`](../equational_theories/Spectrum/Equation63/OrderTen/Separation.lean)
therefore proves `¬ Law115.Subspectral Law63`, `Law63.spectrum ≠ Law115.spectrum`,
and `¬ Law63.DefinableFromFin Law115`. The individual exclusion at 10 is
marked `PROVED` in the catalogue and transferred to every law in the E63
spectrum family. Order 14 remains a separate pending exclusion; it is not
used anywhere in these results.
`Definability/Equation63Spectrum.lean` also registers the obstruction with
the definability board, where closure propagates it to stronger relations
and both finite and unrestricted variants.
