# Small-order results from the positive-model search

The requested E1076 positive searches at orders 9 and 11 instead produced
small complete refutations. Both exclusions are now checked in Lean. The
broader order-12 campaign also produced Lean exclusions for E704, E1279, and
E1516. No new positive model was found in the E1076 branch of the campaign.

| Law | Excluded order | Compressed certificate | Lean replay |
|---|---:|---:|---:|
| E1076 | 9 | 33,552 bytes | 4.5 s |
| E1076 | 11 | 2,216,104 bytes | 141 s |
| E704 | 12 | 291,580 bytes | 23 s |
| E1279 | 12 | 1,358,908 bytes (35 cases) | ~38 s parallel build |
| E1516 | 12 | 747,704 bytes | 72 s |

Times are normal `lake build` measurements with dependencies already built;
concurrent work can affect them. E1279 now uses a squaring-permutation decomposition and direct table encoding;
its original single certificate required 477 seconds. See [the proof note](1279_order12.md). The declarations are
`Spectrum.not_order_1076_9`, `Spectrum.not_order_1076_11`,
`Spectrum.not_order_704_12`, `Spectrum.not_order_1279_12`, and
`Spectrum.not_order_1516_12`.

Apart from the new direct E1279 encoding, these use the unrestricted
`SmallOrders.Encoding` (and `SmallOrders.SquareOuter` for E1516), including its proved cancellation and
first-row normalization. CaDiCaL produces LRAT data; Lean trims the data and
checks reconstructed proofs with its verified LRAT checker. The public
declarations have no `sorry` dependency. Their only extra computational axioms
are registered `spectrum_native` checks. Hashes, compressed sizes, and provenance
are in `data/spectrum/positive_target_exclusions_20261011.json`.

```sh
python3 scripts/spectrum_positive_target_exclusions.py
python3 scripts/spectrum_positive_target_exclusions.py --solve --only 1076
lake build equational_theories.Spectrum.SmallOrders.Certificates.E1076N9 \
  equational_theories.Spectrum.SmallOrders.Certificates.E1076N11
```

The audit command checks hashes and generated wrappers. Regeneration limits
raw proof files to 1 GiB and rejects compressed certificates above 10 MiB.

## E1076 at order 12: completed in Lean

`Spectrum.not_order_1076_12` now excludes order twelve with **nine certificates
totaling 5,114,400 bytes (4.88 MiB)**; each checks in **4–24 seconds**.
The mathematical proof first reduces the left translation to six possible
cycle types. Residual row symmetries reduce the choices for `1*0`. Excluding
the three types containing a three-cycle then gives an order-specific
no-three-cycle lemma, which strengthens the remaining cases. This replaces
the earlier 13,210,900-byte candidate bundle.

See [the complete proof note and reproduction instructions](1076_order12.md).
The strengthened encoding, coverage, symmetry reductions, and final exclusion
are all formalized without `sorry`. All nine Python CNFs exactly match Lean's
exports. The original unrestricted and idempotent searches timed out after
900 seconds, and Mace4 after 600 CPU seconds; those exploratory timeouts do
not contribute to the proof. The earlier six-case search logs remain recorded
in `data/spectrum/e1076_positive_search_20261011.json`.

```sh
python3 scripts/spectrum_1076_twelve_certificate.py
lake build equational_theories.Spectrum.Equation1076.OrderTwelve.Exclusion
```

## Restricted constructions

For order 12, operations admitting a regular automorphism group were checked
for `A4`, `C3 × C2 × C2`, and the dihedral group of order 12. These have the form
`x * y = x f(x⁻¹y)`. Each entire restricted family was UNSAT in under a second.
The search removes the ordinary first-row normalization before imposing the
group symmetry, because that normalization need not preserve the fixed group
labels. Reproduce these runs with
`scripts/spectrum_1076_regular_search.py --group A4` (or `C3V4`, `D12`).

Commutative E1076 models at 9 and 11 were also immediately UNSAT. At even order,
commutativity is impossible already for any idempotent quasigroup: each symbol
appears exactly once on the diagonal, while all its off-diagonal occurrences
come in symmetric pairs. Associativity or a one-sided identity also forces an
idempotent quasigroup to be a singleton, so those restrictions cannot yield
positive models at the target orders.

## E467 at order 12: completed and compressed

The original unsplit refutation (6.2 MiB, over ten minutes of Lean replay)
was replaced by twenty squaring-cycle cases using existing algebraic lemmas.
The complete Lean proof now totals **429,380 bytes**, and its normal build
with dependencies cached takes **16.84 seconds**, including final assembly.
See [the dedicated proof note](467_order12.md).
