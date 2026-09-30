# E677: the order-six exclusion and the effective tail at 164475

The two proofs contributed in [PR #6](https://github.com/Timeroot/equational_theories/pull/6)
are integrated under `equational_theories/Spectrum/Equation677/`. Their former
top-level files, `Order6.lean` and `SpectrumBound.lean`, have been removed. The
proofs use the project's `Magma`, `Equation677`, and `Law677.HasModel`, together
with Mathlib's finite types, cardinalities, minimal periods, and finite rings.

## No model of order six

`Spectrum.not_order_677_6` proves `¬ Law677.HasModel 6`. Left multiplication is
bijective by the existing E677 cancellation theorem. Its cycle through an
element has length at most six; the general division identities eliminate
lengths two and three, and the contributed equational case proofs eliminate
lengths four, five, and six. Every element would therefore be idempotent. The
last equational case proof rules out a six-element idempotent model as well.
These case proofs consist of equality rewriting and cancellation; they do not
assume the open finite implication E677 → E255 or trust a SAT solver.

`OrderSix/Basic.lean` supplies the division identities and finite counting
helpers; `Degree.lean` uses Mathlib's minimal-period theorem. `SixCycle.lean`,
`OtherCycles.lean`, and `Idempotent.lean` contain the case analyses. The local
left-associative `*` notation in these replay files denotes `Magma.op`; the
exported theorem uses the standard law and spectrum definitions.

## Every order at least 164475

`Spectrum.E677.EffectiveTail.all_large` proves
`∀ n, 164475 ≤ n → Law677.HasModel n`. Small scalar models, fourth-power models,
and products supply seeds. A transversal design with 81 groups is truncated
in two groups, producing orders `79q+s+r`, where `q,s,r` already have models
and `s,r ≤ q`; the cross-group blocks have idempotent models of sizes 79, 80,
and 81. The first certificate constructs a bitmap of 147485 positive orders
below 171623 (plus the empty carrier), including the complete interval starting
at 164475. A second extends
the interval through 13558000. A checked chain of 5263 further extensions
reaches the threshold for a simple strong induction: choose a group size
congruent to 1 modulo the product of the primes at most 79, and fill the
remaining hole with a smaller model. All finite certificates are evaluated
by Lean's kernel.

The port replaces the original hand-built enumeration, residue arithmetic,
cyclotomic ring calculations, and coordinate gluing with existing project and
Mathlib constructions. The packed bitmap and instruction lists are unchanged:

* `EffectiveTail/Affine.lean` interprets scalar certificates in `ZMod` and
  reuses the existing fourth-power construction.
* `Seeds.lean` retains the new 21-, 79-, and 127-element seeds, expresses the
  nine-element seed on `ZMod 3 × ZMod 3`, and reuses the existing 80- and
  81-element block models. The 79- and 127-element seeds are checked using
  translation symmetry, with only one displacement check per element.
* `Truncation.lean` uses `PBD.HasTD.cyclic` and `E677.design_model`, with a
  general theorem allowing any number of truncated groups.
* `Bitmap.lean` proves certificate soundness and the interval induction.
* `Data.lean` stores the contributed bitmap and packed construction steps.
* `Certificate.lean` checks the three stages. `EffectiveTail.lean` exports
  the bound and its proof-status audit.

This supersedes the former **42239519** numerical bound, which had not been
formalized. The exact spectrum below 164475 remains open. The new bound is a
sufficient cutoff, not a claim of optimality or nonexistence below it. The
catalogue includes the new tail, all positive orders in the checked bitmap,
seed orders, and the order-six exclusion, with
the same information transferred to the dual equation E2910.

Reproduce the proof checks with:

```sh
lake build equational_theories.Spectrum.Equation677.OrderSix
lake build equational_theories.Spectrum.Equation677.EffectiveTail
lake build equational_theories.Spectrum
lake env lean scripts/check_spectrum.lean
python3 scripts/spectrum_generate.py --check
```
