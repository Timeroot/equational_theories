# E670 cofiniteness and progress on E907

The [even-order research follow-up](e907_even_order_research_20260930.md) proves
the group-affine parity obstruction and three universal restrictions on left
translation cycles in Lean, and records further finite and construction searches.

## E670: cofiniteness proved in Lean

Every sufficiently large order admits an **idempotent** E670 model. This is a
complete Lean proof, with only `propext`, `Classical.choice`, and `Quot.sound`.
No numerical cutoff is asserted.

The existing idempotent models at orders 9, 11, and 16 fill the blocks of a
pairwise balanced design. The constructive design machinery gives eventual
periods 9·8 = 72, 11·10 = 110, and 16·15 = 240. Their gcd is 2. The singleton
and the order-16 seed occupy both parity classes; the proved fibre-completion
theorem therefore fills every sufficiently large order. Gluing the block
models preserves both E670 and idempotence. This proves the required instance
of design existence without assuming the general Wilson theorem.

Sources:

- `Spectrum/Equation670/Cofiniteness.lean`: `PBD.tail_9_11_16`,
  `E670.idempotent_tail`, and `E670.cofinite`.
- `Spectrum/NotePending.lean`: `Pending.cofinite_670` now uses the completed
  proof and is registered `complete`; its previous `sorry` is removed.

Of the 17 remaining exact-spectrum representatives, 15 now have a Lean proof
of cofiniteness. Full cofiniteness remains unresolved for E907 and E1483.

## E907: all sufficiently large odd orders proved in Lean

Every sufficiently large **odd** order admits an idempotent E907 model.
The proof needs only the two block sizes 3 and 23; the previously suggested
13-point seed is unnecessary. Their design periods 6 and 506 have gcd 2,
and the singleton completes the odd residue class. The same constructive
design and gluing theorems now give an unconditional Lean proof. No numerical
cutoff has been extracted. This is an existence theorem for odd orders, not
an exclusion of even orders or a proof of full cofiniteness.

Source: `Spectrum/Equation907/OddTail.lean`, especially
`E907.eventually_odd_idempotent` and `E907.eventually_odd`.
Both use only the standard axioms. The catalogue transfers the odd tail to
E907's dual, E2700, with an explicitly checked theorem and proof link.

## E907: order eight excluded

A new finite refutation rules out **every** eight-element E907 magma.
Neither idempotence nor right cancellation is assumed.

The identity is `x = y*((y*x)*(x*y))`. Consequently every left translation is
surjective, and on a finite carrier it is bijective. Fixing the element named
zero, conjugation puts its left translation into one of 45 canonical forms:
choose the length of the cycle containing zero and a partition of the other
cycle lengths. The identity permutation is included and must also be refuted.

The external SAT encoding has one output per table cell and one occurrence
of each output per row. Given `y*x=a` and `x*y=b`, it encodes the equivalence
`a*b=c ↔ y*c=x`. This equivalence follows from the original law and left
cancellation, now formalized as `E907.left_division`. All 45 forms were
refuted. The same encoding produced a seven-element model, checked directly
against the original law.

The Lean proof independently checks the normalization on all 8! permutations,
then checks each of the 45 bitvector/LRAT refutations. The magma-to-bitvector
bridge uses only row injectivity and the original E907 identity. The proof
uses the repository's explicitly registered native-computation trust boundary;
the Python solver's answer is not used as a Lean axiom.

Sources:

- `Spectrum/Equation907.lean`: left surjectivity, finite left injectivity,
  and the left-division equivalence.
- `Spectrum/Equation907Eight/Canonical.lean` and `CanonicalModels.lean`:
  exhaustive normalization and transport of models.
- `Spectrum/Equation907Eight/Cases/Row00.lean` through `Row44.lean`:
  all 45 refutations, including identity row 14.
- `Spectrum/Equation907Eight.lean`: `Spectrum.not_order_907_8`.

The proved excluded orders are now **2, 4, 5, 6, 8**. The first unresolved
even order is **10**. The general conjecture that all finite E907 models have
odd order remains open.

## Further search and reproduction

A bounded order-10 search tried all 97 canonical row forms at a 10,000-conflict
budget. It refuted 48 forms and left 49 unresolved. Increasing the budget to
100,000 for the first 16 unresolved forms found no additional resolution.
This is not a refutation of order 10. Short automated attempts to derive right
cancellation or general squaring-map injectivity also timed out; neither is
assumed in the proofs above.

```sh
python3 scripts/spectrum_907_row_search.py 7 8 \
  --output /tmp/907_rows.json
# An optional bounded follow-up, reporting unresolved cases honestly:
python3 scripts/spectrum_907_row_search.py 10 --seconds 300 \
  --output /tmp/907_ten.json

# Check that the generated Lean files match the construction:
python3 scripts/spectrum_907_eight.py

LEAN_NUM_THREADS=4 lake build equational_theories.Spectrum.Equation670.Cofiniteness \
  equational_theories.Spectrum.Equation907.OddTail \
  equational_theories.Spectrum.Equation907Eight
lake env lean scripts/check_spectrum.lean
```

The search requires `python-sat`. The saved positive sanity check, all order-8
case results, solver version, script hash, and budgets are in
`data/spectrum/907_row_search_20260930.json`.

Validation completed: the full spectrum build passed (3,982 jobs), and
`scripts/check_spectrum.lean` checked the declaration types and transitive
proof dependencies of all 4,694 catalogue entries, including the new odd-tail
transfers and order-eight exclusions. The catalogue and finite-proof generators
pass their consistency checks; all 18 overview tests and 11 spectrum-view tests
pass. The website deployment bundle has not been regenerated in this step.
