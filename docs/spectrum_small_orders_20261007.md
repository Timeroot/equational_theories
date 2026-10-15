# Orders eight and ten: eleven new exclusions

Date: 2026-10-07. All exclusions below have complete Lean proofs.

**Later follow-up:** order ten is also excluded for E907, E1083, and E1486.
Only E670 and E677 remain open there. See the
[follow-up proof and search notes](order_ten_followup_20261007.md).
The tables below record the original eleven-exclusion pass.

The pass excludes order **8** for **E670, E1076, E1286**, and order **10** for
**E467, E704, E1076, E1110, E1279, E1286, E1313, E1516**.
Duality gives 22 new equation/order exclusions in the catalogue.

Order eight is now decided for all 17 unresolved-spectrum representatives.
At order ten only **E670, E677, E907, E1083, E1486** remain open.
The bounded searches found no model of these orders; their timeouts are not
nonexistence results. No new positive witness was found in this pass.

| Representative | Order 8 | Order 10 |
|---|---|---|
| E63 | Exists | Impossible |
| E467 | Exists | Impossible |
| E667 | Exists | Exists |
| E670 | Impossible | Open |
| E677 | Impossible | Open |
| E704 | Exists | Impossible |
| E883 | Exists | Exists |
| E907 | Impossible | Open |
| E1076 | Impossible | Impossible |
| E1083 | Exists | Open |
| E1110 | Exists | Impossible |
| E1279 | Exists | Impossible |
| E1286 | Impossible | Impossible |
| E1313 | Impossible | Impossible |
| E1483 | Exists | Impossible |
| E1486 | Impossible | Open |
| E1516 | Exists | Impossible |

## Spectrum arrows

The new order-eight exclusion proves

```lean
Spectrum.SmallOrders.not_subspectral_167_670 : ¬ Law167.Subspectral Law670
```

E167 has every positive order congruent to 0 or 1 modulo 4, including 8.
E670 has no eight-element model. This closes one previously unknown arrow
between spectrum classes: **{E167, E501, E3106} → {E670, E2937}**,
or six directed equation pairs. The forward finite FO-definability arrow was
already refuted independently, so the pass adds no new definability-board cells
and resolves no additional possible equivalence-class merges.

The named spectrum and finite-FO obstructions are in
[SmallOrders/Separation.lean](../equational_theories/Spectrum/SmallOrders/Separation.lean).
The spectrum viewer derives the same negative from the model and exclusion
once the deployment data is refreshed.

## Mathematical reduction

Ten certificates use a shared chain-law encoding. Write the identity as
`y * last(x,y,middle(x,y)) = x`. The identity explicitly supplies a preimage
under each left translation. On a finite carrier every left translation is
therefore bijective. When the last inner operation is a right translation,
left cancellation also gives surjectivity, hence bijectivity, of the right
translations. E704 has a separate existing cancellation proof. For E704,
E1110, and E1279 the first variable appears only through its square; equality
of squares therefore implies equality of those variables, so squaring is
bijective as well. These are proved consequences, not search assumptions.

If a non-idempotent element exists, name it zero. Then relabel the orbit of
its left translation and the remaining points consecutively. The normalized
table satisfies `f(0,y) ≤ y+1`, and `f(0,0)=0` implies that the entire table
is idempotent. Every model has such a labelling; the idempotent branch remains
in the search. No extra commutativity or associativity is assumed.

Atoms `p(x,y,z)` record `x*y=z`; `q(x,y,z)` records the two-operation middle
subterm. Each atom family has exactly one output. Eliminating the outermost
operation by cancellation leaves only two layers of clauses. Further inverse
clauses express that either input to an injective translation is recovered
from its output. These redundant mathematical constraints make the refutation
substantially smaller. For E704/10, adding the right-translation and squaring
constraints reduced the compressed certificate from about 4.2 MB to 91 KB;
the inverse clauses reduce it further to about 27 KB.

All these steps are formalized in
[Chain.lean](../equational_theories/Spectrum/SmallOrders/Chain.lean) and
[Encoding.lean](../equational_theories/Spectrum/SmallOrders/Encoding.lean).

E1516 has a square at the head of the outer operation:
`x = (y*y)*(x*(x*y))`. Its existing finite cancellation theorem proves that
both translations and squaring are bijective. The square-headed encoding
uses these facts directly, with `q(x,y,z)` recording `x*(x*y)=z`.
[SquareOuter.lean](../equational_theories/Spectrum/SmallOrders/SquareOuter.lean)
proves its clause soundness and the same normalization; its order-ten
certificate is about 130 KB.

## Certificates and checking

The external solver supplies LRAT data. Lean proves that every hypothetical
model satisfies the encoded formula, then uses `LRAT.check_sound` to refute it.
Certificate checks use the repository’s explicitly registered `native_decide`
trust boundary. Every exported exclusion has a transitive
`spectrum_assert ... complete` guard. None contains a `sorry`, and ordinary
builds replay saved certificates without invoking a SAT solver.

| Law | Order | Compressed bytes | Lean theorem |
|---|---:|---:|---|
| E670 | 8 | 1,478,386 | `Spectrum.not_order_670_8` |
| E1076 | 8 | 25,247 | `Spectrum.not_order_1076_8` |
| E1286 | 8 | 67,522 | `Spectrum.not_order_1286_8` |
| E467 | 10 | 1,392,948 | `Spectrum.not_order_467_10` |
| E704 | 10 | 26,549 | `Spectrum.not_order_704_10` |
| E1076 | 10 | 973,808 | `Spectrum.not_order_1076_10` |
| E1110 | 10 | 4,290,272 | `Spectrum.not_order_1110_10` |
| E1279 | 10 | 274,422 | `Spectrum.not_order_1279_10` |
| E1286 | 10 | 7,769,541 | `Spectrum.not_order_1286_10` |
| E1313 | 10 | 6,429,116 | `Spectrum.not_order_1313_10` |
| E1516 | 10 | 129,696 | `Spectrum.not_order_1516_10` |

The eleven compressed certificates total **22,857,507 bytes**
(about 21.8 MiB). Individual certificate modules compiled in roughly 3–7.5 seconds
in the observed build. These are local timings, not performance guarantees.

[Certificate metadata](../data/spectrum/small_orders_20261007.json) records exact
CNF and proof hashes. [Research probes](../data/spectrum/small_orders_searches_20261007.json)
record 24 bounded searches and distinguish complete refutations from timeouts.
[The pass report](../data/spectrum/small_orders_pass_20261007.json) lists the
22 catalogue changes and the final order-eight/ten status of all representatives.

## Validation

The full spectrum build passed (4,213 jobs). The catalogue check verified
all 4,694 laws, including declaration types and transitive proof dependencies.
All 19 presentation tests and the source-generator consistency check passed.
The ten relation boards were rebuilt and their closure checked against the
full-matrix reference; their counts and open rows are unchanged.

## Reproduction

```sh
python3 scripts/spectrum_small_orders.py                   # verify saved hashes
python3 scripts/spectrum_small_orders.py --solve           # regenerate all certificates
python3 scripts/spectrum_small_orders.py --solve --only 1516
lake build equational_theories.Spectrum
python3 scripts/spectrum_generate.py --check
lake env lean scripts/check_spectrum.lean
python3 scripts/test_spectrum_overview.py
```

The catalogue generator integrates all eleven exclusions, strengthens the
upper bounds, transfers them to dual laws, and provides the Lean theorem names.
Presentation summaries list the new exclusions. A deployment-bundle refresh
is a separate step after committing the proof sources.
