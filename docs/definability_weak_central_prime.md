# E1486 → E1485: a prime-order obstruction

17 September 2026. **E1486 → E1485 is refuted even for finite first-order
definability**, hence in all eight variants. The source has an eleven-element
model; the target has no model of any odd prime order.

This removes the rectangle `{1486,2126} → {1485,2162}` from the completely-open
table: **40 → 36 raw pairs**, **11 → 10 class rows**. No positive classes merge.
The exact E1485 spectrum remains open; this proof does not establish the
square-or-twice-square conjecture.

## The general theorem

[WeakCentralCardinality.lean](../equational_theories/Spectrum/WeakCentralCardinality.lean)
proves `WeakCentralGroupoid.prime_card_eq_two` and its spectrum formulation
`Spectrum.prime_order_1485`. Write the identity as

\[
  (y*x)*(x*(z*y))=x.
\]

The existing `dual_eqn` theorem supplies its left/right dual. The proof follows
the sharp-edge idea from [the graph research](1485_graph_research.md#sharp-edges-give-exact-rectangular-factorizations),
then uses a direct prime-rank argument that avoids Boolean-algebra classification.

1. Call an edge `e ⇒ a` sharp when `e*(a*b)=a` for every `b`. The identity
   implies its dual characterization `(b*e)*a=e`.
2. For fixed `a`, the transformations `P_b(t)=a*(t*b)` are idempotent, and
   each preserves the fixed points of every other one. Finite induction
   produces a common fixed point, giving a sharp successor. Applying this
   argument to the opposite operation gives a sharp predecessor.
3. A sharp edge `e ⇒ a` gives the bijection
   `G ≃ Row(a) × Col(e)`, where `Row(a)={a*x}` and `Col(e)={x*e}`.
   The forward map is `x ↦ (a*x,x*e)` and the inverse is `(u,v) ↦ u*v`.
   Both inverse identities are algebraic and work on arbitrary carriers.
   In particular every finite row rank divides `|G|`.
4. At prime order every row is constant or bijective. A bijective row
   supplies a constant column, and a constant column gives a constant row.
   Thus a constant row exists.
5. Fix a constant row `0*x=1`. The identities imply `x*0=1`, that every
   constant row is indexed by `0`, and that every bijective row is indexed
   by `1`. Every element is therefore `0` or `1`. Prime cardinality is at
   least two, so it equals two.

The intermediate lemmas `constant_column_of_bijective`, `constant_row_unique`,
and `bijective_row_unique` are algebraic and do not require finiteness.
The finite hypothesis is used to obtain sharp neighbors and to turn full row
rank into bijectivity.

## Definability and catalogue integration

[CentralSpectrum.lean](../equational_theories/Definability/CentralSpectrum.lean)
combines `Spectrum.not_order_1485_11` with the existing
`Spectrum.NoteWitness.model_1486_11`. Finite first-order definability would
transport that witness to an E1485 operation on the same eleven-element carrier,
contradicting the prime-order theorem.

The exclusions at both 11 and 13 now have completed proofs. The historical
`Spectrum.Pending` names remain as compatibility aliases with `complete`
status assertions. The generated catalogue uses the completed theorems directly.
The earlier reported exhaustive searches are no longer proof dependencies.

## Reproduction and trust

```sh
lake build equational_theories.Definability equational_theories.Spectrum
lake env lean scripts/check_spectrum.lean
lake env lean scripts/test_spectrum_status.lean
python3 scripts/spectrum_generate.py --check
OPENBLAS_NUM_THREADS=2 python3 -m unittest discover -s scripts -p 'test_definab*.py'
python3 scripts/definability_imports.py --check
OPENBLAS_NUM_THREADS=2 python3 scripts/definability_audit.py --write --date 2026-09-17 --verify-closure
OPENBLAS_NUM_THREADS=2 python3 scripts/spectrum_definability_check.py
```

Axiom guards for the general theorem, spectrum theorem, both exclusions, and
definability consequence list only `propext`, `Classical.choice`, and `Quot.sound`.
The eleven-element table is checked by kernel `decide`. No SAT certificate,
native computation axiom, or pending spectrum obligation is used by this result.

The combined build passed **16,862 jobs**. The full-matrix reference comparison
and regeneration of all 14 audit artifacts passed in **190.61 seconds**; all
**21 Python regression tests** passed. The import audit retains **13,349** local
modules reachable from **6,582** direct entry imports. Spectrum generation also
passes `--check`.

The catalogue type/axiom audit and proof-status regression checks passed. The
independent spectrum scan covers 22 exported orders and finds **5,172,297**
distinct obstructions, all already refuted in all eight boards, with no further
missing D/fin negatives. Its source fingerprint matches the board snapshot.
