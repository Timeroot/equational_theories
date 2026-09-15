# Integrated symmetry-broken bit-vector exclusions

There are complete Lean proofs of both:

```lean
import equational_theories.Spectrum.Generated.BV474_4
import equational_theories.Spectrum.Generated.BV1286_5

#check Spectrum.BitExclusion.not_order_474_4
#check Spectrum.BitExclusion.not_order_1286_5
```

Both are imported by the default Spectrum catalogue, through
`Generated.SmallExclusions`, with public names `Spectrum.not_order_474_4` and
`Spectrum.not_order_1286_5`. The former replaces the old case tree; the latter
discharges the pending size-five exclusion and propagates through the existing
negative-transfer routes. There is no remaining `Pending.not_order_1286_5`.

Every SAT call completed with `timeout := 1`, but that does not bound
preprocessing, proof elaboration, or the sum of all cases. The original
one-second end-to-end goal has not been met. Successful proofs are retained
with this overhead by agreement; total compilation timings are reported below.

## Reduction and trust

1. The squaring map `s(x) = x*x` is a finite endofunction. Its functional graph
   consists of cycles with incoming trees, not necessarily a DAG. There are 19
   isomorphism types on four elements and 47 on five.
2. `Generated.Squaring` lists those representatives and provides a relabeling
   for each of the 256 or 3125 squaring maps. A `native_decide` certificate checks
   every conjugation. `Symmetry.canonical_model` proves that transporting a
   magma along the relabeling preserves its equation and gives that diagonal.
   The Python enumeration is not trusted to be complete.
3. For both E474 and E1286, every left translation is surjective by inspection
   of the law, hence injective on a finite carrier. `SmallOrderLemmas` proves this.
   For E474, the existing proved implication to E8 additionally gives
   `x*(x*x) = x`. On four elements these two facts allow only 12 possibilities
   per row, though the current BV encoding uses row bit-vectors rather than
   enumeration of those 12 possibilities.
4. `BitTables` packs rows into 8-bit or 15-bit words and supplies the prescribed
   diagonal separately, exposing its constants before bit-blasting. It proves
   the encoding correct for **every** original magma. At size five, unused input
   codes 5–7 are mapped to 4; the bridge proves that actual magma evaluations
   remain inside the original five-element carrier.
5. Z3 selects small contradictory subsets of equation instances and the proved
   auxiliary facts. These selections are cached in `data/spectrum/bv_cases.json`.
   Each subset is independently re-proved by `bv_decide`, and Lean proves that
   each premise follows from the actual law. A Z3 answer itself is never used
   as a proof or axiom. Cases are then assembled using the complete diagonal list.

Every refutation and the two assembled exclusions have `spectrum_assert ... complete`.
Native axioms are explicitly tagged, including the finite encoding and symmetry
checks. There are no `sorry`s in this development. `BVAudit.lean` additionally
guards representative axiom lists and the final dependency summaries, and is
imported by the default `AxiomAudit`.

We do not currently impose lexicographic minimality on the entire Cayley table.
The remaining permutations stabilizing a normalized diagonal provide another
possible reduction, as do stronger law-specific consequences.

## Timings and reproduction

Observed local compilation times with dependencies already built:

| Module | Cases | Compilation |
| --- | ---: | ---: |
| `Generated.Squaring` | All maps at orders 4 and 5 | about 29 s, shared infrastructure |
| `BitTables` | Both encoding proofs | about 5 s, shared infrastructure |
| `Symmetry` | General relabeling theorem | about 5 s, shared infrastructure |
| `SmallOrderLemmas` | Left cancellation and E474's unary consequence | about 4–5 s, shared infrastructure |
| `Generated.BV474_4` | 19 diagonal types | about 18 s |
| `Generated.BV1286_5` | 47 diagonal types | about 246 s |
| `BVAudit` | Axiom lists and dependency summaries | about 11–12 s |

The old E474 size-four case tree took about 144 seconds in the previous rebuild.
These are observed compilation times, not timing guarantees; the two BV modules
were built concurrently. A subsequent combined rebuild with the default catalogue
took 26 s and 276 s for the size-four and size-five modules, respectively, and
passed both the BV axiom guards and the catalogue-wide audit.
Early individual probes had approximately 0.1–0.7 s
in the solver/checking tactic but 1–5 s or more in total elaboration. Normalization
and checking the large proof expressions, not just SAT search, now dominate.

The integration rebuild of `equational_theories.Spectrum` took 214.57 s wall
time. That run reused the already compiled BV proof modules and rebuilt their
catalogue dependents and audits; it is **not** a cold-build timing. The table
above reports the proof-module compilation costs separately.

```sh
python3 scripts/spectrum_generate.py --write
lake build equational_theories.Spectrum
python3 scripts/spectrum_generate.py --check
```

The main generator now includes the BV certificates. To regenerate/check only
those certificates, use `scripts/spectrum_bv.py --write` / `--check`; to build
only their proofs and axiom audit, use `lake build equational_theories.Spectrum.BVAudit`.
Ordinary regeneration needs only Python's standard library. To choose new cores
with Z3 and regenerate the proofs, use `python3 scripts/spectrum_bv.py --search`
(requires `z3-solver`). This does not automatically discharge anything: rerun the
Lean build. For detailed profiling, run `lake env lean -Dprofiler=true` on either
generated BV module.
