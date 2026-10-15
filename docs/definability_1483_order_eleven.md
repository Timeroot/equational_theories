# E1483 has no eleven-element model

**Status: proved in Lean, with all certificate inputs distributed.**
`Magma.Central1483.no_operation_eleven` and `Spectrum.not_order_1483_11`
contain no `sorry`. Sixteen compact RUP certificates occupy **10,871,684 bytes
(10.37 MiB)**, replacing the old, undistributed **769,167,024-byte (734 MiB)**
LRAT bundle: about **71 times smaller**. The public proofs check all sixteen
cases and register their native checks with the spectrum proof-status system.

The existing eleven-element E1486 model now gives a checked finite first-order
negative **E1486 → E1483**. The exclusion concerns every operation on an
eleven-element carrier; it does not assume a particular interpretation term,
symmetry, or recovery map. Duality gives the corresponding four raw pairs
`{1486,2126} → {1483,2163}`. This does not decide E1483 versus E1485: both exclude
order eleven, and their possible cospectrality remains open.

## Mathematical reduction

Write `f` for the hypothetical operation and `r(a)` for the size of row `a`.
The law is

```
f(f(y,x), f(x,f(y,z))) = x.
```

The [translation identities](../equational_theories/Definability/Central1483Translations.lean)
and [constant-row argument](../equational_theories/Definability/Central1483Constant.lean)
show that no row is constant or bijective at odd order eleven. Left and right
translation at each element have equally sized images. Whenever `b` belongs
to row `a` or column `a`, the law gives `11 ≤ r(a) r(b)`.

The [graph lemmas](../equational_theories/Spectrum/Equation1483/Graph.lean)
make this structure more explicit. Put an edge `a → b` when `b` occurs in row
`a`. This is equivalent to `a` occurring in column `b`. Each product `a*b`
selects a path `a → a*b → b`. Every edge `a → b` completes a directed triangle
through `b*a`, with `(b*a)*b = a` and `a*(b*a) = b`. Along such an edge,
`(a*x)*(x*b) = x` for every `x`. These statements hold for arbitrary cardinality.
They supply short extra clauses which expose consequences of E1483 directly to
the solver.

Choose a minimum-rank row and name its element `0`. Its image `I` is relabeled
as `{1,…,k}` if it omits zero, or `{0,…,k−1}` otherwise. The diagonal output is
`1`, or `0/1` in the second case. Here `2 ≤ k ≤ 10`. If zero belongs to `I`, the
edge rank bound gives `11 ≤ k²`, ruling out that case at ranks two and three.
This leaves sixteen cases.

The new [normalization](../equational_theories/Spectrum/Equation1483/OrderEleven/Normalization.lean)
then fixes the labels in `I` and sorts the other points using **both** translation
images. Write `J` for the image of column zero. Translation regularity makes
`x ↦ 0*x` on `J` and `y ↦ y*0` on `I` inverse bijections. Consequently:

1. Points of `J` outside the fixed labels can come first.
2. Their row-zero outputs can be sorted **strictly** increasingly.
3. The remaining points can be sorted by nondecreasing row-zero output.

Before this sorting, if `0*1` has a label greater than `2`, swap it with `2`
inside `I`. This fixes `0`, `1`, and the diagonal condition, and ensures
`0*1 ≤ 2`. The later sorting fixes this condition. Lean proves that every
hypothetical model admits all these normalizations; no search branch is discarded
on an unproved symmetry assumption.

The [CNF proof](../equational_theories/Spectrum/Equation1483/OrderEleven/ImageEncoding.lean)
combines the old law, regularity, image, and rank clauses with the new graph and
sorting clauses. The independent Python generator and the actual Lean exporter
produce byte-identical formulas in all sixteen cases.

## Certificates and trust

CaDiCaL generates an LRAT refutation for each normalized formula. Lean's LRAT
trimmer removes unused additions and renumbers the surviving clauses. The
existing `scripts/spectrum_compact_rup.cpp` packer stores learned clauses and
deletions, with an input mask recording which original clauses were used.
Repeated nearby clauses share literals; xz compresses the resulting bytes.
The resulting proofs contain **666,646 learned clauses**, down from 4,646,678.
Solver logs, untrimmed proofs, and the old large bundle are not shipped.

The pure Lean function `Spectrum.CertificateData.CompactRup.reconstruct`
recovers verification hints. It is **untrusted reconstruction**: its output must
pass the standard, proved `LRAT.check`, and only `LRAT.check_sound` establishes
unsatisfiability. The input mask merely restricts the reconstruction search;
the verified checker receives the complete Lean-defined CNF. The external
solver, packer, decompressor, hashes, and independent generator supply data,
not assumptions in the proof.

The mathematical reductions use the ordinary Lean axioms. Certificate checking
adds sixteen explicitly registered `native_decide` axioms, consistent with the
repository's other computational exclusions. There is no `sorryAx` dependency.
The [manifest](../data/spectrum/1483_order11.json) records formula and payload
hashes, sizes, selected input counts, and validation results. The old
`data/definability_1483_order_eleven.json` is retained as historical provenance,
with its separate optional checker; its large certificates are unnecessary.

## Rechecking

```sh
python3 scripts/spectrum_1483_eleven.py
lake build equational_theories.Definability.CentralSpectrum
```

To independently compare every actual Lean formula with the Python generator:

```sh
lake env lean --run equational_theories/Spectrum/Equation1483/OrderEleven/Export.lean .cache/1483-eleven-cnf
python3 scripts/spectrum_1483_eleven.py --check-lean-cnf .cache/1483-eleven-cnf
```

On 2026-10-11, the first build of all sixteen certificate modules and their
combined proof took **219.52 seconds** with the mathematical dependencies
already built. The two largest cases took **165 and 210 seconds**; the others
ranged from about 8 to 46 seconds, including module elaboration. The maximum
reported resident size of a process was about **4 GiB** (not the aggregate
memory of the parallel build). These are local measurements, not a full clean
project-build benchmark.

Use normal `lake build` for timing certificate checks: it loads the compiled
replay library. A bare scratch `lake env lean` invocation without Lake's plugin
configuration interprets the replay code and can be much slower.

To regenerate certificates, export CNFs with `--export-cnf`, run
`cadical --lrat INPUT.cnf OUTPUT.lrat`, trim with Lean's `trim` and
`dumpLRATProof ... true`, then feed the trimmed binary proof to
`spectrum_compact_rup --input-mask OUTPUT.rup` and compress with `xz -6`.
Changed data require updated manifest hashes and regenerated wrappers
(`--write`) before rerunning all Lean checks.
