# Spectrum data: input versus output

These files have different roles. None is a proof oracle.

| File | Role | How it is checked |
| --- | --- | --- |
| `witnesses.json` | Checked-in **input**: candidate multiplication tables, keyed by `equation:order` | The generator emits Lean witnesses; Lean verifies each selected table satisfies the equation |
| `bv_cases.json` | Checked-in **input**: squaring representatives and small SAT-core selections | `scripts/spectrum_bv.py` emits `bv_decide` proofs plus Lean proofs that every selected premise follows from the magma law |
| `catalogue.json` | Generated **output**: one record for each of E1–E4694 | `scripts/check_spectrum.lean` checks theorem types and transitive evidence statuses against the Lean environment |

A witness is a row-major array of `n*n` integers in `[0,n)`, with entry `n*x+y`
representing `x*y`. Candidates may come from finite-field linear search,
repository examples, or Z3. Search failure never proves nonexistence.

The catalogue lists exact formulas where the note states one, or lower/upper
bounds where the exact answer is unknown. `mathematical_status = EXACT` means
the note **states an exact formula**, not that we have completed its proof.
Check `exact_proof_status`, or the corresponding bound/cofinite proof status:

- `PROVED`: completed Lean proof (explicitly allowed native checks may occur).
- `PROOF_AVAILABLE`: argument/citation/reported ATP result awaiting formalization or integration;
  a local ATP certificate is not necessarily available.
- `NOTE_GAP`: an essential step in the note has not been reconstructed.
- `UNKNOWN`: exact spectrum left mathematically open in the note; no exact theorem.

`cofinite_status = DISPUTED` records the conflicting E1313 claims. Conjectures are
separate fields, not asserted exact theorems. `explicit_orders` is a selected
witness list, not the multiplicative closure or an exhaustive list of known orders.

The previous `spectrum_finite_obligations.json` was a redundant list of names and
has been removed. The authoritative obligations are now annotated beside their
declarations in `Spectrum/NotePending.lean` and `Generated/NoteObligations.lean`.
Use `#spectrum_status Spectrum.Catalogue.exact_546` to see the actual dependencies,
source sections, and missing steps. `Catalogue.lean` explains all proof layers.

Regenerate and verify from the repository root:

```sh
python3 scripts/spectrum_generate.py --write
lake build equational_theories.Spectrum
lake env lean scripts/check_spectrum.lean
python3 scripts/spectrum_generate.py --check
```

`scripts/spectrum_note.py` transcribes the PDF formulas/bounds;
`scripts/spectrum_catalogue.py` emits their Lean statements and JSON index.
Optional `python3 scripts/spectrum_witnesses.py --write` updates candidate input
and requires `z3-solver`; ordinary regeneration does not need Z3.

The integrated symmetry-broken BV proofs are included in normal regeneration
and the default Spectrum build; they also have focused generator/build targets:
see [spectrum_bv.md](../../docs/spectrum_bv.md). Their core cache contains no
multiplication tables or trusted UNSAT answers. `e_...` selects an equation
instance, `i_row_col_col` a row-injectivity consequence, `u_x` the proved E474
unary consequence, and `b_row_col` an output bound. Ordinary regeneration reads
this cache without invoking Z3; `--search` selects new cores. A wrong core fails
Lean's `bv_decide` check or its proof that the premises follow from the law.
