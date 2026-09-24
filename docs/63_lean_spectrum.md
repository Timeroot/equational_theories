# Lean bounds for the spectrum of E63

The new formalization proves that every positive order except

```
2, 6, 10, 14, 18, 26, 30, 38, 42, 90, 158
```

has an E63 model. In particular **every order at least 159** has a model.
The positive theorem and its cofinite corollary contain no `sorry`, external
computation axioms, or assumed design-existence theorems.

Orders 2 and 6 are excluded by complete Lean proofs.
`Spectrum.E63.not_two` checks all sixteen binary tables directly in the kernel;
`Spectrum.not_order_63_6` reuses the existing checked finite refutation. Exclusions at 10 and 14
are explicitly admitted in `Generated/NoteObligations.lean`, as requested;
externally checked finite refutations do not count as Lean proofs.
Neither admission is used by any positive construction.

There is one discrepancy with the requested exception list: **90 must still
be retained in the fully proved bound**. Bennett (1989), Lemma 5.46, claims
existence at 90 using a 16-element model containing a 5-element submodel.
The saved singular-product 16-model has no such submodel; that missing
ingredient has not been reconstructed. This is a gap in our reconstruction,
not a proof that order 90 is impossible. The six mathematically unsettled
orders remain 18, 26, 30, 38, 42, and 158. No negative conclusion is drawn
from a failed construction or search. A targeted 30-minute search for the
partial 16-element model with a 5-element hole was unresolved; the command,
solver version, and input hash are recorded in
`data/spectrum/63_order90_reconstruction.json`.

## Proof organization

The entry point is `equational_theories/Spectrum/Equation63.lean`:

- `Spectrum.E63.lower`: the positive bound above.
- `Spectrum.E63.all_large`: existence at every order at least 159.
- `Spectrum.E63.cofinite`: a complete replacement for the old Wilson-theorem
  admission `Spectrum.Pending.cofinite_63`.
- `Spectrum.E63.proved_upper`: the fully proved exclusions at 2 and 6.

Files under `Spectrum/Equation63/` contain the reusable argument:

1. `Gluing.lean` proves group-divisible-design gluing. Group models need not
   be idempotent. The transversal blocks are idempotent; injectivity of left
   translations shows that evaluating E63 at distinct block points never
   invokes a diagonal multiplication.
2. `Transversal.lean` restricts a transversal design to seven complete groups
   and an arbitrary subset of an eighth group. Block sizes are 7 and 8.
3. `CyclicDesign.lean` constructs TD(8,q) over `ZMod q` for q coprime to 60
   (equivalently 30), using slopes 0 through 6 and one vertical coordinate.
   Differences between slopes are units. This avoids a general finite-field
   existence theorem in the infinite induction.
4. `DifferenceMatrix.lean` and `Designs/` develop four kernel-checked small
   difference matrices, of orders 9, 25, 27, and 36. The first three come
   from small finite fields; the last uses the saved design certificate.
5. `Singular.lean` proves the one-point singular product, with order
   k*m+1 from an idempotent k-model, a pointed (m+1)-model, and an m-model.
6. `Seeds.lean` proves the affine formula `x ◇ y = -b^3*x + b*y` whenever
   `b^5+b^4+1=0`, and idempotence when `b^3-b+1=0`. It derives the small
   singular-product witnesses. `Construction.lean` applies the small designs.
7. `FiniteBasis.lean` certifies every required order below 1608 by those
   proved rules; the completeness of its finite list is also kernel checked.
8. `Induction.lean` handles the tail. Given n >= 1608, put a=ceil(n/8) and
   choose q among a,...,a+5 coprime to 60. Set r=n-7q. Lean verifies
   159 <= r <= q < n and r < n. Strong induction supplies the two fillings;
   the TD(8,q) construction supplies order n.

## Finite witnesses retained

All twelve additional positive orders are proved:
**22, 29, 34, 46, 47, 58, 62, 74, 106, 110, 114, 118**.

Only **46, 47, 62, 74, 114, and 118** need new multiplication tables in this
formalization. Each is reconstructed by `scripts/spectrum_63_bennett.py`, packed
row-major into fixed-width fields of a natural-number literal, and checked
in Lean using `decide +kernel`. Modulo the order makes the decoded operation
total; the kernel independently verifies every E63 instance. The Python
packing code and Bennett reconstruction are not trusted proof oracles.

The other witnesses are products or singular products. In particular the old
9- and 12-element tables have been removed from both `witnesses.json` and the
generated Lean files: 9=3*3 and 12=4*3. The order-13 witness was already a
compact modular construction, not a stored multiplication table.

The existing small tables at 4 and 8 are reused. Finite design matrices are
small auxiliary combinatorial certificates, not large magma tables.

## Reproduction

Run from the repository root:

```sh
python3 scripts/spectrum_63_lean_designs.py
python3 scripts/spectrum_63_lean_witnesses.py
python3 scripts/spectrum_63_lean_bounds.py
python3 scripts/spectrum_generate.py --write
lake build equational_theories.Spectrum
lake env lean scripts/check_spectrum.lean
```

The catalogue transfers the bounds and complete cofiniteness result to the
laws with the same proved spectrum. Its upper bound includes the explicitly
admitted exclusions at 10 and 14 and is therefore marked `PROOF_AVAILABLE`;
the lower bound and cofiniteness are marked `PROVED`.

After committing the proof changes, `python3 scripts/build_website_data.py`
regenerates the commit-pinned website bundle. The generated website data is
committed separately.
