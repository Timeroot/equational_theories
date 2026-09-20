# Counting obstructions for partially resolved cells

The 18 September 2026 pass extends counting beyond the completely-open
inventory. It adds finite term-structural negatives, which also refute
term-structural definability over arbitrary carriers. It does not establish
negatives for one-way term definability or first-order definability.

The scan of all 4,689 previously open TS/fin class pairs found 174 linear-count
certificates over the rings `ZMod n`, for `2 ≤ n ≤ 200`. Positive closure reduces
these to 137 generating declarations. Counting every labeled three-element
operation supplies 17 further declarations. All are imported through
[PartialCountingCatalogue.lean](../equational_theories/Definability/PartialCountingCatalogue.lean).
The completely-open inventory remains **32 raw pairs / 9 class rows**.

## Verified board impact

| Board | Newly refuted raw pairs | Newly refuted class pairs | Remaining raw open | Remaining class open |
|---|---:|---:|---:|---:|
| TS/fin | 978 | 191 | 22,473 | 4,498 |
| TS/all | 902 | 192 | 24,589 | 5,010 |

The two class counts differ because each board has its own equivalence classes.
No positive classes merged, and the other eight boards are unchanged. The full
Definability build passed (16,661 incremental jobs), all 22 regression tests
passed, and all ten optimized closure computations matched the full-matrix
reference. The audit regenerated all 14 artifacts in 155.02 seconds.
The independent spectrum recheck found the same 5,172,297 already-covered
obstructions and no missing D/fin negative, with the same source fingerprint.

## Why counting works

Fix a finite nonempty carrier A and a finite family of distinct source
operations on A. Take their direct product, with one coordinate per source
operation. A term-defined target operation acts coordinatewise, and each
coordinate satisfies the target law. If two coordinates acquire the same target
operation, every recovery term preserves equality between those coordinates.
Applying that term to constant tuples shows that the original source operations
were equal. Thus the source operations inject into the possible target
operations. More sources than targets is a contradiction.

This argument permits the forward and recovery terms to depend on the entire
product magma, as the definitions require. It assumes no uniform term across
separate source magmas. The product can be enormous; its elements and clone
are never enumerated.

[ModelCounting.lean](../equational_theories/Definability/ModelCounting.lean)
formalizes the argument for arbitrary finite operation families. Its main
inequality is `table_count_le_of_termStructuralFromFin`. The existing
[LinearCounting.lean](../equational_theories/Definability/LinearCounting.lean)
uses the additional invariant that terms in coordinatewise linear operations
remain coordinatewise linear. Only target coefficient pairs need to be counted
in that case. Composite moduli are valid: the argument needs a commutative ring,
not a field.

For **E167 → E1482**, three E167 source operations on `ZMod 5` have coefficient
pairs `(1,3)`, `(2,4)`, and `(3,1)`. Only two target coefficient pairs pass the
necessary E1482 basis tests. Their product, of order 125, therefore has no
term-defined E1482 companion admitting term recovery. This certificate uses
only the standard Lean axioms.

For **E621 → E48**, there are **33** labeled source tables on `Fin 3` but
only **27** labeled target tables. Taking all source tables gives a finite
counterexample by the general theorem. These are counts of operations on a
fixed labeled carrier, not counts up to isomorphism. The computation checks all
`3^9 = 19,683` tables and every variable assignment.

## Certificates and trust

The saved [linear data](../data/definability_partial_linear_counts.json) records
every coefficient count and the selected factors. The saved
[table data](../data/definability_table_counts.json) records all 17 table-count
inequalities. Python independently recomputes these data and reproduces the
Lean source; only the compiled Lean declarations supply board facts.

The two general counting theorems have standard-axiom guards. All linear source
identities are proved algebraically, using ring normalization and reduction in
the finite characteristic. Of the 137 linear target counts, 65 use kernel
`decide` and 72 use `native_decide`. Each of the latter explicitly guards its
single native-computation axiom. The 17 full-table inequalities each use and
guard one native-computation axiom. No solver unsatisfiability result is used.

Checking every source assignment directly was needlessly expensive at large
moduli; the algebraic proofs avoid that cost and reduce the native trust surface
to the target counts. The finite table counts still enumerate assignments,
since those operations need not be linear.

## Reproduction

```sh
python3 scripts/definability_partial_counts_check.py
OPENBLAS_NUM_THREADS=2 python3 scripts/definability_table_counts_check.py
lake build equational_theories.Definability
python3 scripts/definability_imports.py --check
OPENBLAS_NUM_THREADS=2 python3 -m unittest discover -s scripts -p 'test_definab*.py'
OPENBLAS_NUM_THREADS=2 python3 scripts/definability_audit.py --write --date 2026-09-18 --verify-closure
```

Use `--write` with either certificate checker to reproduce its generated Lean
files. To search the current remaining TS/fin inventory, use
`python3 scripts/definability_linear_counts.py --all-open --max-modulus 200`.
That search will omit cells already closed by the saved certificates; use
`--pair SOURCE TARGET` to rediscover a particular settled pair.

## Follow-up affine and symmetry pass

The subsequent [finite-family counting pass](definability_affine_counting.md)
certifies all 62 affine candidates originally saved by this pass, then extends
the search to scalar, matrix, translation, and unary-symmetry families. Those
new results are reported separately from this page's historical totals.
The general affine lemma is now in
[AffineCounting.lean](../equational_theories/Definability/AffineCounting.lean).
