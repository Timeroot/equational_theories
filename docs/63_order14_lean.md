# A compact order-fourteen exclusion for E63

`Spectrum.not_order_63_14` is proved without `sorry` in
[`OrderFourteen/Exclusion.lean`](../equational_theories/Spectrum/Equation63/OrderFourteen/Exclusion.lean).
The certificates total **1,580,396 bytes (1.51 MiB)**. Checking all certificates
with the normal Lean build took **45.06 seconds**, with the mathematical modules
cached, and peaked at **2.20 GiB RAM**. The old 52 MiB DRAT archive is historical
external evidence; the new Lean proof does not read it.

## Mathematical reduction

Left division transforms a finite E63 magma into a Latin operation satisfying
`(x * (x * y)) * x = y`. Thus `Rₓ = Lₓ⁻²`; the cycle of `x` under `Lₓ` has length
one or three, and no `Lₓ` has a two-cycle. These are the existing general lemmas
from the order-ten proof, reused unchanged.

There is a short useful fixed-point argument. For each column `y`, let
`owner(y)` be the unique row `x` with `x*y=y`; in this cubic presentation,
`owner(y)=y*(y*y)`. If every row has a fixed point, `owner` is surjective and hence
bijective. Consequently **every row has exactly one fixed point**. Otherwise
choose a row without fixed points as row zero. In the first case choose zero
non-idempotent if possible; if that is impossible the whole operation is
idempotent. This normalization, for arbitrary finite sizes, is proved in
[`Normalization.lean`](../equational_theories/Spectrum/Equation63/OrderFourteen/Normalization.lean).
It needs neither a cardinality network nor a permutation enumeration.

Label the cycles of row zero consecutively, giving `0*y ≤ y+1`. Row zero has at
most one singleton cycle, and its distinguished cycle has length one or three.
There are 70 ordered cycle decompositions consistent with these conditions.
They comprise **21 cycle types**: changing the order of the other cycles just
relabels the magma. Explicit permutations fix zero and conjugate each of the
70 rows to its representative. Their inverse and conjugacy equations are
checked by kernel reduction in
[`CanonicalData.lean`](../equational_theories/Spectrum/Equation63/OrderFourteen/CanonicalData.lean).
The ordinary isomorphism argument transferring the exclusions is in
[`RowTransfer.lean`](../equational_theories/Spectrum/Equation63/OrderFourteen/RowTransfer.lean).

## Certificate construction and checking

The formula has 2,744 table-entry variables and 192,416 clauses. Its soundness is
proved in [`Encoding.lean`](../equational_theories/Spectrum/Equation63/OrderFourteen/Encoding.lean).
The independent Python generator produces exactly the same clauses, in the
same order, as Lean. Besides the Latin and cubic constraints, it includes only
proved translation and normalization consequences.

CaDiCaL refuted all 70 fixed-row cases in 70.568 cumulative solver-seconds; the
slowest took 5.509 seconds. For each cycle type we retain the smallest proof.
The 21 chosen proofs have 114,162 RUP additions. A separate **208-addition**
refutation checks that excluding all 70 ordered rows contradicts the normalized
formula. Thus even completeness of the external case enumeration is checked;
it is not an assumption of the Lean proof.

Each branch retains its fourteen row-entry assumptions as permanent root units.
This lets the replay engine cache their propagation instead of repeating it at
every step. Unused clauses are removed, and used clauses are deleted after
their last use. The compact data omit propagation hints and record a mask of
relevant input clauses. Lean reconstructs those hints using the compiled
certificate library, then checks the resulting LRAT proof using
`Std.Tactic.BVDecide.LRAT.check_sound`. The checks are registered with
`@[spectrum_native]`, matching the repository's finite-refutation trust policy.
The solver, proof trimming, masks, compression, and hint reconstruction are all
untrusted data suppliers.

## Reproduction

Audit hashes, the generated relabeling data and wrapper, and the independent CNF:

```sh
python3 scripts/spectrum_63_fourteen_certificate.py
```

Regenerate the searches and packed data:

```sh
python3 scripts/spectrum_63_fourteen_certificate.py --solve
```

Each case has a 180-second limit and a 512 MB raw trace cap; at most three solver
jobs run concurrently by default. A timeout is an error, never an exclusion.
The small row-coverage solver has a separate 120-second limit. Only the selected
21 cases and coverage certificate are retained in the repository.

Check the theorem through the normal build, which loads the compiled replay
library:

```sh
lake build equational_theories.Spectrum.Equation63.OrderFourteen.Exclusion
```

The certificate-only benchmark above includes input generation, reconstruction,
and the final verified checks. The finite relabeling checks separately took
approximately 13–20 seconds. Timings depend on the machine and concurrent work;
ordinary builds reuse these modules unless their inputs change.
