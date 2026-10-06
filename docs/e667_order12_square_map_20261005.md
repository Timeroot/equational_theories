# E667 at order twelve: square-map reduction

**E667 has no model of order twelve, proved in Lean.** The unrestricted theorem
is `Spectrum.not_order_667_12` in `Equation667Twelve/Exclusion.lean`.
All normalization arguments, all 129 new certificate replays, and the final
completeness audit have passed. The spectrum catalogue now excludes 3, 6,
and 12, leaving 15 unresolved orders:

```
15, 24, 30, 39, 48, 51, 60, 75, 87, 96, 102, 159, 174, 195, 219.
```

Since E481 has an order-twelve model, the result also proves
`Spectrum.spectrum_667_ne_481` and
`Spectrum.not_definableFin_481_667`. No part of this exclusion uses an admitted
theorem. The finite computations use the repository's explicit
`spectrum_native` policy and Lean's verified LRAT checker.

## Exhaustive mathematical split

Write `D(x) = x*x`. A noninjective `D` has one of these three patterns:

1. `D(e)=e=D(x)` with `x != e`.
2. Three distinct points with `D(a)=D(b)=c` and `D(c)=a`.
3. Four distinct points with `D(a)=D(b)=c` and `D(c)=d`.

To see this, take a collision `D(a)=D(b)=c`. If `c` is either input, it is
idempotent. Otherwise inspect `D(c)`: it equals `c`, one of the two inputs,
or a fourth point. This split is proved without any algebraic assumption in
`Spectrum.E667.square_cases`.

If `D` is injective, it is a permutation. There are 77 integer partitions of
12, hence 77 possible permutation cycle types up to relabelling.

## Efficient bijective-square search

Prescribing `D` removes the auxiliary table from the SAT encoding. Its core
is the cubic identity `y*(x*(D(x)*y))=x`, together with Latin cancellation.
This needs 1,728 Boolean variables and about 97,000 clauses. All its algebraic
clauses have Lean soundness proofs in `Equation667FixedSquare/Encoding.lean`.

Seventy-three cycle types were refuted in the initial short pass. The other
four were involutions, with respectively six, four, two, or zero fixed points.
The six-fixed-point case was subsequently refuted without extra normalization.

The decisive improvement was to normalize using permutations that **commute
with `D`**. We may swap fixed points, flip a two-cycle, or exchange two
two-cycles. Choose a lexicographically least relabelled table. Whenever such
a swap fixes all preceding inputs and outputs, it cannot decrease the next
output. These conditional first-use inequalities preserve the prescribed
diagonal. Ordinary unrestricted row normalization would not do so.

The three remaining cases then took approximately 3.7, 0.4, and 8.4 seconds.
The general normalization theorem is proved in
`Spectrum.FiniteSearch.exists_centralizer_first_use`; its application to the
SAT clauses is proved in `Equation667FixedSquare/Normalization.lean`.
All 77 formulas have also been exported independently from Lean and matched
clause for clause against the Python inputs. Compact certificates total
6,244,112 gzip-compressed bytes; all 77 have now passed Lean replay. The complete theorem
`Spectrum.E667.FixedSquare.not_injective_square` excludes bijective squaring.

## Collision searches

The three- and four-point patterns were refuted with first-use normalization
fixing the named points. Both now have captured LRAT traces. The idempotent
collision was refuted in approximately 1,008 seconds using the left-division
encoding, but that original run did not capture a trace. All 50 relevant
first-row cycle types now also have captured LRAT traces, providing a
replacement certificate route for this branch. The normalization proofs
are complete in `Equation667Twelve/Collisions.lean` and
`Equation667Twelve/IdempotentCollision.lean`. Both the three-point and
four-point certificates and all 50 row checks have passed Lean replay.

For the idempotent collision, label the idempotent point zero. Its left
translation `L₀` fixes zero, and the square-fibre identity forces
`L₀²(x)=x` for another point. Consequently its cycle partition starts with
a singleton and has either another singleton or a two-cycle. Exactly 50 of
the 77 partitions qualify. Conjugating `L₀` while fixing zero puts its row
in one of these canonical forms; no additional symmetry assumption is made.

### Reusing exclusions and the remaining row symmetries (2026-10-06)

The five largest row refutations now use a further necessary condition:
**every repeated value of the square map is idempotent**. This is only being
asserted for a hypothetical order-twelve model, after the other two collision
patterns have been excluded. Indeed, if `D(a)=D(b)=c` with `a != b`, either
`c` is one of the inputs and is already idempotent, or the four-point exclusion
forces `D(c)` to be `a`, `b`, or `c`. The first two alternatives contradict
the three-point exclusion (interchanging `a,b` if necessary). This argument is
proved as `Spectrum.E667.Twelve.collision_target_idempotent` in
`CollisionConsequences.lean`. Its hypotheses are just the three- and four-point
refutations; it does not use the final exclusion or any row certificate.

For rows 37 and 39, we also minimize the single entry `f(1,2)` among
relabellings fixing zero and commuting with the prescribed first row. A finite
orbit has a minimum. Importantly, the relabellings may move input 2: the
inequality compares `f(1,2)` with `s(f(s⁻¹(1),s⁻¹(2)))`, not just with a
relabelled output at the original inputs. `RowReduction.exists_minimal`
formalizes the orbit argument, and `RowMoves.moves_valid` checks that each
listed permutation really preserves the row. Completeness of the list of
permutations is unnecessary for soundness.

| First-row cycles | Old compressed bytes | New compressed bytes |
|---|---:|---:|
| 1,1,3,3,4 | 5,939,431 | 2,578,829 |
| 1,1,3,7 | 2,671,944 | 1,948,564 |
| 1,1,4,6 | 8,903,948 | 4,767,055 |
| 1,1,5,5 | 4,427,966 | 2,122,992 |
| 1,1,10 | 3,720,862 | 2,455,793 |

After the mathematical reductions, the 52 collision certificates occupied
**29,136,214 gzip-compressed bytes**,
down from 40,927,132 (28.8% less). Including the 77 bijective-square cases,
the total at that stage was **35,380,326 bytes**, down from 47,171,244 (25.0% less).
The four row batches are rebalanced after replacing the large certificates.

The new search generator is `scripts/spectrum_667_twelve_row_reduction.py`.
Its five DIMACS outputs exactly reproduce the solved inputs. All five
`RowReduction.natFormula` formulas were independently exported from Lean and
matched clause for clause. The collision certificate script's `--improve`
option checks those matches before replacing the stored certificates and
updating their hashes.

### Reconstruction cost

A native profile of the original four-point refutation separated about
85.3 seconds of RUP-to-LRAT reconstruction from 3.0 seconds in `LRAT.check`.
The reconstruction code now treats binary clauses as implication edges and
caches a blocking literal for each longer-clause watch. A true blocker avoids
loading and reordering the clause. With the same compact certificate and CNF,
reconstruction took about 71.0 seconds and checking 2.7 seconds. These numbers
exclude Lean elaboration and formula construction. They are native executable
measurements; an unconfigured `lake env lean --run` can interpret imported
code and should not be used as a substitute for a real `lake build` timing.

Reconstruction remains untrusted, ordinary pure Lean code. Every resulting
LRAT proof is checked, and `LRAT.check_sound` is the only link from the data
to unsatisfiability. Neither the mathematical strengthening nor the replay
optimization changes the trust policy.

With those first-pass changes, `lake build +equational_theories.Spectrum.Equation667Twelve.Exclusion`
replayed all 129 certificates and completed successfully in **600 seconds**.
The six collision batches took 418, 102, 578, 355, 360, and 380 seconds.
The slowest at that stage was **578 seconds**, down from 1,483 seconds (61% less).
It contains the formerly largest row and seven additional small cases;
the old 1,483-second batch contained just that row. The 77 bijective-square
checks also passed, with their slowest batch falling from about 164 to
113 seconds. Final mathematical assembly took approximately ten seconds.
These are incremental builds with the ordinary mathematical dependencies
already available, but all E667 compact certificates actually replayed.
The separation target also rebuilt successfully; `#spectrum_status` reports
`complete` with 138 registered native checks for the order-twelve exclusion
and both separation corollaries.

### Select only the input clauses used by the proof

The second pass keeps exactly the same learned-clause and deletion streams,
but records which original CNF clauses appear in the captured LRAT hints.
For the largest row, only **63,712 of 139,567** input clauses occur. Watching
the remaining clauses made hint reconstruction do unnecessary propagation.
The optional input mask lets reconstruction omit those watch lists while
preserving all clause IDs. The final `LRAT.check` still receives the entire
original Lean CNF. The selector is untrusted data, just like the clauses and
reconstructed hints; it cannot bypass that check.

`CompactRup.reconstruct` accepts both the original stream format and the
new optional header: after the initial clause-ID word, byte `m` introduces
one selection byte per original clause ID, including unused ID zero.
Unselected slots remain present as inactive placeholders. The generator
`scripts/spectrum_compact_rup.cpp --input-mask` extracts this information
from a trimmed binary LRAT proof. The collision preparation script's
`--select-inputs WORK --write-lean` option checks that removing the new
headers reproduces every old clause stream byte for byte before installation.

These 52 certificates now use xz compression (preset 6), which also more than
pays for the small masks. They occupy **26,898,276 bytes** in total, versus
29,136,214 before this pass; all 129 E667 certificates together occupy
**33,142,388 bytes**. The obsolete gzip copies have been removed. The
existing gzip embedding remains supported for the 77 other certificates;
both embeddings produce the same kind of literal byte array before checking.
Builds require `xz` as well as the existing `gzip`, `base64`, and `bash` tools.

Native profiling of the masked data took about **42 seconds** for four-point
reconstruction plus 2.6 seconds for checking, compared with 71 and 2.7 seconds
before the mask. The largest row took about **242 seconds** for reconstruction
and 7 seconds for checking. These profiler figures exclude Lean elaboration;
the full build measurements below include it. Separate small checks also
covered an omitted needed premise, an all-zero mask, and
truncated/misaligned headers; all these malformed examples were rejected.

The final focused `Separation` build passed in **320.97 seconds (5m21s)**,
replaying all 129 certificates with the ordinary mathematical dependencies
cached. This includes both the 52 masked xz streams and the 77 original gzip
streams. The six collision batches took **242, 57, 301, 186, 182, and 198
seconds**. The slowest batch is now **301 seconds**, down from 578 in the
first pass and 1,483 originally: a further 48% reduction, or 80% overall.
For comparison, the first-pass exclusion rebuild alone took 600.09 seconds;
the new timing also includes rebuilding the separation corollaries.
The order-twelve exclusion and both separation corollaries still audit as
`complete`, each with 138 registered native checks. No proof obligations
or additional assumptions were introduced.

To audit the saved data and rebuild the complete proof:

```sh
python3 scripts/spectrum_667_twelve_certificate.py
python3 scripts/spectrum_667_twelve_collision_certificate.py
lake build equational_theories.Spectrum.Equation667Twelve.Separation
```

The focused target includes the unrestricted exclusion and both separation
corollaries. The original formalization also passed the complete `Spectrum`
and `Definability` umbrella build, including `Spectrum.AxiomAudit` (17,849 jobs).
The optimization is validated separately by rebuilding the E667 certificates
and this focused target; it does not change any spectrum or definability result.
Regenerating the global negative-transfer
table also changes a shared dependency of the older E467 order-sixteen
certificate modules, so a subsequent build of the complete `Spectrum` or
`Definability` umbrella can replay those certificates too. That extra cost
is separate from the E667 timings above; isolating the E467 certificate data
from the generated small-order proofs would avoid this rebuild dependency.

The division operation is explicit:
`q(x,y) = y*((y*y)*x)`. It is left division in the original finite quasigroup.
The equation `q(x,d)=x` characterizes `d=D(x)`, and E667 implies
`q(q(d,q(x,y)),x)=y`. These transformations are proved in
`Equation667Division.lean`.

## A disproved shortcut

Involutive squaring does **not** necessarily preserve multiplication.
`data/spectrum/667_involutive_square_counterexample.json` contains a checked
nine-element counterexample. It was found by searching for two distinct
idempotent Latin operations `f,g` with

```
f(f(x,g(x,y)),x)=y,   g(g(x,f(x,y)),x)=y,
```

then finding an involution conjugating them and converting back through
left division. Thus the stronger conjecture that these coupled identities
force `f=g` is also false.

There is still a valid order-twelve consequence: if involutive squaring
preserved multiplication, removing that automorphism twist would give an
idempotent E667 model, already excluded at order twelve. This restricted
statement is proved in
`Spectrum.E667.involutive_square_not_multiplicative_twelve`.

The external results and their precise current proof status are recorded in
`data/spectrum/667_order12_square_search.json`. Search scripts are
`scripts/spectrum_667_fixed_square.py`,
`scripts/spectrum_667_square_collisions.py`, and
`scripts/spectrum_667_division_search.py`.
