# Order forty cannot have nine central elements

Research theorem, 20 September 2026. **The nine-central case is now
excluded.** The proof combines analytic arguments, small explicit finite
graph checks, and five previously retained LRAT proofs in an earlier
profile reduction. The new final step needs no SAT certificates. This
is not yet a Lean theorem, and the full spectrum conjecture remains open.

**Theorem.** An E1485 magma of order forty and minimum translation
degree four cannot have nine central elements.

## Proof map

Write `Z,A,B,T` for the degree classes `4,5,8,10`.

1. If any member of `A` has three top neighbors in either direction,
   the [complement-tiling reduction](1485_nine_central_three_profile.md)
   and [eighteen-top exclusion](1485_nine_central_eighteen_top.md) leave
   sixteen or seventeen tops. The
   [sixteen-top proof](1485_nine_central_sixteen_exclusion.md) and
   [seventeen-top proof](1485_nine_central_seventeen_degree_counts.md)
   exclude both possibilities.
2. Otherwise every member of `A` has four top neighbors in each
   direction. The [analytic class-count reduction](1485_order_forty_nine_central_reduction.md)
   forces `(|Z|,|A|,|B|,|T|)=(9,7,7,17)`. Each `B` vertex
   has one sharp neighbor in each direction and balanced top counts.
3. Let `D` be ordinary adjacency on the seven vertices of `B`,
   `Q` its sharp endpoint permutation, `d_x` its balanced degrees,
   `K=Σd_x`, and `τ` its number of bad internal two-edge paths.
   The [basic graph bounds](1485_order_forty_nine_central_nonuniform_B.md),
   including the [odd-degree trace obstruction](1485_order_forty_nine_central_uniform_exclusion.md),
   give `1≤d_x≤4` and `K≤20`.
4. The [central-moment inequality](1485_nine_central_missing_degree_five_neighbor.md#4-the-central-gap-forces-nineteen-or-twenty-internal-edges)
   gives `K≥19+2n_1`, where `n_1` counts internal degree-one
   vertices. Therefore `K=19` or `20`, all degrees are at least
   two, and the same calculation gives `τ≥19`.
5. If `τ=K`, the [whole-orbit lemma](1485_order_forty_nine_central_dense_closed_orbits.md)
   excludes all 81 normalized cases. Its only two intermediate graphs
   have explicit forbidden five-walks.
6. The only other possibility is `K=20,τ=19`. The
   [single-defect lemma](1485_order_forty_nine_central_twenty_one_defect.md)
   excludes all 396 normalized cases. No graph survives even the
   degree, forbidden-shift, and repeated-middle constraints.

Both alternatives for the degree-five profiles are impossible, proving
the theorem.

## Proof-status inventory

| Component | Kind of proof |
| --- | --- |
| Three-profile complement tilings and central moments | Analytic; tiny integer table checks are also provided |
| Three-profile eighteen-top exclusion | Three analytic cases and **five retained, independently checked LRAT refutations**; [certificate inventory](../data/1485_certificates/NINE_CENTRAL_H18.md) |
| Three-profile sixteen-top exclusion | Analytic reduction and two explicit sixteen-bit graph lemmas, with independent controls |
| Three-profile seventeen-top exclusion | Analytic |
| All-four-profile class counts and central-moment gap | Analytic, independently audited |
| Final full-rotation and single-defect branches | Exact standard-Python orbit checks, independently audited and rerun |

Thus the whole theorem is **not claimed to be purely analytic or
Lean-checked**. In particular, "no new SAT dependency in the final
step" does not remove the five older certificates from step 1.

The separate fifteen-edge and sixteen-edge graph checks are independent
corroboration, not mathematical dependencies of the final reduction.
Some final checkers reuse their elementary partition/orbit code; this
code reuse does not invoke those earlier finite lemmas.

## Reproduce the new final finite step

```sh
python3 scripts/1485_m9_dense_closed_orbits_check.py
python3 scripts/1485_m9_twenty_one_defect_check.py
```

These cover **477 normalized cases** and **25,754 recursion nodes**.
They use no external Python packages or SAT solver. Both have explicit
normalization checks, positive intermediate fixtures, negative controls,
and refusal of Python's assertion-disabling `-O` mode. The linked
component proofs give the search completeness arguments and exact counts.
Independent root replays took **2.264 seconds** and **8.043 seconds**,
respectively, including the normalization and fixture controls.

## Remaining spectrum problem

Together with the previous four-central and ten-central exclusions,
this leaves central counts **five through eight** at order forty.
Order forty is not yet excluded. Arbitrary minimum degree at least
four remains open, so this is not the square-or-double-square spectrum
characterization.
