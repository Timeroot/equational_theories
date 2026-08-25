import equational_theories.Definability.ExactEnd3R

/-!
# Term-structural certificate sources: `Magma.end3R`

For each of the following magmas, drawn from the `15` magmas on `Fin 3` whose endomorphism monoid is
exactly the order-`5` monoid of `Magma.endE3R`, the equations it satisfies that no earlier listed
magma does. Together they are the `71` equations that are worth using as the *source* `L'` of a
`Magma.end3R` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `7` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd3`.
-/

set_option maxHeartbeats 1000000

/-- `29` equations satisfied by `Magma.end3R 3`, and by no earlier member of the cover. -/
theorem end3R_satisfies_0 :
    Satisfies (Magma.end3R 3) [
      221, 224, 1664, 1684, 1687, 1894, 1904, 2296, 2306, 2314, 2318, 2322, 2333, 2368, 2372,
      2376, 2499, 2702, 2736, 2739, 2774, 2778, 2782, 3108, 3769, 3786, 3880, 3883, 4642
    ] := by decide!

/-- `27` equations satisfied by `Magma.end3R 0`, and by no earlier member of the cover. -/
theorem end3R_satisfies_1 :
    Satisfies (Magma.end3R 0) [
      105, 106, 428, 834, 839, 840, 841, 1037, 1240, 1243, 1245, 1246, 1247, 1250, 1259, 1260,
      1261, 1635, 1636, 1843, 1848, 1849, 3462, 3463, 3726, 3727, 4286
    ] := by decide!

/-- `5` equations satisfied by `Magma.end3R 10`, and by no earlier member of the cover. -/
theorem end3R_satisfies_2 :
    Satisfies (Magma.end3R 10) [
      258, 1454, 2044, 2653, 2663
    ] := by decide!

/-- `4` equations satisfied by `Magma.end3R 5`, and by no earlier member of the cover. -/
theorem end3R_satisfies_3 :
    Satisfies (Magma.end3R 5) [
      72, 916, 1525, 2063
    ] := by decide!

/-- `2` equations satisfied by `Magma.end3R 2`, and by no earlier member of the cover. -/
theorem end3R_satisfies_4 :
    Satisfies (Magma.end3R 2) [
      1660, 1871
    ] := by decide!

/-- `2` equations satisfied by `Magma.end3R 4`, and by no earlier member of the cover. -/
theorem end3R_satisfies_5 :
    Satisfies (Magma.end3R 4) [
      3555, 3961
    ] := by decide!

/-- `2` equations satisfied by `Magma.end3R 9`, and by no earlier member of the cover. -/
theorem end3R_satisfies_6 :
    Satisfies (Magma.end3R 9) [
      1668, 1875
    ] := by decide!
