import equational_theories.Definability.ExactEnd6R

/-!
# Term-structural certificate sources: `Magma.end6R`

For each of the following magmas, drawn from the `2` magmas on `Fin 6` whose endomorphism monoid is
exactly the order-`52` monoid of `Magma.endE6R`, the equations it satisfies that no earlier listed
magma does. Together they are the `57` equations that are worth using as the *source* `L'` of a
`Magma.end6R` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `30` equations satisfied by `Magma.end6R 0`, and by no earlier member of the cover. -/
theorem end6R_satisfies_0 :
    Satisfies (Magma.end6R 0) [
      106, 834, 837, 838, 839, 840, 841, 842, 1041, 1048, 1051, 1059, 1063, 1067, 1240, 1243,
      1244, 1245, 1246, 1247, 1250, 1259, 1260, 1261, 1266, 1270, 1834, 1853, 3661, 3727
    ] := by decide!

/-- `27` equations satisfied by `Magma.end6R 1`, and by no earlier member of the cover. -/
theorem end6R_satisfies_1 :
    Satisfies (Magma.end6R 1) [
      224, 1644, 1650, 2259, 2269, 2285, 2296, 2306, 2314, 2318, 2322, 2333, 2368, 2372, 2376,
      2488, 2652, 2662, 2665, 2702, 2739, 2774, 2778, 2782, 3052, 3664, 3769
    ] := by decide!
