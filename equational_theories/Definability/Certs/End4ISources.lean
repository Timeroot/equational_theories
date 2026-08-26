import equational_theories.Definability.ExactEnd4I

/-!
# Term-structural certificate sources: `Magma.end4I`

For each of the following magmas, drawn from the `3` magmas on `Fin 4` whose endomorphism monoid is
exactly the order-`10` monoid of `Magma.endE4I`, the equations it satisfies that no earlier listed
magma does. Together they are the `40` equations that are worth using as the *source* `L'` of a
`Magma.end4I` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `3` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd4`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `17` equations satisfied by `Magma.end4I 0`, and by no earlier member of the cover. -/
theorem end4I_satisfies_0 :
    Satisfies (Magma.end4I 0) [
      106, 839, 840, 841, 1037, 1237, 1240, 1243, 1245, 1246, 1247, 1260, 1261, 1636, 3463, 3726,
      3727
    ] := by decide!

/-- `17` equations satisfied by `Magma.end4I 1`, and by no earlier member of the cover. -/
theorem end4I_satisfies_1 :
    Satisfies (Magma.end4I 1) [
      224, 1904, 2296, 2306, 2322, 2333, 2368, 2372, 2376, 2415, 2499, 2739, 2774, 2782, 3769,
      3786, 3883
    ] := by decide!

/-- `6` equations satisfied by `Magma.end4I 2`, and by no earlier member of the cover. -/
theorem end4I_satisfies_2 :
    Satisfies (Magma.end4I 2) [
      3345, 3548, 3555, 3954, 3961, 4157
    ] := by decide!
