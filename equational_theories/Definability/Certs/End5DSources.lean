import equational_theories.Definability.ExactEnd5D

/-!
# Term-structural certificate sources: `Magma.end5D`

For each of the following magmas, drawn from the `80` magmas on `Fin 5` whose endomorphism monoid is
exactly the order-`13` monoid of `Magma.endE5D`, the equations it satisfies that no earlier listed
magma does. Together they are the `38` equations that are worth using as the *source* `L'` of a
`Magma.end5D` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `4` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `11` equations satisfied by `Magma.end5D 22`, and by no earlier member of the cover. -/
theorem end5D_satisfies_0 :
    Satisfies (Magma.end5D 22) [
      65, 473, 513, 562, 679, 713, 872, 1491, 1518, 3271, 4209
    ] := by decide!

/-- `11` equations satisfied by `Magma.end5D 54`, and by no earlier member of the cover. -/
theorem end5D_satisfies_1 :
    Satisfies (Magma.end5D 54) [
      261, 2054, 2061, 2660, 2856, 2873, 3056, 3079, 3091, 3317, 4071
    ] := by decide!

/-- `8` equations satisfied by `Magma.end5D 17`, and by no earlier member of the cover. -/
theorem end5D_satisfies_2 :
    Satisfies (Magma.end5D 17) [
      238, 2513, 2550, 2601, 2618, 2716, 2753, 2821
    ] := by decide!

/-- `8` equations satisfied by `Magma.end5D 40`, and by no earlier member of the cover. -/
theorem end5D_satisfies_3 :
    Satisfies (Magma.end5D 40) [
      103, 824, 830, 831, 1027, 1030, 1033, 1034
    ] := by decide!
