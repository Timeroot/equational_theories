import equational_theories.Definability.ExactEnd4M

/-!
# Term-structural certificate sources: `Magma.end4M`

For each of the following magmas, drawn from the `2` magmas on `Fin 4` whose endomorphism monoid is
exactly the order-`12` monoid of `Magma.endE4M`, the equations it satisfies that no earlier listed
magma does. Together they are the `33` equations that are worth using as the *source* `L'` of a
`Magma.end4M` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd4`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `24` equations satisfied by `Magma.end4M 1`, and by no earlier member of the cover. -/
theorem end4M_satisfies_0 :
    Satisfies (Magma.end4M 1) [
      257, 260, 266, 1441, 2040, 2070, 2655, 2679, 2683, 2691, 2849, 2858, 2868, 2878, 2882,
      2890, 2894, 3055, 3061, 3081, 3085, 3089, 3097, 3732
    ] := by decide!

/-- `9` equations satisfied by `Magma.end4M 0`, and by no earlier member of the cover. -/
theorem end4M_satisfies_1 :
    Satisfies (Magma.end4M 0) [
      416, 422, 446, 856, 864, 1431, 1437, 2037, 3728
    ] := by decide!
