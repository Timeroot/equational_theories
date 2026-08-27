import equational_theories.Definability.ExactEnd6D

/-!
# Term-structural certificate sources: `Magma.end6D`

For each of the following magmas, drawn from the `2` magmas on `Fin 6` whose endomorphism monoid is
exactly the order-`36` monoid of `Magma.endE6D`, the equations it satisfies that no earlier listed
magma does. Together they are the `34` equations that are worth using as the *source* `L'` of a
`Magma.end6D` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `17` equations satisfied by `Magma.end6D 0`, and by no earlier member of the cover. -/
theorem end6D_satisfies_0 :
    Satisfies (Magma.end6D 0) [
      53, 261, 430, 630, 843, 1432, 1456, 2054, 2061, 2062, 2264, 2270, 2666, 2856, 2860, 2873,
      4403
    ] := by decide!

/-- `17` equations satisfied by `Magma.end6D 1`, and by no earlier member of the cover. -/
theorem end6D_satisfies_1 :
    Satisfies (Magma.end6D 1) [
      65, 273, 679, 713, 723, 947, 1288, 1370, 1491, 1506, 1518, 2097, 2203, 2709, 2902, 3142,
      4420
    ] := by decide!
