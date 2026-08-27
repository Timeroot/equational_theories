import equational_theories.Definability.ExactEnd6E

/-!
# Term-structural certificate sources: `Magma.end6E`

For each of the following magmas, drawn from the `4` magmas on `Fin 6` whose endomorphism monoid is
exactly the order-`24` monoid of `Magma.endE6E`, the equations it satisfies that no earlier listed
magma does. Together they are the `22` equations that are worth using as the *source* `L'` of a
`Magma.end6E` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `11` equations satisfied by `Magma.end6E 0`, and by no earlier member of the cover. -/
theorem end6E_satisfies_0 :
    Satisfies (Magma.end6E 0) [
      16, 500, 528, 575, 1082, 1122, 1184, 1312, 1780, 1934, 1949
    ] := by decide!

/-- `11` equations satisfied by `Magma.end6E 1`, and by no earlier member of the cover. -/
theorem end6E_satisfies_1 :
    Satisfies (Magma.end6E 1) [
      26, 1658, 1662, 1873, 2241, 2447, 2470, 2485, 3053, 3083, 3094
    ] := by decide!
