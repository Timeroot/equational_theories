import equational_theories.Definability.ExactEnd7D

/-!
# Term-structural certificate sources: `Magma.end7D`

For each of the following magmas, drawn from the `8` magmas on `Fin 7` whose endomorphism monoid is
exactly the order-`351` monoid of `Magma.endE7D`, the equations it satisfies that no earlier listed
magma does. Together they are the `10` equations that are worth using as the *source* `L'` of a
`Magma.end7D` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd7`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `5` equations satisfied by `Magma.end7D 2`, and by no earlier member of the cover. -/
theorem end7D_satisfies_0 :
    Satisfies (Magma.end7D 2) [
      153, 1640, 1660, 1834, 1843
    ] := by decide!

/-- `5` equations satisfied by `Magma.end7D 6`, and by no earlier member of the cover. -/
theorem end7D_satisfies_1 :
    Satisfies (Magma.end7D 6) [
      156, 1644, 1664, 1867, 1875
    ] := by decide!
