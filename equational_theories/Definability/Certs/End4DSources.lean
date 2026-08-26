import equational_theories.Definability.ExactEnd4D

/-!
# Term-structural certificate sources: `Magma.end4D`

For each of the following magmas, drawn from the `2` magmas on `Fin 4` whose endomorphism monoid is
exactly the order-`16` monoid of `Magma.endE4D`, the equations it satisfies that no earlier listed
magma does. Together they are the `12` equations that are worth using as the *source* `L'` of a
`Magma.end4D` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `1` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd4`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `12` equations satisfied by `Magma.end4D 0`, and by no earlier member of the cover. -/
theorem end4D_satisfies_0 :
    Satisfies (Magma.end4D 0) [
      162, 1461, 1465, 1469, 1473, 1676, 1879, 2046, 2066, 2074, 2082, 3744
    ] := by decide!
