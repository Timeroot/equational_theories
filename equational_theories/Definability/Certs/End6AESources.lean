import equational_theories.Definability.ExactEnd6AE

/-!
# Term-structural certificate sources: `Magma.end6AE`

For each of the following magmas, drawn from the `2` magmas on `Fin 6` whose endomorphism monoid is
exactly the order-`58` monoid of `Magma.endE6AE`, the equations it satisfies that no earlier listed
magma does. Together they are the `14` equations that are worth using as the *source* `L'` of a
`Magma.end6AE` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `7` equations satisfied by `Magma.end6AE 0`, and by no earlier member of the cover. -/
theorem end6AE_satisfies_0 :
    Satisfies (Magma.end6AE 0) [
      1042, 1052, 1243, 1259, 1262, 3888, 3894
    ] := by decide!

/-- `7` equations satisfied by `Magma.end6AE 1`, and by no earlier member of the cover. -/
theorem end6AE_satisfies_1 :
    Satisfies (Magma.end6AE 1) [
      2277, 2314, 2372, 2571, 2588, 3475, 3496
    ] := by decide!
