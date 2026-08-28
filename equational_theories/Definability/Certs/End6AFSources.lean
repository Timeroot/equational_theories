import equational_theories.Definability.ExactEnd6AF

/-!
# Term-structural certificate sources: `Magma.end6AF`

For each of the following magmas, drawn from the `4` magmas on `Fin 6` whose endomorphism monoid is
exactly the order-`30` monoid of `Magma.endE6AF`, the equations it satisfies that no earlier listed
magma does. Together they are the `14` equations that are worth using as the *source* `L'` of a
`Magma.end6AF` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `7` equations satisfied by `Magma.end6AF 0`, and by no earlier member of the cover. -/
theorem end6AF_satisfies_0 :
    Satisfies (Magma.end6AF 0) [
      3726, 3727, 3728, 3730, 3939, 3947, 4506
    ] := by decide!

/-- `7` equations satisfied by `Magma.end6AF 2`, and by no earlier member of the cover. -/
theorem end6AF_satisfies_1 :
    Satisfies (Magma.end6AF 2) [
      3515, 3541, 3732, 3769, 3786, 3837, 4391
    ] := by decide!
