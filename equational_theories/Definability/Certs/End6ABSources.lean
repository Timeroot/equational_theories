import equational_theories.Definability.ExactEnd6AB

/-!
# Term-structural certificate sources: `Magma.end6AB`

For each of the following magmas, drawn from the `1` magmas on `Fin 6` whose endomorphism monoid is
exactly the order-`68` monoid of `Magma.endE6AB`, the equations it satisfies that no earlier listed
magma does. Together they are the `14` equations that are worth using as the *source* `L'` of a
`Magma.end6AB` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `1` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `14` equations satisfied by `Magma.end6AB 0`, and by no earlier member of the cover. -/
theorem end6AB_satisfies_0 :
    Satisfies (Magma.end6AB 0) [
      427, 861, 1239, 2293, 2699, 2808, 3105, 3350, 3573, 3703, 3756, 3823, 3979, 4229
    ] := by decide!
