import equational_theories.Definability.ExactEnd6AK

/-!
# Term-structural certificate sources: `Magma.end6AK`

For each of the following magmas, drawn from the `1` magmas on `Fin 6` whose endomorphism monoid is
exactly the order-`63` monoid of `Magma.endE6AK`, the equations it satisfies that no earlier listed
magma does. Together they are the `13` equations that are worth using as the *source* `L'` of a
`Magma.end6AK` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `1` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `13` equations satisfied by `Magma.end6AK 0`, and by no earlier member of the cover. -/
theorem end6AK_satisfies_0 :
    Satisfies (Magma.end6AK 0) [
      332, 387, 3342, 3345, 3545, 3548, 3555, 3751, 3758, 3954, 3961, 3964, 4157
    ] := by decide!
