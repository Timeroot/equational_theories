import equational_theories.Definability.ExactEnd5X

/-!
# Term-structural certificate sources: `Magma.end5X`

For each of the following magmas, drawn from the `12` magmas on `Fin 5` whose endomorphism monoid is
exactly the order-`28` monoid of `Magma.endE5X`, the equations it satisfies that no earlier listed
magma does. Together they are the `8` equations that are worth using as the *source* `L'` of a
`Magma.end5X` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `1` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `8` equations satisfied by `Magma.end5X 0`, and by no earlier member of the cover. -/
theorem end5X_satisfies_0 :
    Satisfies (Magma.end5X 0) [
      3417, 3588, 3601, 3756, 3823, 3994, 4007, 4162
    ] := by decide!
