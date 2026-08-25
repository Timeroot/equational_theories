import equational_theories.Definability.ExactEnd3X

/-!
# Term-structural certificate sources: `Magma.end3X`

For each of the following magmas, drawn from the `15` magmas on `Fin 3` whose endomorphism monoid is
exactly the order-`4` monoid of `Magma.endE3X`, the equations it satisfies that no earlier listed
magma does. Together they are the `2` equations that are worth using as the *source* `L'` of a
`Magma.end3X` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd3`.
-/

set_option maxHeartbeats 1000000

/-- `1` equations satisfied by `Magma.end3X 0`, and by no earlier member of the cover. -/
theorem end3X_satisfies_0 :
    Satisfies (Magma.end3X 0) [
      4629
    ] := by decide!

/-- `1` equations satisfied by `Magma.end3X 1`, and by no earlier member of the cover. -/
theorem end3X_satisfies_1 :
    Satisfies (Magma.end3X 1) [
      4291
    ] := by decide!
