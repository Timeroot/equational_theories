import equational_theories.Definability.ExactEnd4B

/-!
# Term-structural certificate sources: `Magma.end4B`

For each of the following magmas, drawn from the `1` magmas on `Fin 4` whose endomorphism monoid is
exactly the order-`16` monoid of `Magma.endE4B`, the equations it satisfies that no earlier listed
magma does. Together they are the `1` equations that are worth using as the *source* `L'` of a
`Magma.end4B` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `1` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd4`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `1` equations satisfied by `Magma.end4B 0`, and by no earlier member of the cover. -/
theorem end4B_satisfies_0 :
    Satisfies (Magma.end4B 0) [
      2789
    ] := by decide!
