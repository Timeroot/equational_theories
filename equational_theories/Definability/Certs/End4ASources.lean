import equational_theories.Definability.ExactEnd4A

/-!
# Term-structural certificate sources: `Magma.end4A`

For each of the following magmas, drawn from the `2` magmas on `Fin 4` whose endomorphism monoid is
exactly the order-`16` monoid of `Magma.endE4A`, the equations it satisfies that no earlier listed
magma does. Together they are the `2` equations that are worth using as the *source* `L'` of a
`Magma.end4A` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd4`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `1` equations satisfied by `Magma.end4A 0`, and by no earlier member of the cover. -/
theorem end4A_satisfies_0 :
    Satisfies (Magma.end4A 0) [
      114
    ] := by decide!

/-- `1` equations satisfied by `Magma.end4A 1`, and by no earlier member of the cover. -/
theorem end4A_satisfies_1 :
    Satisfies (Magma.end4A 1) [
      27
    ] := by decide!
