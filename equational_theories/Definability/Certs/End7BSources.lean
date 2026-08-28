import equational_theories.Definability.ExactEnd7B

/-!
# Term-structural certificate sources: `Magma.end7B`

For each of the following magmas, drawn from the `38` magmas on `Fin 7` whose endomorphism monoid is
exactly the order-`223` monoid of `Magma.endE7B`, the equations it satisfies that no earlier listed
magma does. Together they are the `14` equations that are worth using as the *source* `L'` of a
`Magma.end7B` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd7`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `7` equations satisfied by `Magma.end7B 6`, and by no earlier member of the cover. -/
theorem end7B_satisfies_0 :
    Satisfies (Magma.end7B 6) [
      49, 416, 422, 619, 625, 1231, 1631
    ] := by decide!

/-- `7` equations satisfied by `Magma.end7B 37`, and by no earlier member of the cover. -/
theorem end7B_satisfies_1 :
    Satisfies (Magma.end7B 37) [
      260, 1847, 2263, 2852, 2882, 3055, 3085
    ] := by decide!
