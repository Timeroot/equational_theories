import equational_theories.Definability.ExactEnd6AI

/-!
# Term-structural certificate sources: `Magma.end6AI`

For each of the following magmas, drawn from the `2` magmas on `Fin 6` whose endomorphism monoid is
exactly the order-`420` monoid of `Magma.endE6AI`, the equations it satisfies that no earlier listed
magma does. Together they are the `10` equations that are worth using as the *source* `L'` of a
`Magma.end6AI` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `6` equations satisfied by `Magma.end6AI 1`, and by no earlier member of the cover. -/
theorem end6AI_satisfies_0 :
    Satisfies (Magma.end6AI 1) [
      1724, 2536, 2712, 3145, 3180, 4175
    ] := by decide!

/-- `4` equations satisfied by `Magma.end6AI 0`, and by no earlier member of the cover. -/
theorem end6AI_satisfies_1 :
    Satisfies (Magma.end6AI 0) [
      434, 1043, 1855, 3321
    ] := by decide!
