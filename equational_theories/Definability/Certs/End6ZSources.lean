import equational_theories.Definability.ExactEnd6Z

/-!
# Term-structural certificate sources: `Magma.end6Z`

For each of the following magmas, drawn from the `4` magmas on `Fin 6` whose endomorphism monoid is
exactly the order-`36` monoid of `Magma.endE6Z`, the equations it satisfies that no earlier listed
magma does. Together they are the `15` equations that are worth using as the *source* `L'` of a
`Magma.end6Z` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `8` equations satisfied by `Magma.end6Z 2`, and by no earlier member of the cover. -/
theorem end6Z_satisfies_0 :
    Satisfies (Magma.end6Z 2) [
      159, 416, 1231, 1234, 1631, 1660, 1837, 1871
    ] := by decide!

/-- `7` equations satisfied by `Magma.end6Z 3`, and by no earlier member of the cover. -/
theorem end6Z_satisfies_1 :
    Satisfies (Magma.end6Z 3) [
      1634, 1668, 1847, 1875, 2263, 2273, 3055
    ] := by decide!
