import equational_theories.Definability.ExactEnd6AG

/-!
# Term-structural certificate sources: `Magma.end6AG`

For each of the following magmas, drawn from the `2` magmas on `Fin 6` whose endomorphism monoid is
exactly the order-`180` monoid of `Magma.endE6AG`, the equations it satisfies that no earlier listed
magma does. Together they are the `10` equations that are worth using as the *source* `L'` of a
`Magma.end6AG` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `5` equations satisfied by `Magma.end6AG 0`, and by no earlier member of the cover. -/
theorem end6AG_satisfies_0 :
    Satisfies (Magma.end6AG 0) [
      2296, 2351, 2554, 3285, 3488
    ] := by decide!

/-- `5` equations satisfied by `Magma.end6AG 1`, and by no earlier member of the cover. -/
theorem end6AG_satisfies_1 :
    Satisfies (Magma.end6AG 1) [
      1060, 1240, 1263, 3902, 4105
    ] := by decide!
