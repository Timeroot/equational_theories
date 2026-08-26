import equational_theories.Definability.ExactEnd4J

/-!
# Term-structural certificate sources: `Magma.end4J`

For each of the following magmas, drawn from the `2` magmas on `Fin 4` whose endomorphism monoid is
exactly the order-`10` monoid of `Magma.endE4J`, the equations it satisfies that no earlier listed
magma does. Together they are the `21` equations that are worth using as the *source* `L'` of a
`Magma.end4J` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd4`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `11` equations satisfied by `Magma.end4J 1`, and by no earlier member of the cover. -/
theorem end4J_satisfies_0 :
    Satisfies (Magma.end4J 1) [
      616, 822, 1234, 1660, 1871, 2452, 2646, 2675, 2852, 2886, 3525
    ] := by decide!

/-- `10` equations satisfied by `Magma.end4J 0`, and by no earlier member of the cover. -/
theorem end4J_satisfies_1 :
    Satisfies (Magma.end4J 0) [
      619, 653, 860, 1055, 1668, 1875, 2273, 2649, 2862, 3935
    ] := by decide!
