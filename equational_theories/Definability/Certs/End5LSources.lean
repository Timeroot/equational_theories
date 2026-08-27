import equational_theories.Definability.ExactEnd5L

/-!
# Term-structural certificate sources: `Magma.end5L`

For each of the following magmas, drawn from the `4` magmas on `Fin 5` whose endomorphism monoid is
exactly the order-`13` monoid of `Magma.endE5L`, the equations it satisfies that no earlier listed
magma does. Together they are the `49` equations that are worth using as the *source* `L'` of a
`Magma.end5L` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `27` equations satisfied by `Magma.end5L 0`, and by no earlier member of the cover. -/
theorem end5L_satisfies_0 :
    Satisfies (Magma.end5L 0) [
      111, 361, 371, 443, 1042, 1052, 1056, 1068, 1265, 1271, 3873, 3884, 3894, 3898, 3902, 3910,
      3931, 4072, 4076, 4085, 4087, 4104, 4105, 4107, 4113, 4584, 4651
    ] := by decide!

/-- `22` equations satisfied by `Magma.end5L 2`, and by no earlier member of the cover. -/
theorem end5L_satisfies_1 :
    Satisfies (Magma.end5L 2) [
      242, 309, 319, 2420, 2425, 2517, 2571, 2588, 2623, 3197, 3275, 3467, 3478, 3488, 3492,
      3504, 3529, 4269, 4279, 4327, 4331, 4336
    ] := by decide!
