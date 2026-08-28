import equational_theories.Definability.ExactEnd6U

/-!
# Term-structural certificate sources: `Magma.end6U`

For each of the following magmas, drawn from the `14` magmas on `Fin 6` whose endomorphism monoid is
exactly the order-`18` monoid of `Magma.endE6U`, the equations it satisfies that no earlier listed
magma does. Together they are the `45` equations that are worth using as the *source* `L'` of a
`Magma.end6U` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `3` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `21` equations satisfied by `Magma.end6U 8`, and by no earlier member of the cover. -/
theorem end6U_satisfies_0 :
    Satisfies (Magma.end6U 8) [
      242, 319, 2420, 2425, 2517, 2623, 3275, 3289, 3290, 3297, 3301, 3302, 3478, 3492, 3504,
      4279, 4324, 4327, 4331, 4336, 4337
    ] := by decide!

/-- `20` equations satisfied by `Magma.end6U 1`, and by no earlier member of the cover. -/
theorem end6U_satisfies_1 :
    Satisfies (Magma.end6U 1) [
      111, 371, 1271, 3884, 3898, 3910, 4072, 4081, 4085, 4087, 4101, 4104, 4107, 4109, 4113,
      4594, 4616, 4626, 4639, 4651
    ] := by decide!

/-- `4` equations satisfied by `Magma.end6U 0`, and by no earlier member of the cover. -/
theorem end6U_satisfies_2 :
    Satisfies (Magma.end6U 0) [
      861, 2808, 3675, 3703
    ] := by decide!
