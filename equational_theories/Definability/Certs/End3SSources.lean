import equational_theories.Definability.ExactEnd3S

/-!
# Term-structural certificate sources: `Magma.end3S`

For each of the following magmas, drawn from the `3` magmas on `Fin 3` whose endomorphism monoid is
exactly the order-`5` monoid of `Magma.endE3S`, the equations it satisfies that no earlier listed
magma does. Together they are the `60` equations that are worth using as the *source* `L'` of a
`Magma.end3S` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `3` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd3`.
-/

set_option maxHeartbeats 1000000

/-- `29` equations satisfied by `Magma.end3S 2`, and by no earlier member of the cover. -/
theorem end3S_satisfies_0 :
    Satisfies (Magma.end3S 2) [
      452, 455, 647, 655, 861, 1061, 1429, 1515, 1523, 2038, 2124, 2132, 2592, 2808, 2964, 2998,
      3201, 3214, 3350, 3497, 3573, 3675, 3703, 3756, 3823, 3903, 3979, 4229, 4497
    ] := by decide!

/-- `18` equations satisfied by `Magma.end3S 1`, and by no earlier member of the cover. -/
theorem end3S_satisfies_1 :
    Satisfies (Magma.end3S 1) [
      319, 3275, 3285, 3289, 3290, 3301, 3302, 3478, 3488, 3492, 3496, 3504, 4105, 4279, 4324,
      4331, 4336, 4337
    ] := by decide!

/-- `13` equations satisfied by `Magma.end3S 0`, and by no earlier member of the cover. -/
theorem end3S_satisfies_2 :
    Satisfies (Magma.end3S 0) [
      371, 3884, 3894, 3898, 3902, 3910, 4085, 4087, 4101, 4107, 4113, 4594, 4626
    ] := by decide!
