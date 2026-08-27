import equational_theories.Definability.ExactEnd6B

/-!
# Term-structural certificate sources: `Magma.end6B`

For each of the following magmas, drawn from the `12` magmas on `Fin 6` whose endomorphism monoid is
exactly the order-`21` monoid of `Magma.endE6B`, the equations it satisfies that no earlier listed
magma does. Together they are the `99` equations that are worth using as the *source* `L'` of a
`Magma.end6B` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `5` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `58` equations satisfied by `Magma.end6B 0`, and by no earlier member of the cover. -/
theorem end6B_satisfies_0 :
    Satisfies (Magma.end6B 0) [
      316, 320, 368, 369, 3276, 3282, 3286, 3293, 3473, 3485, 3486, 3489, 3499, 3500, 3501, 3502,
      3665, 3672, 3677, 3682, 3686, 3688, 3689, 3690, 3691, 3692, 3693, 3699, 3700, 3704, 3709,
      3872, 3879, 3891, 3892, 3906, 3907, 3908, 3954, 4092, 4094, 4095, 4097, 4098, 4099, 4109,
      4157, 4280, 4346, 4355, 4390, 4443, 4471, 4484, 4497, 4498, 4499, 4500
    ] := by decide!

/-- `19` equations satisfied by `Magma.end6B 11`, and by no earlier member of the cover. -/
theorem end6B_satisfies_1 :
    Satisfies (Magma.end6B 11) [
      455, 508, 643, 658, 731, 914, 981, 1137, 1523, 1929, 1996, 2132, 2949, 2964, 3011, 3297,
      3895, 4297, 4424
    ] := by decide!

/-- `11` equations satisfied by `Magma.end6B 10`, and by no earlier member of the cover. -/
theorem end6B_satisfies_2 :
    Satisfies (Magma.end6B 10) [
      833, 861, 2699, 2808, 3350, 3573, 3703, 3756, 3823, 3979, 4229
    ] := by decide!

/-- `9` equations satisfied by `Magma.end6B 9`, and by no earlier member of the cover. -/
theorem end6B_satisfies_3 :
    Satisfies (Magma.end6B 9) [
      647, 1673, 1726, 2474, 2688, 2741, 3147, 4477, 4612
    ] := by decide!

/-- `2` equations satisfied by `Magma.end6B 2`, and by no earlier member of the cover. -/
theorem end6B_satisfies_4 :
    Satisfies (Magma.end6B 2) [
      3345, 3548
    ] := by decide!
