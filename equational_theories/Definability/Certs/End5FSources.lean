import equational_theories.Definability.ExactEnd5F

/-!
# Term-structural certificate sources: `Magma.end5F`

For each of the following magmas, drawn from the `8` magmas on `Fin 5` whose endomorphism monoid is
exactly the order-`13` monoid of `Magma.endE5F`, the equations it satisfies that no earlier listed
magma does. Together they are the `168` equations that are worth using as the *source* `L'` of a
`Magma.end5F` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `4` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `94` equations satisfied by `Magma.end5F 6`, and by no earlier member of the cover. -/
theorem end5F_satisfies_0 :
    Satisfies (Magma.end5F 6) [
      11, 31, 40, 440, 444, 452, 481, 643, 655, 658, 695, 820, 823, 846, 850, 858, 879, 887, 978,
      1026, 1049, 1061, 1064, 1101, 1229, 1252, 1256, 1264, 1384, 1488, 1496, 1515, 1523, 1537,
      1682, 1710, 1740, 1885, 1902, 1993, 2038, 2041, 2105, 2132, 2146, 2300, 2319, 2340, 2355,
      2389, 2503, 2543, 2592, 2602, 2605, 2650, 2706, 2725, 2733, 2746, 2755, 2761, 2795, 2949,
      2998, 3008, 3011, 3139, 3152, 3161, 3167, 3201, 3282, 3286, 3294, 3485, 3497, 3500, 3665,
      3677, 3688, 3692, 3700, 3891, 3903, 3906, 4094, 4098, 4106, 4325, 4461, 4491, 4497, 4620
    ] := by decide!

/-- `44` equations satisfied by `Magma.end5F 0`, and by no earlier member of the cover. -/
theorem end5F_satisfies_1 :
    Satisfies (Magma.end5F 0) [
      335, 384, 3276, 3293, 3298, 3303, 3343, 3473, 3486, 3499, 3501, 3502, 3672, 3682, 3686,
      3689, 3690, 3691, 3693, 3699, 3704, 3709, 3872, 3879, 3892, 3907, 3908, 4092, 4095, 4097,
      4099, 4130, 4280, 4346, 4355, 4399, 4471, 4484, 4498, 4499, 4500, 4592, 4609, 4623
    ] := by decide!

/-- `15` equations satisfied by `Magma.end5F 2`, and by no earlier member of the cover. -/
theorem end5F_satisfies_2 :
    Satisfies (Magma.end5F 2) [
      100, 108, 109, 818, 821, 844, 847, 849, 851, 1224, 1227, 1250, 1253, 1255, 1257
    ] := by decide!

/-- `15` equations satisfied by `Magma.end5F 4`, and by no earlier member of the cover. -/
theorem end5F_satisfies_3 :
    Satisfies (Magma.end5F 4) [
      218, 231, 246, 2290, 2318, 2364, 2385, 2406, 2430, 2696, 2724, 2770, 2791, 2812, 2836
    ] := by decide!
