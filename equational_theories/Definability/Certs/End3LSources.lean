import equational_theories.Definability.ExactEnd3L

/-!
# Term-structural certificate sources: `Magma.end3L`

For each of the following magmas, drawn from the `4` magmas on `Fin 3` whose endomorphism monoid is
exactly the order-`6` monoid of `Magma.endE3L`, the equations it satisfies that no earlier listed
magma does. Together they are the `251` equations that are worth using as the *source* `L'` of a
`Magma.end3L` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `4` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd3`.
-/

set_option maxHeartbeats 1000000

/-- `135` equations satisfied by `Magma.end3L 0`, and by no earlier member of the cover. -/
theorem end3L_satisfies_0 :
    Satisfies (Magma.end3L 0) [
      25, 101, 156, 205, 214, 257, 260, 263, 266, 323, 361, 378, 381, 616, 822, 1022, 1025, 1031,
      1228, 1231, 1234, 1441, 1631, 1644, 1647, 1650, 1837, 1847, 1857, 1867, 2040, 2050, 2060,
      2070, 2240, 2243, 2249, 2259, 2263, 2269, 2273, 2277, 2285, 2443, 2446, 2449, 2452, 2456,
      2462, 2469, 2472, 2476, 2480, 2484, 2488, 2646, 2649, 2652, 2655, 2659, 2662, 2665, 2672,
      2675, 2679, 2683, 2687, 2691, 2849, 2852, 2858, 2862, 2865, 2868, 2872, 2875, 2878, 2882,
      2886, 2890, 2894, 3052, 3055, 3061, 3065, 3071, 3075, 3081, 3085, 3089, 3093, 3097, 3306,
      3309, 3316, 3458, 3512, 3515, 3519, 3525, 3732, 3736, 3864, 3867, 3873, 3918, 3921, 3925,
      3931, 3935, 3939, 3943, 3947, 4070, 4073, 4076, 4121, 4124, 4128, 4131, 4134, 4138, 4142,
      4146, 4150, 4284, 4382, 4396, 4402, 4473, 4476, 4599, 4602, 4655, 4675
    ] := by decide!

/-- `94` equations satisfied by `Magma.end3L 2`, and by no earlier member of the cover. -/
theorem end3L_satisfies_1 :
    Satisfies (Magma.end3L 2) [
      49, 52, 55, 58, 104, 110, 153, 309, 329, 413, 416, 419, 422, 426, 432, 442, 446, 450, 454,
      458, 619, 622, 625, 629, 632, 635, 642, 645, 649, 653, 657, 661, 819, 828, 832, 835, 838,
      842, 845, 848, 852, 856, 860, 864, 1035, 1041, 1045, 1048, 1051, 1055, 1059, 1063, 1067,
      1238, 1244, 1258, 1262, 1266, 1270, 1428, 1431, 1434, 1437, 1634, 1637, 1640, 1834, 1850,
      1853, 2037, 3255, 3261, 3264, 3312, 3322, 3326, 3330, 3334, 3338, 3461, 3467, 3529, 3533,
      3537, 3541, 3718, 3728, 4287, 4316, 4340, 4360, 4432, 4508, 4516
    ] := by decide!

/-- `11` equations satisfied by `Magma.end3L 1`, and by no earlier member of the cover. -/
theorem end3L_satisfies_2 :
    Satisfies (Magma.end3L 1) [
      325, 3315, 3318, 3518, 3521, 3714, 3724, 4314, 4398, 4433, 4436
    ] := by decide!

/-- `11` equations satisfied by `Magma.end3L 3`, and by no earlier member of the cover. -/
theorem end3L_satisfies_3 :
    Satisfies (Magma.end3L 3) [
      385, 3749, 3752, 3952, 3962, 4155, 4165, 4406, 4442, 4480, 4606
    ] := by decide!
