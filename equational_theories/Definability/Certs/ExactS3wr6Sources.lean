import equational_theories.Definability.ExactAut6S3wr6

/-!
# Structural certificate sources: `Magma.exactS3wr6`

For each of the following magmas, drawn from the `4` magmas on `Fin 6` whose automorphism group is
exactly the order-`72` group of `Magma.permES3wr6`, the equations it satisfies that no earlier
listed magma does. Together they are the `212` equations that are worth using as the *source* `L'`
of a `Magma.exactS3wr6` certificate -- the rest have such a model too, but the resulting facts are
already implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactAut6`.
-/

set_option maxHeartbeats 1000000
-- each `rfl` below reads one entry out of `Magma.memArrS3wr6`, and reading entry `k` recurses `k`
-- deep into the list behind the array
set_option maxRecDepth 100000

/-- `191` equations satisfied by `Magma.exactS3wr6 0`, and by no earlier member of the cover. -/
theorem exactS3wr6_satisfies_0 :
    Satisfies (Magma.exactS3wr6 0) [
      10, 25, 49, 52, 101, 104, 107, 110, 153, 156, 159, 205, 208, 211, 214, 257, 260, 266, 309,
      323, 361, 378, 413, 416, 426, 432, 439, 616, 619, 625, 629, 632, 635, 639, 645, 822, 832,
      835, 838, 842, 852, 856, 1022, 1025, 1028, 1031, 1035, 1041, 1048, 1051, 1055, 1059, 1063,
      1067, 1225, 1228, 1234, 1238, 1244, 1251, 1254, 1258, 1262, 1266, 1270, 1428, 1431, 1441,
      1447, 1451, 1454, 1631, 1634, 1637, 1640, 1644, 1650, 1657, 1660, 1834, 1837, 1847, 1853,
      1857, 1860, 1867, 1871, 2037, 2040, 2043, 2050, 2056, 2063, 2070, 2240, 2243, 2249, 2253,
      2259, 2266, 2269, 2273, 2277, 2281, 2285, 2443, 2446, 2452, 2456, 2462, 2466, 2469, 2472,
      2476, 2480, 2484, 2488, 2646, 2649, 2652, 2655, 2662, 2665, 2675, 2679, 2683, 2687, 2691,
      2849, 2852, 2855, 2858, 2862, 2865, 2868, 2878, 2882, 2886, 2890, 2894, 3052, 3055, 3061,
      3065, 3071, 3078, 3081, 3085, 3089, 3093, 3097, 3255, 3258, 3309, 3316, 3322, 3458, 3461,
      3464, 3467, 3512, 3519, 3525, 3661, 3664, 3667, 3732, 3864, 3867, 3870, 3873, 3918, 3925,
      3931, 3935, 4067, 4070, 4076, 4121, 4128, 4138, 4269, 4284, 4316, 4382, 4399, 4432, 4438,
      4584, 4599, 4631
    ] := by decide!

/-- `21` equations satisfied by `Magma.exactS3wr6 2`, and by no earlier member of the cover. -/
theorem exactS3wr6_satisfies_1 :
    Satisfies (Magma.exactS3wr6 2) [
      58, 422, 442, 446, 450, 454, 458, 649, 653, 657, 661, 828, 848, 860, 864, 1437, 1668, 1875,
      3264, 3529, 3728
    ] := by decide!
