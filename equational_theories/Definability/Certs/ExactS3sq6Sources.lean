import equational_theories.Definability.ExactAut6S3sq6

/-!
# Structural certificate sources: `Magma.exactS3sq6`

For each of the following magmas, drawn from the `30` magmas on `Fin 6` whose automorphism group is
exactly the order-`36` group of `Magma.permES3sq6`, the equations it satisfies that no earlier
listed magma does. Together they are the `490` equations that are worth using as the *source* `L'`
of a `Magma.exactS3sq6` certificate -- the rest have such a model too, but the resulting facts are
already implied by what is on the board. `7` members cover them.

This file is generated; see the module docstring of `Definability.ExactAut6`.
-/

set_option maxHeartbeats 1000000
-- each `rfl` below reads one entry out of `Magma.memArrS3sq6`, and reading entry `k` recurses `k`
-- deep into the list behind the array
set_option maxRecDepth 100000

/-- `273` equations satisfied by `Magma.exactS3sq6 3`, and by no earlier member of the cover. -/
theorem exactS3sq6_satisfies_0 :
    Satisfies (Magma.exactS3sq6 3) [
      10, 25, 47, 49, 52, 55, 99, 101, 104, 107, 110, 151, 153, 156, 159, 205, 208, 211, 214,
      255, 257, 260, 263, 266, 307, 309, 323, 326, 359, 361, 375, 378, 411, 413, 416, 419, 426,
      429, 432, 436, 439, 614, 616, 619, 622, 625, 629, 632, 635, 639, 642, 645, 817, 819, 822,
      825, 832, 835, 838, 842, 845, 852, 856, 1020, 1022, 1025, 1028, 1031, 1035, 1038, 1041,
      1045, 1048, 1051, 1055, 1059, 1063, 1067, 1223, 1225, 1228, 1231, 1234, 1238, 1241, 1244,
      1248, 1251, 1254, 1258, 1262, 1266, 1270, 1426, 1428, 1431, 1434, 1441, 1444, 1447, 1451,
      1454, 1629, 1631, 1634, 1637, 1640, 1644, 1647, 1650, 1654, 1657, 1660, 1832, 1834, 1837,
      1840, 1847, 1850, 1853, 1857, 1860, 1867, 1871, 2035, 2037, 2040, 2043, 2050, 2053, 2056,
      2060, 2063, 2070, 2238, 2240, 2243, 2246, 2249, 2253, 2256, 2259, 2263, 2266, 2269, 2273,
      2277, 2281, 2285, 2441, 2443, 2446, 2449, 2452, 2456, 2459, 2462, 2466, 2469, 2472, 2476,
      2480, 2484, 2488, 2644, 2646, 2649, 2652, 2655, 2659, 2662, 2665, 2669, 2672, 2675, 2679,
      2683, 2687, 2691, 2847, 2849, 2852, 2855, 2858, 2862, 2865, 2868, 2872, 2875, 2878, 2882,
      2886, 2890, 2894, 3050, 3052, 3055, 3058, 3061, 3065, 3068, 3071, 3075, 3078, 3081, 3085,
      3089, 3093, 3097, 3253, 3255, 3258, 3261, 3306, 3309, 3316, 3319, 3322, 3456, 3458, 3461,
      3464, 3467, 3509, 3512, 3519, 3522, 3525, 3659, 3661, 3664, 3667, 3712, 3715, 3722, 3725,
      3732, 3862, 3864, 3867, 3870, 3873, 3915, 3918, 3925, 3928, 3931, 3935, 4065, 4067, 4070,
      4073, 4076, 4118, 4121, 4128, 4131, 4138, 4269, 4284, 4316, 4380, 4382, 4396, 4399, 4432,
      4435, 4438, 4470, 4473, 4584, 4599, 4631
    ] := by decide!

/-- `72` equations satisfied by `Magma.exactS3sq6 4`, and by no earlier member of the cover. -/
theorem exactS3sq6_satisfies_1 :
    Satisfies (Magma.exactS3sq6 4) [
      26, 53, 102, 105, 160, 212, 258, 362, 417, 430, 617, 620, 630, 826, 836, 843, 1029, 1036,
      1226, 1249, 1432, 1442, 1455, 1632, 1635, 1658, 1662, 1838, 1848, 1861, 1873, 2044, 2051,
      2241, 2244, 2267, 2447, 2457, 2470, 2485, 2653, 2663, 2670, 2850, 2853, 2863, 3053, 3066,
      3079, 3083, 3094, 3259, 3308, 3459, 3462, 3511, 3518, 3526, 3668, 3724, 3871, 3917, 3924,
      4068, 4127, 4135, 4146, 4283, 4383, 4398, 4585, 4656
    ] := by decide!

/-- `72` equations satisfied by `Magma.exactS3sq6 16`, and by no earlier member of the cover. -/
theorem exactS3sq6_satisfies_2 :
    Satisfies (Magma.exactS3sq6 16) [
      16, 72, 127, 179, 221, 228, 273, 315, 466, 500, 513, 528, 575, 669, 676, 703, 882, 909,
      916, 1075, 1082, 1122, 1184, 1285, 1312, 1325, 1481, 1525, 1684, 1691, 1731, 1780, 1894,
      1921, 1934, 1949, 2090, 2097, 2137, 2303, 2327, 2496, 2540, 2709, 2736, 2743, 2902, 2909,
      2936, 3112, 3142, 3278, 3334, 3353, 3414, 3484, 3549, 3556, 3687, 3749, 3880, 3887, 3955,
      3962, 4023, 4083, 4158, 4275, 4307, 4409, 4442, 4635
    ] := by decide!

/-- `21` equations satisfied by `Magma.exactS3sq6 5`, and by no earlier member of the cover. -/
theorem exactS3sq6_satisfies_3 :
    Satisfies (Magma.exactS3sq6 5) [
      58, 422, 442, 446, 450, 454, 458, 649, 653, 657, 661, 828, 848, 860, 864, 1437, 1668, 1875,
      3264, 3529, 3728
    ] := by decide!

/-- `19` equations satisfied by `Magma.exactS3sq6 22`, and by no earlier member of the cover. -/
theorem exactS3sq6_satisfies_4 :
    Satisfies (Magma.exactS3sq6 22) [
      43, 332, 387, 3342, 3355, 3545, 3751, 3758, 3964, 4154, 4167, 4343, 4358, 4405, 4482, 4531,
      4544, 4608, 4677
    ] := by decide!

/-- `17` equations satisfied by `Magma.exactS3sq6 0`, and by no earlier member of the cover. -/
theorem exactS3sq6_satisfies_5 :
    Satisfies (Magma.exactS3sq6 0) [
      325, 377, 3315, 3318, 3521, 3714, 3721, 3927, 4120, 4130, 4314, 4433, 4436, 4472, 4512,
      4598, 4629
    ] := by decide!

/-- `16` equations satisfied by `Magma.exactS3sq6 11`, and by no earlier member of the cover. -/
theorem exactS3sq6_satisfies_6 :
    Satisfies (Magma.exactS3sq6 11) [
      333, 385, 3343, 3346, 3546, 3752, 3759, 3952, 4155, 4165, 4291, 4320, 4406, 4445, 4480, 4606
    ] := by decide!
