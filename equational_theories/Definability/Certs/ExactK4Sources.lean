import equational_theories.Definability.ExactAut4K4

/-!
# Structural certificate sources: `Magma.exactK4`

For each of the following magmas, drawn from the `210` magmas on `Fin 4` whose automorphism group is
exactly the order-`4` group of `Magma.permEK4`, the equations it satisfies that no earlier listed
magma does. Together they are the `657` equations that are worth using as the *source* `L'` of a
`Magma.exactK4` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `9` members cover them.

This file is generated; see the module docstring of `Definability.ExactAut4`.
-/

set_option maxHeartbeats 1000000
-- each `rfl` below reads one entry out of `Magma.memArrK4`, and reading entry `k` recurses `k`
-- deep into the list behind the array
set_option maxRecDepth 100000

/-- `331` equations satisfied by `Magma.exactK4 6`, and by no earlier member of the cover. -/
theorem exactK4_satisfies_0 :
    Satisfies (Magma.exactK4 6) [
      10, 23, 25, 47, 49, 52, 55, 58, 153, 156, 159, 162, 203, 205, 208, 211, 214, 255, 257, 260,
      263, 266, 307, 309, 323, 326, 329, 359, 361, 375, 378, 381, 411, 413, 416, 419, 422, 426,
      429, 432, 436, 439, 442, 446, 450, 454, 458, 614, 616, 619, 622, 625, 629, 632, 635, 639,
      642, 645, 649, 653, 657, 661, 817, 819, 822, 825, 828, 832, 835, 838, 842, 845, 848, 852,
      856, 860, 864, 1020, 1022, 1025, 1028, 1031, 1035, 1038, 1041, 1045, 1048, 1051, 1055,
      1059, 1063, 1067, 1223, 1225, 1228, 1231, 1234, 1238, 1241, 1244, 1248, 1251, 1254, 1258,
      1262, 1266, 1270, 1426, 1428, 1431, 1434, 1437, 1441, 1444, 1447, 1451, 1454, 1457, 1461,
      1465, 1469, 1473, 1629, 1631, 1634, 1637, 1640, 1644, 1647, 1650, 1654, 1657, 1660, 1664,
      1668, 1672, 1676, 1832, 1834, 1837, 1840, 1843, 1847, 1850, 1853, 1857, 1860, 1863, 1867,
      1871, 1875, 1879, 2035, 2037, 2040, 2043, 2046, 2050, 2053, 2056, 2060, 2063, 2066, 2070,
      2074, 2078, 2082, 2238, 2240, 2243, 2246, 2249, 2253, 2256, 2259, 2263, 2266, 2269, 2273,
      2277, 2281, 2285, 2441, 2443, 2446, 2449, 2452, 2456, 2459, 2462, 2466, 2469, 2472, 2476,
      2480, 2484, 2488, 2644, 2646, 2649, 2652, 2655, 2659, 2662, 2665, 2669, 2672, 2675, 2679,
      2683, 2687, 2691, 2847, 2849, 2852, 2855, 2858, 2862, 2865, 2868, 2872, 2875, 2878, 2882,
      2886, 2890, 2894, 3050, 3052, 3055, 3058, 3061, 3065, 3068, 3071, 3075, 3078, 3081, 3085,
      3089, 3093, 3097, 3253, 3255, 3258, 3261, 3264, 3306, 3309, 3312, 3316, 3319, 3322, 3326,
      3330, 3334, 3338, 3456, 3458, 3461, 3464, 3467, 3509, 3512, 3515, 3519, 3522, 3525, 3529,
      3533, 3537, 3541, 3659, 3661, 3664, 3667, 3670, 3712, 3715, 3718, 3722, 3725, 3728, 3732,
      3736, 3740, 3744, 3862, 3864, 3867, 3870, 3873, 3915, 3918, 3921, 3925, 3928, 3931, 3935,
      3939, 3943, 3947, 4065, 4067, 4070, 4073, 4076, 4118, 4121, 4124, 4128, 4131, 4134, 4138,
      4142, 4146, 4150, 4269, 4284, 4380, 4402, 4438, 4476, 4508, 4512, 4516, 4520, 4584, 4599,
      4602, 4631
    ] := by decide!

/-- `103` equations satisfied by `Magma.exactK4 0`, and by no earlier member of the cover. -/
theorem exactK4_satisfies_1 :
    Satisfies (Magma.exactK4 0) [
      9, 48, 50, 51, 103, 105, 308, 377, 412, 414, 415, 417, 418, 420, 421, 423, 424, 425, 427,
      428, 615, 617, 618, 620, 621, 623, 624, 626, 627, 628, 818, 820, 821, 823, 824, 826, 827,
      829, 830, 831, 836, 837, 1021, 1023, 1024, 1026, 1027, 1029, 1030, 1032, 1033, 1034, 1036,
      1224, 1226, 1227, 1229, 1230, 1232, 1233, 1235, 1236, 1237, 1239, 1242, 1249, 1259, 1427,
      1429, 1430, 1630, 1632, 1633, 1635, 1655, 1833, 1838, 1839, 1848, 1849, 2036, 3254, 3256,
      3257, 3318, 3320, 3457, 3459, 3460, 3462, 3660, 3721, 3723, 3927, 4120, 4127, 4130, 4268,
      4282, 4283, 4286, 4598, 4629
    ] := by decide!

/-- `103` equations satisfied by `Magma.exactK4 14`, and by no earlier member of the cover. -/
theorem exactK4_satisfies_2 :
    Satisfies (Magma.exactK4 14) [
      28, 166, 218, 221, 228, 238, 270, 280, 290, 333, 364, 1478, 1681, 1684, 1687, 1691, 1701,
      1884, 1894, 1897, 1921, 1958, 2087, 2124, 2161, 2290, 2293, 2300, 2303, 2310, 2314, 2327,
      2330, 2337, 2347, 2364, 2381, 2398, 2415, 2493, 2496, 2503, 2513, 2530, 2540, 2550, 2567,
      2584, 2601, 2618, 2696, 2706, 2716, 2733, 2736, 2743, 2753, 2770, 2778, 2787, 2804, 2821,
      2899, 2909, 2919, 2936, 2946, 2956, 2973, 2990, 3007, 3024, 3102, 3105, 3108, 3112, 3122,
      3139, 3149, 3159, 3176, 3193, 3210, 3227, 3343, 3346, 3353, 3546, 3674, 3759, 3803, 3877,
      3880, 3887, 3897, 4080, 4090, 4100, 4155, 4192, 4587, 4635, 4642
    ] := by decide!

/-- `41` equations satisfied by `Magma.exactK4 78`, and by no earlier member of the cover. -/
theorem exactK4_satisfies_3 :
    Satisfies (Magma.exactK4 78) [
      117, 127, 138, 179, 194, 466, 473, 500, 513, 528, 562, 575, 1278, 1288, 1299, 1315, 1325,
      1336, 1353, 1370, 1387, 1405, 2100, 2115, 2137, 2152, 2182, 2203, 2227, 3952, 3962, 3972,
      3989, 4006, 4023, 4040, 4275, 4362, 4606, 4615, 4645
    ] := by decide!

/-- `37` equations satisfied by `Magma.exactK4 75`, and by no earlier member of the cover. -/
theorem exactK4_satisfies_4 :
    Satisfies (Magma.exactK4 75) [
      160, 161, 209, 212, 215, 1452, 1453, 1455, 1456, 1458, 1459, 1460, 2254, 2257, 2260, 2264,
      2267, 2270, 2274, 2278, 2282, 2286, 3053, 3056, 3066, 3079, 3083, 3091, 3094, 3518, 3520,
      3521, 3523, 3524, 3526, 3527, 4585
    ] := by decide!

/-- `28` equations satisfied by `Magma.exactK4 69`, and by no earlier member of the cover. -/
theorem exactK4_satisfies_5 :
    Satisfies (Magma.exactK4 69) [
      53, 66, 170, 177, 264, 273, 281, 1073, 1075, 1109, 1113, 1117, 1152, 1155, 2444, 2457,
      2494, 2534, 2538, 2573, 2576, 4273, 4332, 4369, 4588, 4605, 4647, 4684
    ] := by decide!

/-- `10` equations satisfied by `Magma.exactK4 79`, and by no earlier member of the cover. -/
theorem exactK4_satisfies_6 :
    Satisfies (Magma.exactK4 79) [
      1442, 1481, 1482, 2051, 2090, 2125, 3511, 3549, 3917, 3955
    ] := by decide!

/-- `2` equations satisfied by `Magma.exactK4 46`, and by no earlier member of the cover. -/
theorem exactK4_satisfies_7 :
    Satisfies (Magma.exactK4 46) [
      2093, 4083
    ] := by decide!

/-- `2` equations satisfied by `Magma.exactK4 58`, and by no earlier member of the cover. -/
theorem exactK4_satisfies_8 :
    Satisfies (Magma.exactK4 58) [
      1443, 3259
    ] := by decide!
