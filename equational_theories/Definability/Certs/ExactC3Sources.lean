import equational_theories.Definability.ExactAut4C3

/-!
# Structural certificate sources: `Magma.exactC3`

For each of the following magmas, drawn from the `990` magmas on `Fin 4` whose automorphism group is
exactly the order-`3` group of `Magma.permEC3`, the equations it satisfies that no earlier listed
magma does. Together they are the `713` equations that are worth using as the *source* `L'` of a
`Magma.exactC3` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `32` members cover them.

This file is generated; see the module docstring of `Definability.ExactAut4`.
-/

set_option maxHeartbeats 1000000
-- each `rfl` below reads one entry out of `Magma.memArrC3`, and reading entry `k` recurses `k`
-- deep into the list behind the array
set_option maxRecDepth 100000

/-- `223` equations satisfied by `Magma.exactC3 0`, and by no earlier member of the cover. -/
theorem exactC3_satisfies_0 :
    Satisfies (Magma.exactC3 0) [
      40, 312, 313, 315, 316, 317, 319, 320, 360, 365, 368, 369, 371, 3268, 3269, 3270, 3271,
      3273, 3274, 3276, 3279, 3280, 3281, 3282, 3283, 3284, 3285, 3286, 3287, 3288, 3290, 3292,
      3293, 3294, 3295, 3296, 3297, 3298, 3299, 3302, 3303, 3471, 3473, 3474, 3475, 3476, 3477,
      3478, 3481, 3482, 3483, 3485, 3486, 3487, 3488, 3489, 3490, 3492, 3493, 3495, 3496, 3497,
      3498, 3499, 3500, 3501, 3502, 3504, 3505, 3661, 3662, 3663, 3664, 3665, 3666, 3667, 3668,
      3670, 3671, 3672, 3675, 3677, 3678, 3679, 3680, 3681, 3682, 3684, 3685, 3686, 3687, 3688,
      3689, 3690, 3691, 3692, 3693, 3694, 3695, 3696, 3698, 3699, 3700, 3701, 3703, 3704, 3707,
      3708, 3709, 3863, 3865, 3866, 3868, 3869, 3872, 3875, 3879, 3881, 3882, 3884, 3885, 3888,
      3889, 3891, 3892, 3894, 3895, 3896, 3898, 3902, 3903, 3904, 3906, 3907, 3908, 3910, 3912,
      4066, 4069, 4071, 4072, 4081, 4084, 4085, 4087, 4092, 4094, 4095, 4097, 4098, 4099, 4101,
      4105, 4106, 4107, 4109, 4113, 4276, 4277, 4279, 4280, 4294, 4297, 4299, 4301, 4305, 4308,
      4311, 4312, 4324, 4325, 4331, 4336, 4337, 4346, 4355, 4381, 4388, 4389, 4390, 4392, 4397,
      4410, 4412, 4417, 4421, 4423, 4424, 4425, 4426, 4429, 4434, 4447, 4449, 4454, 4460, 4461,
      4462, 4463, 4466, 4469, 4471, 4475, 4483, 4484, 4486, 4491, 4495, 4497, 4498, 4499, 4500,
      4503, 4591, 4592, 4594, 4609, 4616, 4620, 4623, 4626, 4639, 4651
    ] := by decide!

/-- `101` equations satisfied by `Magma.exactC3 154`, and by no earlier member of the cover. -/
theorem exactC3_satisfies_1 :
    Satisfies (Magma.exactC3 154) [
      256, 259, 261, 262, 265, 267, 268, 269, 2039, 2042, 2045, 2047, 2048, 2049, 2054, 2055,
      2057, 2058, 2059, 2061, 2062, 2065, 2067, 2069, 2071, 2072, 2073, 2075, 2076, 2077, 2079,
      2080, 2081, 2083, 2084, 2085, 2086, 2645, 2648, 2650, 2651, 2654, 2656, 2657, 2658, 2661,
      2664, 2666, 2667, 2668, 2670, 2671, 2674, 2676, 2677, 2678, 2680, 2681, 2682, 2684, 2685,
      2686, 2689, 2690, 2692, 2693, 2694, 2695, 2848, 2851, 2854, 2856, 2857, 2859, 2860, 2861,
      2863, 2864, 2866, 2867, 2869, 2870, 2871, 2873, 2874, 2877, 2879, 2881, 2883, 2884, 2885,
      2887, 2888, 2889, 2891, 2892, 2893, 2895, 2896, 2897, 2898
    ] := by decide!

/-- `101` equations satisfied by `Magma.exactC3 525`, and by no earlier member of the cover. -/
theorem exactC3_satisfies_2 :
    Satisfies (Magma.exactC3 525) [
      62, 65, 68, 78, 82, 86, 90, 94, 666, 669, 672, 679, 682, 686, 690, 694, 698, 706, 709, 713,
      719, 723, 727, 735, 740, 744, 748, 752, 757, 761, 765, 769, 774, 778, 782, 786, 791, 796,
      801, 806, 811, 869, 875, 879, 882, 885, 889, 893, 897, 901, 912, 922, 926, 930, 934, 938,
      943, 947, 951, 955, 960, 964, 968, 972, 977, 985, 989, 994, 999, 1004, 1009, 1014, 1491,
      1494, 1498, 1502, 1506, 1510, 1518, 1521, 1531, 1535, 1539, 1547, 1552, 1556, 1560, 1564,
      1569, 1573, 1577, 1581, 1586, 1590, 1594, 1598, 1603, 1608, 1613, 1618, 1623
    ] := by decide!

/-- `48` equations satisfied by `Magma.exactC3 242`, and by no earlier member of the cover. -/
theorem exactC3_satisfies_3 :
    Satisfies (Magma.exactC3 242) [
      31, 221, 231, 242, 246, 1718, 1746, 2293, 2314, 2318, 2330, 2340, 2351, 2355, 2364, 2368,
      2372, 2385, 2389, 2402, 2406, 2420, 2425, 2430, 2506, 2517, 2543, 2554, 2558, 2571, 2588,
      2605, 2623, 2724, 2746, 2761, 2791, 2795, 2812, 2836, 3115, 3152, 3167, 3275, 3289, 3301,
      3786, 3820
    ] := by decide!

/-- `46` equations satisfied by `Magma.exactC3 56`, and by no earlier member of the cover. -/
theorem exactC3_satisfies_4 :
    Satisfies (Magma.exactC3 56) [
      11, 105, 108, 109, 111, 437, 440, 444, 844, 846, 847, 849, 850, 851, 858, 1042, 1046, 1049,
      1052, 1053, 1056, 1060, 1064, 1068, 1227, 1239, 1242, 1243, 1245, 1250, 1252, 1253, 1255,
      1256, 1257, 1259, 1263, 1264, 1265, 1267, 1271, 1835, 1857, 1865, 3726, 3729
    ] := by decide!

/-- `37` equations satisfied by `Magma.exactC3 2`, and by no earlier member of the cover. -/
theorem exactC3_satisfies_5 :
    Satisfies (Magma.exactC3 2) [
      372, 3479, 3491, 3506, 3874, 3899, 3911, 4074, 4075, 4077, 4078, 4082, 4088, 4102, 4110,
      4111, 4114, 4115, 4393, 4440, 4450, 4457, 4467, 4477, 4487, 4489, 4494, 4504, 4595, 4612,
      4614, 4627, 4640, 4646, 4652, 4661, 4670
    ] := by decide!

/-- `21` equations satisfied by `Magma.exactC3 133`, and by no earlier member of the cover. -/
theorem exactC3_satisfies_6 :
    Satisfies (Magma.exactC3 133) [
      103, 824, 827, 830, 831, 1027, 1030, 1033, 1034, 1233, 1235, 1236, 1237, 1633, 3059, 3069,
      3076, 3716, 3930, 4507, 4510
    ] := by decide!

/-- `21` equations satisfied by `Magma.exactC3 507`, and by no earlier member of the cover. -/
theorem exactC3_satisfies_7 :
    Satisfies (Magma.exactC3 507) [
      238, 476, 503, 510, 1958, 2347, 2381, 2398, 2415, 2513, 2550, 2601, 2618, 2716, 2753, 2804,
      2821, 3566, 3790, 4456, 4490
    ] := by decide!

/-- `14` equations satisfied by `Magma.exactC3 301`, and by no earlier member of the cover. -/
theorem exactC3_satisfies_8 :
    Satisfies (Magma.exactC3 301) [
      643, 658, 861, 1523, 2132, 2808, 2949, 3011, 3350, 3573, 3756, 3823, 3979, 4229
    ] := by decide!

/-- `14` equations satisfied by `Magma.exactC3 600`, and by no earlier member of the cover. -/
theorem exactC3_satisfies_9 :
    Satisfies (Magma.exactC3 600) [
      56, 63, 1692, 1694, 1719, 1721, 1888, 1897, 1922, 1931, 2497, 2504, 3056, 3091
    ] := by decide!

/-- `11` equations satisfied by `Magma.exactC3 401`, and by no earlier member of the cover. -/
theorem exactC3_satisfies_10 :
    Satisfies (Magma.exactC3 401) [
      271, 283, 1083, 1110, 1638, 1655, 1685, 1851, 1858, 1895, 3388
    ] := by decide!

/-- `10` equations satisfied by `Magma.exactC3 371`, and by no earlier member of the cover. -/
theorem exactC3_satisfies_11 :
    Satisfies (Magma.exactC3 371) [
      117, 127, 159, 179, 1085, 1278, 1315, 1657, 1860, 2100
    ] := by decide!

/-- `8` equations satisfied by `Magma.exactC3 139`, and by no earlier member of the cover. -/
theorem exactC3_satisfies_12 :
    Satisfies (Magma.exactC3 139) [
      156, 1867, 3061, 3081, 3089, 3093, 3097, 3732
    ] := by decide!

/-- `7` equations satisfied by `Magma.exactC3 564`, and by no earlier member of the cover. -/
theorem exactC3_satisfies_13 :
    Satisfies (Magma.exactC3 564) [
      160, 209, 212, 1452, 2254, 2257, 2467
    ] := by decide!

/-- `6` equations satisfied by `Magma.exactC3 1`, and by no earlier member of the cover. -/
theorem exactC3_satisfies_14 :
    Satisfies (Magma.exactC3 1) [
      4369, 4403, 4413, 4420, 4430, 4684
    ] := by decide!

/-- `6` equations satisfied by `Magma.exactC3 501`, and by no earlier member of the cover. -/
theorem exactC3_satisfies_15 :
    Satisfies (Magma.exactC3 501) [
      153, 446, 450, 454, 458, 1640
    ] := by decide!

/-- `6` equations satisfied by `Magma.exactC3 615`, and by no earlier member of the cover. -/
theorem exactC3_satisfies_16 :
    Satisfies (Magma.exactC3 615) [
      73, 118, 125, 222, 229, 274
    ] := by decide!

/-- `5` equations satisfied by `Magma.exactC3 352`, and by no earlier member of the cover. -/
theorem exactC3_satisfies_17 :
    Satisfies (Magma.exactC3 352) [
      2592, 2964, 2998, 3201, 3214
    ] := by decide!

/-- `5` equations satisfied by `Magma.exactC3 372`, and by no earlier member of the cover. -/
theorem exactC3_satisfies_18 :
    Satisfies (Magma.exactC3 372) [
      167, 1482, 1682, 1885, 2125
    ] := by decide!

/-- `5` equations satisfied by `Magma.exactC3 544`, and by no earlier member of the cover. -/
theorem exactC3_satisfies_19 :
    Satisfies (Magma.exactC3 544) [
      452, 455, 647, 655, 1061
    ] := by decide!

/-- `2` equations satisfied by `Magma.exactC3 57`, and by no earlier member of the cover. -/
theorem exactC3_satisfies_20 :
    Satisfies (Magma.exactC3 57) [
      443, 1240
    ] := by decide!

/-- `2` equations satisfied by `Magma.exactC3 81`, and by no earlier member of the cover. -/
theorem exactC3_satisfies_21 :
    Satisfies (Magma.exactC3 81) [
      640, 1050
    ] := by decide!

/-- `2` equations satisfied by `Magma.exactC3 160`, and by no earlier member of the cover. -/
theorem exactC3_satisfies_22 :
    Satisfies (Magma.exactC3 160) [
      1435, 1641
    ] := by decide!

/-- `2` equations satisfied by `Magma.exactC3 241`, and by no earlier member of the cover. -/
theorem exactC3_satisfies_23 :
    Satisfies (Magma.exactC3 241) [
      2296, 3197
    ] := by decide!

/-- `2` equations satisfied by `Magma.exactC3 272`, and by no earlier member of the cover. -/
theorem exactC3_satisfies_24 :
    Satisfies (Magma.exactC3 272) [
      2609, 2912
    ] := by decide!

/-- `2` equations satisfied by `Magma.exactC3 528`, and by no earlier member of the cover. -/
theorem exactC3_satisfies_25 :
    Satisfies (Magma.exactC3 528) [
      1975, 2134
    ] := by decide!

/-- `1` equations satisfied by `Magma.exactC3 142`, and by no earlier member of the cover. -/
theorem exactC3_satisfies_26 :
    Satisfies (Magma.exactC3 142) [
      2244
    ] := by decide!

/-- `1` equations satisfied by `Magma.exactC3 357`, and by no earlier member of the cover. -/
theorem exactC3_satisfies_27 :
    Satisfies (Magma.exactC3 357) [
      53
    ] := by decide!

/-- `1` equations satisfied by `Magma.exactC3 404`, and by no earlier member of the cover. -/
theorem exactC3_satisfies_28 :
    Satisfies (Magma.exactC3 404) [
      501
    ] := by decide!

/-- `1` equations satisfied by `Magma.exactC3 510`, and by no earlier member of the cover. -/
theorem exactC3_satisfies_29 :
    Satisfies (Magma.exactC3 510) [
      1285
    ] := by decide!

/-- `1` equations satisfied by `Magma.exactC3 555`, and by no earlier member of the cover. -/
theorem exactC3_satisfies_30 :
    Satisfies (Magma.exactC3 555) [
      273
    ] := by decide!

/-- `1` equations satisfied by `Magma.exactC3 595`, and by no earlier member of the cover. -/
theorem exactC3_satisfies_31 :
    Satisfies (Magma.exactC3 595) [
      3106
    ] := by decide!
