import equational_theories.Definability.ExactAut4A4

/-!
# Structural certificate sources: `Magma.exactA4`

For each of the following magmas, drawn from the `2` magmas on `Fin 4` whose automorphism group is
exactly the order-`12` group of `Magma.permEA4`, the equations it satisfies that no earlier listed
magma does. Together they are the `236` equations that are worth using as the *source* `L'` of a
`Magma.exactA4` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `1` members cover them.

This file is generated; see the module docstring of `Definability.ExactAut4`.
-/

set_option maxHeartbeats 1000000
-- each `rfl` below reads one entry out of `Magma.memArrA4`, and reading entry `k` recurses `k`
-- deep into the list behind the array
set_option maxRecDepth 100000

/-- `236` equations satisfied by `Magma.exactA4 0`, and by no earlier member of the cover. -/
theorem exactA4_satisfies_0 :
    Satisfies (Magma.exactA4 0) [
      1, 3, 8, 14, 23, 29, 47, 53, 66, 75, 99, 105, 115, 124, 151, 159, 170, 177, 203, 206, 219,
      221, 255, 264, 273, 281, 307, 313, 326, 335, 359, 365, 375, 384, 411, 417, 430, 439, 466,
      477, 489, 501, 510, 614, 620, 630, 639, 669, 680, 692, 707, 716, 746, 778, 817, 825, 836,
      843, 873, 880, 906, 919, 934, 1020, 1023, 1036, 1038, 1073, 1075, 1109, 1113, 1117, 1152,
      1155, 1223, 1232, 1241, 1249, 1276, 1288, 1316, 1322, 1358, 1426, 1432, 1442, 1451, 1481,
      1492, 1504, 1519, 1528, 1558, 1590, 1629, 1635, 1648, 1657, 1684, 1695, 1707, 1719, 1728,
      1832, 1841, 1848, 1860, 1888, 1894, 1924, 1932, 1977, 2035, 2043, 2051, 2064, 2079, 2090,
      2097, 2128, 2135, 2167, 2180, 2238, 2247, 2256, 2264, 2291, 2303, 2331, 2337, 2373, 2441,
      2444, 2457, 2459, 2494, 2496, 2530, 2534, 2538, 2573, 2576, 2644, 2647, 2669, 2673, 2677,
      2707, 2709, 2734, 2736, 2847, 2855, 2863, 2876, 2891, 2902, 2909, 2940, 2947, 2979, 2992,
      3050, 3059, 3066, 3078, 3106, 3112, 3142, 3150, 3195, 3253, 3259, 3272, 3281, 3308, 3319,
      3331, 3343, 3352, 3456, 3462, 3472, 3481, 3511, 3522, 3534, 3549, 3558, 3588, 3620, 3659,
      3667, 3678, 3685, 3715, 3722, 3748, 3761, 3776, 3862, 3865, 3878, 3880, 3915, 3917, 3951,
      3955, 3959, 3994, 3997, 4065, 4074, 4083, 4091, 4118, 4130, 4158, 4164, 4200, 4273, 4290,
      4332, 4369, 4380, 4386, 4399, 4408, 4446, 4458, 4479, 4588, 4605, 4647, 4684
    ] := by decide!
