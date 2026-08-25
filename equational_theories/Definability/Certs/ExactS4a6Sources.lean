import equational_theories.Definability.ExactAut6S4a6

/-!
# Structural certificate sources: `Magma.exactS4a6`

For each of the following magmas, drawn from the `8` magmas on `Fin 6` whose automorphism group is
exactly the order-`24` group of `Magma.permES4a6`, the equations it satisfies that no earlier listed
magma does. Together they are the `186` equations that are worth using as the *source* `L'` of a
`Magma.exactS4a6` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactAut6`.
-/

set_option maxHeartbeats 1000000
-- each `rfl` below reads one entry out of `Magma.memArrS4a6`, and reading entry `k` recurses `k`
-- deep into the list behind the array
set_option maxRecDepth 100000

/-- `117` equations satisfied by `Magma.exactS4a6 0`, and by no earlier member of the cover. -/
theorem exactS4a6_satisfies_0 :
    Satisfies (Magma.exactS4a6 0) [
      1, 3, 26, 47, 53, 55, 102, 105, 151, 160, 203, 212, 255, 258, 263, 307, 326, 359, 362, 375,
      411, 417, 419, 430, 436, 617, 620, 630, 642, 826, 836, 843, 845, 1029, 1036, 1038, 1045,
      1223, 1226, 1231, 1241, 1249, 1426, 1432, 1434, 1442, 1444, 1455, 1629, 1632, 1635, 1647,
      1654, 1658, 1662, 1832, 1838, 1840, 1848, 1850, 1861, 1873, 2035, 2044, 2053, 2060, 2241,
      2244, 2256, 2263, 2267, 2447, 2449, 2457, 2459, 2470, 2485, 2653, 2663, 2670, 2672, 2850,
      2853, 2863, 2875, 3053, 3058, 3066, 3075, 3079, 3083, 3094, 3259, 3261, 3306, 3308, 3459,
      3462, 3518, 3526, 3668, 3724, 3871, 3917, 3924, 4068, 4073, 4127, 4131, 4135, 4146, 4283,
      4383, 4398, 4435, 4585, 4656
    ] := by decide!

/-- `69` equations satisfied by `Magma.exactS4a6 1`, and by no earlier member of the cover. -/
theorem exactS4a6_satisfies_1 :
    Satisfies (Magma.exactS4a6 1) [
      16, 72, 127, 179, 221, 228, 273, 315, 466, 500, 513, 528, 575, 669, 676, 703, 882, 909,
      916, 1075, 1082, 1122, 1184, 1285, 1312, 1325, 1481, 1525, 1684, 1691, 1731, 1780, 1894,
      1921, 1934, 1949, 2090, 2097, 2137, 2303, 2327, 2496, 2540, 2709, 2736, 2743, 2902, 2936,
      3142, 3278, 3334, 3353, 3414, 3484, 3549, 3556, 3687, 3749, 3880, 3887, 3962, 4023, 4083,
      4158, 4275, 4307, 4409, 4442, 4635
    ] := by decide!
