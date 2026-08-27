import equational_theories.Definability.ExactEnd6A

/-!
# Term-structural certificate targets: `Magma.end6A`

Equations with no model among the `4` magmas on `Fin 6` whose endomorphism monoid is exactly the
order-`36` monoid of `Magma.endE6A`. `221` of them are worth listing, of which `221` appear here;
each is a valid *target* `L` of a `Magma.end6A` certificate, and so is not term-structural from any
of the `37` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `4` magmas on `Fin 6` whose endomorphism monoid is exactly the order-`36` monoid of
`Magma.endE6A` satisfies any of these `221` equations. -/
theorem end6A_refutes_0 :
    FamilyRefutes Magma.end6A [
      8, 10, 16, 23, 25, 26, 99, 100, 101, 104, 107, 110, 203, 205, 208, 211, 214, 218, 411, 413,
      416, 417, 419, 426, 427, 429, 430, 432, 436, 439, 466, 500, 513, 528, 575, 617, 620, 630,
      818, 820, 821, 823, 833, 836, 843, 1020, 1022, 1023, 1025, 1028, 1029, 1031, 1035, 1036,
      1038, 1041, 1045, 1048, 1051, 1055, 1059, 1063, 1067, 1075, 1082, 1122, 1184, 1223, 1224,
      1225, 1226, 1228, 1229, 1230, 1231, 1234, 1238, 1241, 1244, 1248, 1249, 1251, 1254, 1258,
      1262, 1266, 1270, 1312, 1325, 1427, 1432, 1442, 1455, 1629, 1630, 1631, 1632, 1635, 1644,
      1647, 1650, 1654, 1658, 1662, 1681, 1684, 1691, 1731, 1780, 1832, 1833, 1834, 1838, 1840,
      1847, 1848, 1850, 1853, 1861, 1873, 1884, 1894, 1921, 1934, 1949, 2087, 2090, 2097, 2137,
      2238, 2240, 2241, 2243, 2246, 2249, 2253, 2256, 2259, 2263, 2266, 2267, 2269, 2273, 2277,
      2281, 2285, 2290, 2300, 2303, 2310, 2327, 2441, 2443, 2446, 2447, 2449, 2452, 2456, 2457,
      2459, 2462, 2466, 2469, 2470, 2472, 2476, 2480, 2484, 2485, 2488, 2496, 2530, 2540, 2696,
      2699, 2706, 2709, 2733, 2736, 2770, 2902, 2909, 2936, 3050, 3052, 3053, 3055, 3058, 3065,
      3066, 3068, 3071, 3075, 3078, 3079, 3083, 3094, 3105, 3112, 3278, 3353, 3414, 3484, 3549,
      3556, 3871, 3917, 3924, 4068, 4127, 4135, 4380, 4382, 4383, 4385, 4395, 4398, 4409, 4432,
      4435, 4442
    ] := by nativeDecideFin!
