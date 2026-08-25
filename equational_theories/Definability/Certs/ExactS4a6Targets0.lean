import equational_theories.Definability.ExactAut6S4a6

/-!
# Structural certificate targets: `Magma.exactS4a6` (part 1 of 1)

Equations with no model among the `8` magmas on `Fin 6` whose automorphism group is exactly the
order-`24` group of `Magma.permES4a6`. `210` of them are worth listing, of which `210` appear here;
each is a valid *target* `L` of a `Magma.exactS4a6` certificate, and so is not structural from any
of the `186` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactAut6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `8` magmas on `Fin 6` whose automorphism group is exactly the order-`24` group of
`Magma.permES4a6` satisfies any of these `210` equations. -/
theorem exactS4a6_refutes_0 :
    FamilyRefutes Magma.exactS4a6 [
      10, 25, 49, 52, 101, 104, 107, 110, 159, 205, 208, 211, 214, 257, 260, 309, 323, 325, 333,
      361, 377, 378, 385, 413, 416, 426, 429, 432, 439, 616, 619, 622, 629, 632, 639, 819, 822,
      825, 832, 835, 838, 842, 848, 1022, 1025, 1028, 1031, 1035, 1041, 1048, 1051, 1055, 1059,
      1063, 1067, 1225, 1228, 1234, 1238, 1244, 1248, 1251, 1254, 1258, 1262, 1266, 1270, 1428,
      1431, 1441, 1451, 1454, 1631, 1634, 1637, 1644, 1650, 1657, 1834, 1837, 1847, 1853, 1857,
      1860, 2037, 2040, 2043, 2050, 2063, 2240, 2243, 2246, 2249, 2253, 2259, 2266, 2269, 2273,
      2277, 2281, 2285, 2443, 2446, 2452, 2456, 2462, 2466, 2469, 2472, 2476, 2480, 2484, 2488,
      2646, 2649, 2652, 2659, 2662, 2665, 2669, 2687, 2849, 2852, 2855, 2862, 2865, 2872, 3052,
      3055, 3065, 3068, 3071, 3078, 3255, 3258, 3264, 3309, 3315, 3316, 3318, 3322, 3343, 3346,
      3458, 3461, 3464, 3467, 3509, 3512, 3519, 3521, 3525, 3529, 3546, 3661, 3664, 3667, 3712,
      3714, 3721, 3725, 3752, 3759, 3864, 3867, 3870, 3873, 3918, 3925, 3927, 3928, 3931, 3935,
      3952, 4067, 4070, 4076, 4120, 4121, 4128, 4130, 4138, 4155, 4165, 4269, 4284, 4291, 4314,
      4316, 4320, 4358, 4382, 4396, 4399, 4406, 4432, 4433, 4436, 4438, 4445, 4472, 4473, 4480,
      4584, 4598, 4599, 4606, 4629, 4631, 4677
    ] := by nativeDecideFin!
