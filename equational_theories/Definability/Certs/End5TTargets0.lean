import equational_theories.Definability.ExactEnd5T

/-!
# Term-structural certificate targets: `Magma.end5T`

Equations with no model among the `24` magmas on `Fin 5` whose endomorphism monoid is exactly the
order-`108` monoid of `Magma.endE5T`. `148` of them are worth listing, of which `148` appear here;
each is a valid *target* `L` of a `Magma.end5T` certificate, and so is not term-structural from any
of the `20` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `24` magmas on `Fin 5` whose endomorphism monoid is exactly the order-`108` monoid
of `Magma.endE5T` satisfies any of these `148` equations. -/
theorem end5T_refutes_0 :
    FamilyRefutes Magma.end5T [
      10, 16, 25, 26, 107, 110, 211, 214, 310, 367, 413, 419, 426, 429, 432, 436, 439, 442, 466,
      473, 500, 513, 528, 575, 1038, 1041, 1048, 1051, 1059, 1063, 1067, 1075, 1082, 1122, 1184,
      1241, 1244, 1251, 1254, 1262, 1266, 1270, 1278, 1312, 1325, 1387, 1432, 1451, 1455, 1459,
      1635, 1645, 1658, 1662, 1718, 1721, 1731, 1746, 1780, 1835, 1851, 1861, 1865, 1873, 1887,
      1894, 1934, 1949, 2043, 2097, 2137, 2152, 2241, 2254, 2256, 2259, 2266, 2267, 2269, 2277,
      2281, 2282, 2285, 2447, 2457, 2459, 2462, 2469, 2470, 2472, 2480, 2484, 2485, 2488, 3052,
      3053, 3056, 3058, 3065, 3066, 3068, 3071, 3075, 3078, 3079, 3083, 3093, 3094, 3266, 3268,
      3271, 3278, 3281, 3288, 3308, 3343, 3346, 3414, 3466, 3513, 3905, 3993, 4066, 4068, 4071,
      4074, 4120, 4130, 4135, 4158, 4270, 4272, 4275, 4283, 4286, 4291, 4307, 4320, 4362, 4583,
      4585, 4590, 4598, 4629, 4635, 4642, 4656, 4673
    ] := by nativeDecideFin!
