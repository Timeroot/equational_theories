import equational_theories.Definability.ExactAut5C55

/-!
# Structural certificate targets: `Magma.exactC55` (part 1 of 1)

Equations with no model among the `3100` magmas on `Fin 5` whose automorphism group is exactly the
order-`5` group of `Magma.permEC55`. `190` of them are worth listing, of which `190` appear here;
each is a valid *target* `L` of a `Magma.exactC55` certificate, and so is not structural from any of
the `400` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactAut5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `3100` magmas on `Fin 5` whose automorphism group is exactly the order-`5` group of
`Magma.permEC55` satisfies any of these `190` equations. -/
theorem exactC55_refutes_0 :
    FamilyRefutes Magma.exactC55 [
      58, 63, 65, 73, 118, 124, 125, 206, 222, 229, 261, 266, 271, 274, 442, 446, 450, 454, 458,
      633, 640, 649, 657, 661, 669, 731, 848, 860, 864, 870, 906, 981, 1119, 1387, 1432, 1435,
      1437, 1448, 1454, 1457, 1459, 1461, 1489, 1491, 1515, 1516, 1518, 1543, 1638, 1648, 1660,
      1668, 1672, 1685, 1692, 1697, 1718, 1724, 1728, 1746, 1835, 1841, 1855, 1863, 1865, 1869,
      1871, 1875, 1895, 1922, 1924, 1931, 2038, 2054, 2061, 2063, 2068, 2070, 2091, 2097, 2098,
      2134, 2152, 2165, 2282, 2450, 2647, 2675, 2687, 2688, 2691, 2697, 2858, 2863, 2878, 2880,
      2894, 2912, 2939, 3061, 3081, 3089, 3093, 3097, 3268, 3269, 3271, 3274, 3279, 3284, 3288,
      3292, 3296, 3300, 3349, 3356, 3359, 3363, 3367, 3371, 3375, 3380, 3384, 3388, 3392, 3397,
      3401, 3405, 3409, 3418, 3422, 3426, 3431, 3436, 3441, 3446, 3451, 3475, 3481, 3495, 3566,
      3669, 3702, 3716, 3728, 3732, 3790, 3865, 3874, 3888, 3930, 4066, 4069, 4071, 4072, 4075,
      4077, 4078, 4079, 4081, 4084, 4117, 4119, 4122, 4123, 4125, 4126, 4129, 4132, 4133, 4136,
      4137, 4139, 4140, 4141, 4143, 4144, 4145, 4147, 4148, 4149, 4151, 4152, 4153, 4403, 4420,
      4456, 4490, 4507, 4510
    ] := by nativeDecideFin!
