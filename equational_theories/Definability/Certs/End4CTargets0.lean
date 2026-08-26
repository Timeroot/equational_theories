import equational_theories.Definability.ExactEnd4C

/-!
# Term-structural certificate targets: `Magma.end4C`

Equations with no model among the `132` magmas on `Fin 4` whose endomorphism monoid is exactly the
order-`4` monoid of `Magma.endE4C`. `146` of them are worth listing, of which `146` appear here;
each is a valid *target* `L` of a `Magma.end4C` certificate, and so is not term-structural from any
of the `183` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd4`.
-/

set_option maxHeartbeats 1000000

/-- None of the `132` magmas on `Fin 4` whose endomorphism monoid is exactly the order-`4` monoid of
`Magma.endE4C` satisfies any of these `146` equations. -/
theorem end4C_refutes_0 :
    FamilyRefutes Magma.end4C [
      10, 25, 101, 107, 110, 208, 211, 214, 309, 323, 326, 329, 361, 375, 378, 381, 413, 416,
      417, 422, 426, 427, 432, 439, 442, 446, 450, 454, 458, 639, 817, 1028, 1031, 1041, 1048,
      1051, 1059, 1063, 1067, 1226, 1234, 1244, 1249, 1251, 1254, 1262, 1266, 1270, 1431, 1434,
      1437, 1441, 1443, 1444, 1447, 1461, 1465, 1469, 1473, 1635, 1655, 1684, 1687, 1848, 1849,
      1894, 1897, 2037, 2040, 2046, 2053, 2056, 2060, 2066, 2070, 2074, 2082, 2093, 2259, 2266,
      2269, 2273, 2277, 2281, 2285, 2303, 2327, 2462, 2466, 2469, 2472, 2476, 2480, 2484, 2488,
      2644, 2855, 3052, 3055, 3061, 3065, 3071, 3078, 3081, 3085, 3089, 3093, 3097, 3105, 3112,
      3318, 3320, 3343, 3346, 3464, 3467, 3509, 3512, 3515, 3529, 3533, 3537, 3541, 3659, 3870,
      3873, 3918, 3921, 3928, 3931, 3939, 3943, 3947, 4120, 4130, 4155, 4192, 4283, 4286, 4291,
      4380, 4435, 4470, 4629, 4635, 4642
    ] := by nativeDecideFin!
