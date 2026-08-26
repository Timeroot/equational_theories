import equational_theories.Definability.ExactEnd4E

/-!
# Term-structural certificate targets: `Magma.end4E`

Equations with no model among the `4` magmas on `Fin 4` whose endomorphism monoid is exactly the
order-`13` monoid of `Magma.endE4E`. `152` of them are worth listing, of which `152` appear here;
each is a valid *target* `L` of a `Magma.end4E` certificate, and so is not term-structural from any
of the `242` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd4`.
-/

set_option maxHeartbeats 1000000

/-- None of the `4` magmas on `Fin 4` whose endomorphism monoid is exactly the order-`13` monoid of
`Magma.endE4E` satisfies any of these `152` equations. -/
theorem end4E_refutes_0 :
    FamilyRefutes Magma.end4E [
      10, 25, 52, 55, 58, 107, 110, 211, 214, 257, 263, 266, 309, 323, 361, 378, 426, 429, 432,
      436, 629, 632, 635, 639, 642, 645, 649, 653, 657, 661, 669, 835, 838, 842, 845, 848, 852,
      856, 860, 864, 1038, 1041, 1048, 1051, 1059, 1063, 1067, 1241, 1244, 1251, 1254, 1262,
      1266, 1270, 1285, 1431, 1434, 1437, 1441, 1442, 1444, 1481, 1644, 1647, 1650, 1654, 1834,
      1840, 1850, 1853, 2037, 2040, 2051, 2053, 2060, 2070, 2090, 2244, 2256, 2259, 2266, 2269,
      2277, 2281, 2285, 2459, 2462, 2469, 2472, 2480, 2484, 2488, 2652, 2655, 2662, 2665, 2672,
      2675, 2683, 2687, 2691, 2849, 2855, 2858, 2863, 2865, 2868, 2875, 2878, 2886, 2890, 2894,
      3052, 3058, 3068, 3071, 3258, 3261, 3264, 3306, 3309, 3343, 3464, 3467, 3509, 3511, 3549,
      3870, 3873, 3917, 3928, 3955, 4067, 4073, 4076, 4121, 4130, 4131, 4269, 4283, 4284, 4291,
      4316, 4382, 4398, 4432, 4442, 4584, 4599, 4629, 4631, 4635
    ] := by nativeDecideFin!
