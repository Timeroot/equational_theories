import equational_theories.Definability.ExactAut7F207

/-!
# Structural certificate targets: `Magma.exactF207` (part 1 of 1)

Equations with no model among the `72` magmas on `Fin 7` whose automorphism group is exactly the
order-`20` group of `Magma.permEF207`. `126` of them are worth listing, of which `126` appear here;
each is a valid *target* `L` of a `Magma.exactF207` certificate, and so is not structural from any
of the `274` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactAut7`.
-/

set_option maxHeartbeats 1000000

/-- None of the `72` magmas on `Fin 7` whose automorphism group is exactly the order-`20` group of
`Magma.permEF207` satisfies any of these `126` equations. -/
theorem exactF207_refutes_0 :
    FamilyRefutes Magma.exactF207 [
      16, 26, 55, 159, 263, 315, 362, 430, 436, 439, 442, 466, 500, 513, 528, 575, 630, 632, 635,
      639, 642, 645, 703, 716, 843, 845, 848, 856, 919, 1075, 1122, 1184, 1278, 1325, 1387, 1434,
      1442, 1444, 1451, 1454, 1455, 1459, 1481, 1528, 1657, 1658, 1662, 1721, 1731, 1780, 1851,
      1860, 1861, 1873, 1934, 1949, 2043, 2051, 2053, 2060, 2063, 2064, 2090, 2137, 2152, 2254,
      2267, 2282, 2457, 2470, 2485, 2672, 2673, 2683, 2687, 2709, 2850, 2855, 2865, 2868, 2875,
      2876, 2890, 2902, 3053, 3058, 3066, 3078, 3079, 3083, 3093, 3094, 3142, 3259, 3261, 3264,
      3278, 3281, 3323, 3334, 3414, 3474, 3484, 3526, 3667, 3668, 3687, 3868, 3871, 4023, 4068,
      4073, 4074, 4076, 4083, 4135, 4146, 4226, 4275, 4307, 4362, 4383, 4409, 4585, 4656, 4673
    ] := by nativeDecideFin!
