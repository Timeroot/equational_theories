import equational_theories.Definability.ExactAut7G247

/-!
# Structural certificate targets: `Magma.exactG247` (part 1 of 1)

Equations with no model among the `768` magmas on `Fin 7` whose automorphism group is exactly the
order-`24` group of `Magma.permEG247`. `103` of them are worth listing, of which `103` appear here;
each is a valid *target* `L` of a `Magma.exactG247` certificate, and so is not structural from any
of the `245` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactAut7`.
-/

set_option maxHeartbeats 1000000

/-- None of the `768` magmas on `Fin 7` whose automorphism group is exactly the order-`24` group of
`Magma.permEG247` satisfies any of these `103` equations. -/
theorem exactG247_refutes_0 :
    FamilyRefutes Magma.exactG247 [
      16, 26, 72, 258, 427, 430, 466, 500, 513, 528, 575, 630, 703, 833, 834, 836, 839, 843, 879,
      909, 916, 1036, 1075, 1122, 1184, 1249, 1260, 1325, 1432, 1451, 1455, 1457, 1525, 1635,
      1658, 1662, 1684, 1731, 1780, 1848, 1861, 1873, 1894, 1934, 1949, 2043, 2044, 2078, 2097,
      2137, 2267, 2303, 2306, 2457, 2470, 2485, 2496, 2650, 2653, 2663, 2699, 2702, 2709, 2736,
      2774, 2850, 2902, 3053, 3066, 3079, 3083, 3094, 3105, 3142, 3259, 3278, 3308, 3334, 3414,
      3462, 3463, 3484, 3529, 3871, 3880, 3883, 3931, 4068, 4083, 4135, 4146, 4158, 4275, 4286,
      4307, 4358, 4383, 4399, 4409, 4585, 4642, 4656, 4677
    ] := by nativeDecideFin!
