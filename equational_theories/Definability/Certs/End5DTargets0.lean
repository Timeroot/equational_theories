import equational_theories.Definability.ExactEnd5D

/-!
# Term-structural certificate targets: `Magma.end5D`

Equations with no model among the `80` magmas on `Fin 5` whose endomorphism monoid is exactly the
order-`13` monoid of `Magma.endE5D`. `82` of them are worth listing, of which `82` appear here; each
is a valid *target* `L` of a `Magma.end5D` certificate, and so is not term-structural from any of
the `38` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `80` magmas on `Fin 5` whose endomorphism monoid is exactly the order-`13` monoid of
`Magma.endE5D` satisfies any of these `82` equations. -/
theorem end5D_refutes_0 :
    FamilyRefutes Magma.end5D [
      16, 26, 55, 72, 258, 263, 436, 466, 500, 528, 575, 632, 642, 703, 845, 909, 916, 1075,
      1122, 1184, 1230, 1233, 1235, 1236, 1278, 1325, 1434, 1454, 1455, 1525, 1658, 1662, 1731,
      1780, 1861, 1873, 1934, 1949, 2044, 2060, 2063, 2137, 2254, 2267, 2310, 2347, 2381, 2398,
      2457, 2470, 2485, 2653, 2663, 2672, 2850, 2865, 2875, 3053, 3058, 3066, 3083, 3094, 3261,
      3278, 3334, 3414, 3484, 3723, 3803, 3871, 4068, 4073, 4135, 4146, 4275, 4307, 4362, 4383,
      4409, 4585, 4656, 4673
    ] := by nativeDecideFin!
