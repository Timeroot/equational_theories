import equational_theories.Definability.ExactEnd3T

/-!
# Term-structural certificate targets: `Magma.end3T`

Equations with no model among the `6` magmas on `Fin 3` whose endomorphism monoid is exactly the
order-`6` monoid of `Magma.endE3T`. `102` of them are worth listing, of which `102` appear here;
each is a valid *target* `L` of a `Magma.end3T` certificate, and so is not term-structural from any
of the `6` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `6` magmas on `Fin 3` whose endomorphism monoid is exactly the order-`6` monoid of
`Magma.endE3T` satisfies any of these `102` equations. -/
theorem end3T_refutes_0 :
    FamilyRefutes Magma.end3T [
      16, 26, 55, 65, 72, 258, 261, 263, 427, 436, 466, 500, 513, 528, 575, 632, 639, 642, 669,
      679, 703, 833, 845, 872, 879, 906, 909, 916, 1075, 1122, 1184, 1229, 1231, 1325, 1434,
      1444, 1454, 1455, 1491, 1518, 1525, 1647, 1654, 1658, 1662, 1731, 1780, 1840, 1850, 1861,
      1873, 1934, 1949, 2044, 2053, 2054, 2060, 2061, 2063, 2137, 2263, 2267, 2300, 2457, 2470,
      2485, 2647, 2650, 2653, 2660, 2663, 2672, 2699, 2850, 2855, 2863, 2865, 2873, 2875, 3053,
      3058, 3066, 3079, 3083, 3094, 3105, 3261, 3278, 3334, 3414, 3484, 3526, 3871, 4023, 4068,
      4073, 4275, 4362, 4383, 4409, 4585, 4673
    ] := by nativeDecideFin!
