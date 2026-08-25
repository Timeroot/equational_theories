import equational_theories.Definability.ExactAut6S4b6

/-!
# Structural certificate targets: `Magma.exactS4b6` (part 1 of 1)

Equations with no model among the `8` magmas on `Fin 6` whose automorphism group is exactly the
order-`24` group of `Magma.permES4b6`. `57` of them are worth listing, of which `57` appear here;
each is a valid *target* `L` of a `Magma.exactS4b6` certificate, and so is not structural from any
of the `35` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactAut6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `8` magmas on `Fin 6` whose automorphism group is exactly the order-`24` group of
`Magma.permES4b6` satisfies any of these `57` equations. -/
theorem exactS4b6_refutes_0 :
    FamilyRefutes Magma.exactS4b6 [
      16, 26, 500, 528, 575, 703, 1082, 1122, 1184, 1444, 1647, 1658, 1662, 1691, 1731, 1780,
      1838, 1850, 1861, 1873, 1934, 1949, 2053, 2447, 2470, 2485, 2850, 3053, 3083, 3094, 3278,
      3306, 3334, 3353, 3414, 3484, 3518, 3526, 3556, 3871, 3924, 3962, 4023, 4068, 4127, 4131,
      4135, 4146, 4275, 4283, 4307, 4383, 4398, 4409, 4585, 4635, 4656
    ] := by nativeDecideFin!
