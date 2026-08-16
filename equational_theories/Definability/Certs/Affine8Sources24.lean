import equational_theories.Definability.Certificates

/-!
# Definability certificate sources: `Magma.affine8` (part 25 of 26)

For each of the following magmas, drawn from the `8` magmas on `Fin 8` with all of `AGL(1, 8)` as automorphisms, the equations in at most four variables
that it satisfies. Every one of the `2101` such equations with a model in the family appears
in at least one of these lists, so they are exactly the equations in at most four variables that
can be used as the *source* `L'` of a `Magma.affine8` certificate.

This file is generated; see the module docstring of `Definability.Certificates`.
-/

set_option maxHeartbeats 1000000

/-- `60` of the `101` equations satisfied by `Magma.affine8 6` (part 1 of 2). -/
theorem affine8_satisfies_6_0 :
    Satisfies (Magma.affine8 6) [
      1, 3, 8, 23, 47, 63, 99, 118, 151, 159, 203, 222, 255, 274, 307, 326, 359, 375, 411, 427,
      467, 503, 614, 633, 667, 706, 817, 825, 870, 883, 898, 1020, 1039, 1086, 1119, 1223, 1242,
      1279, 1312, 1426, 1451, 1489, 1516, 1629, 1657, 1692, 1722, 1832, 1860, 1898, 1922, 2035,
      2043, 2088, 2101, 2116, 2238, 2244, 2293, 2304
    ] := by decide!

/-- `41` of the `101` equations satisfied by `Magma.affine8 6` (part 2 of 2). -/
theorem affine8_satisfies_6_1 :
    Satisfies (Magma.affine8 6) [
      2316, 2441, 2447, 2497, 2506, 2644, 2669, 2710, 2737, 2847, 2853, 2903, 2912, 3050, 3076,
      3115, 3143, 3253, 3269, 3319, 3355, 3456, 3475, 3522, 3555, 3659, 3667, 3715, 3722, 3862,
      3881, 3915, 3954, 4065, 4084, 4118, 4157, 4380, 4399, 4435, 4470
    ] := by decide!
