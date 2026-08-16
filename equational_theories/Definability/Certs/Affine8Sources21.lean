import equational_theories.Definability.Certificates

/-!
# Definability certificate sources: `Magma.affine8` (part 22 of 26)

For each of the following magmas, drawn from the `8` magmas on `Fin 8` with all of `AGL(1, 8)` as automorphisms, the equations in at most four variables
that it satisfies. Every one of the `2101` such equations with a model in the family appears
in at least one of these lists, so they are exactly the equations in at most four variables that
can be used as the *source* `L'` of a `Magma.affine8` certificate.

This file is generated; see the module docstring of `Definability.Certificates`.
-/

set_option maxHeartbeats 1000000

/-- `60` of the `101` equations satisfied by `Magma.affine8 3` (part 1 of 2). -/
theorem affine8_satisfies_3_0 :
    Satisfies (Magma.affine8 3) [
      1, 3, 8, 23, 47, 73, 99, 125, 151, 159, 203, 229, 255, 271, 307, 326, 359, 375, 411, 437,
      476, 504, 614, 640, 676, 704, 817, 825, 910, 917, 1020, 1046, 1082, 1110, 1223, 1239, 1285,
      1323, 1368, 1426, 1451, 1479, 1526, 1587, 1629, 1657, 1685, 1729, 1832, 1860, 1895, 1925,
      2035, 2043, 2091, 2098, 2238, 2241, 2328, 2330
    ] := by decide!

/-- `41` of the `101` equations satisfied by `Magma.affine8 3` (part 2 of 2). -/
theorem affine8_satisfies_3_1 :
    Satisfies (Magma.affine8 3) [
      2441, 2450, 2533, 2541, 2644, 2669, 2697, 2744, 2805, 2847, 2866, 2900, 2939, 3050, 3069,
      3105, 3140, 3253, 3279, 3319, 3345, 3456, 3482, 3522, 3548, 3659, 3667, 3715, 3722, 3862,
      3888, 3915, 3961, 4065, 4081, 4118, 4154, 4380, 4399, 4435, 4470
    ] := by decide!
