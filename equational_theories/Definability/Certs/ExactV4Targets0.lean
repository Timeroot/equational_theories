import equational_theories.Definability.ExactAut4V4

/-!
# Structural certificate targets: `Magma.exactV4` (part 1 of 1)

Equations with no model among the `240` magmas on `Fin 4` whose automorphism group is exactly the
order-`4` group of `Magma.permEV4`. `52` of them are worth listing, of which `52` appear here; each
is a valid *target* `L` of a `Magma.exactV4` certificate, and so is not structural from any of the
`8` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactAut4`.
-/

set_option maxHeartbeats 1000000

/-- None of the `240` magmas on `Fin 4` whose automorphism group is exactly the order-`4` group of
`Magma.permEV4` satisfies any of these `52` equations. -/
theorem exactV4_refutes_0 :
    FamilyRefutes Magma.exactV4 [
      105, 221, 427, 430, 433, 676, 716, 833, 834, 836, 837, 839, 843, 854, 919, 1036, 1239,
      1242, 1249, 1259, 1260, 1481, 1528, 2051, 2064, 2293, 2303, 2306, 2314, 2330, 2496, 2673,
      2699, 2702, 2709, 2712, 2736, 2774, 2778, 2853, 2876, 3105, 3142, 3180, 3670, 3718, 3736,
      3740, 4401, 4402, 4452, 4476
    ] := by nativeDecideFin!
