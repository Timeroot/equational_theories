import equational_theories.Definability.ExactEnd4F

/-!
# Term-structural certificate targets: `Magma.end4F`

Equations with no model among the `9` magmas on `Fin 4` whose endomorphism monoid is exactly the
order-`7` monoid of `Magma.endE4F`. `87` of them are worth listing, of which `87` appear here; each
is a valid *target* `L` of a `Magma.end4F` certificate, and so is not term-structural from any of
the `163` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd4`.
-/

set_option maxHeartbeats 1000000

/-- None of the `9` magmas on `Fin 4` whose endomorphism monoid is exactly the order-`7` monoid of
`Magma.endE4F` satisfies any of these `87` equations. -/
theorem end4F_refutes_0 :
    FamilyRefutes Magma.end4F [
      10, 25, 101, 105, 110, 208, 214, 221, 326, 375, 413, 417, 426, 432, 620, 825, 1022, 1026,
      1031, 1035, 1041, 1046, 1048, 1051, 1055, 1059, 1063, 1234, 1243, 1244, 1262, 1266, 1444,
      1631, 1644, 1650, 1834, 1847, 1853, 2053, 2259, 2269, 2273, 2277, 2372, 2443, 2452, 2456,
      2462, 2469, 2472, 2476, 2480, 2484, 2503, 2506, 2669, 2909, 3052, 3065, 3071, 3112, 3318,
      3322, 3346, 3463, 3521, 3525, 3529, 3714, 3748, 3752, 3756, 3761, 3823, 3883, 3931, 3935,
      3952, 4120, 4138, 4155, 4286, 4291, 4438, 4629, 4642
    ] := by nativeDecideFin!
