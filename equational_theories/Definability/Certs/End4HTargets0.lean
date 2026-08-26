import equational_theories.Definability.ExactEnd4H

/-!
# Term-structural certificate targets: `Magma.end4H`

Equations with no model among the `56` magmas on `Fin 4` whose endomorphism monoid is exactly the
order-`4` monoid of `Magma.endE4H`. `52` of them are worth listing, of which `52` appear here; each
is a valid *target* `L` of a `Magma.end4H` certificate, and so is not term-structural from any of
the `36` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd4`.
-/

set_option maxHeartbeats 1000000

/-- None of the `56` magmas on `Fin 4` whose endomorphism monoid is exactly the order-`4` monoid of
`Magma.endE4H` satisfies any of these `52` equations. -/
theorem end4H_refutes_0 :
    FamilyRefutes Magma.end4H [
      10, 25, 107, 110, 211, 214, 413, 416, 422, 426, 432, 439, 1038, 1041, 1048, 1051, 1059,
      1063, 1067, 1241, 1244, 1251, 1254, 1262, 1266, 1270, 1441, 1444, 2037, 2053, 2256, 2259,
      2266, 2269, 2277, 2281, 2285, 2459, 2462, 2469, 2472, 2480, 2484, 2488, 3052, 3055, 3065,
      3071, 3078, 3085, 3533, 3921
    ] := by nativeDecideFin!
