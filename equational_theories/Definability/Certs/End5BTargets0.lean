import equational_theories.Definability.ExactEnd5B

/-!
# Term-structural certificate targets: `Magma.end5B`

Equations with no model among the `16` magmas on `Fin 5` whose endomorphism monoid is exactly the
order-`15` monoid of `Magma.endE5B`. `59` of them are worth listing, of which `59` appear here; each
is a valid *target* `L` of a `Magma.end5B` certificate, and so is not term-structural from any of
the `68` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `16` magmas on `Fin 5` whose endomorphism monoid is exactly the order-`15` monoid of
`Magma.endE5B` satisfies any of these `59` equations. -/
theorem end5B_refutes_0 :
    FamilyRefutes Magma.end5B [
      16, 26, 326, 375, 422, 429, 436, 466, 500, 513, 528, 575, 1075, 1122, 1184, 1434, 1647,
      1654, 1658, 1662, 1731, 1780, 1840, 1850, 1861, 1873, 1934, 1949, 2060, 2457, 2470, 2485,
      3053, 3058, 3066, 3068, 3079, 3083, 3085, 3094, 3261, 3278, 3306, 3318, 3320, 3334, 3414,
      3533, 3921, 4068, 4073, 4131, 4146, 4155, 4192, 4275, 4307, 4585, 4656
    ] := by nativeDecideFin!
