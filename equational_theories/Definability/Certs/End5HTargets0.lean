import equational_theories.Definability.ExactEnd5H

/-!
# Term-structural certificate targets: `Magma.end5H`

Equations with no model among the `4` magmas on `Fin 5` whose endomorphism monoid is exactly the
order-`19` monoid of `Magma.endE5H`. `43` of them are worth listing, of which `43` appear here; each
is a valid *target* `L` of a `Magma.end5H` certificate, and so is not term-structural from any of
the `126` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `4` magmas on `Fin 5` whose endomorphism monoid is exactly the order-`19` monoid of
`Magma.endE5H` satisfies any of these `43` equations. -/
theorem end5H_refutes_0 :
    FamilyRefutes Magma.end5H [
      127, 160, 179, 212, 429, 436, 466, 1075, 1288, 1325, 1370, 1454, 1455, 1456, 1457, 1731,
      1861, 2063, 2078, 2137, 2203, 2264, 2267, 2270, 2457, 3058, 3066, 3068, 3278, 3316, 3322,
      3519, 3521, 3525, 3925, 3935, 3952, 4068, 4128, 4138, 4314, 4435, 4606
    ] := by nativeDecideFin!
