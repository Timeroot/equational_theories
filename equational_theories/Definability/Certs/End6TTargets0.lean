import equational_theories.Definability.ExactEnd6T

/-!
# Term-structural certificate targets: `Magma.end6T`

Equations with no model among the `4` magmas on `Fin 6` whose endomorphism monoid is exactly the
order-`28` monoid of `Magma.endE6T`. `38` of them are worth listing, of which `38` appear here; each
is a valid *target* `L` of a `Magma.end6T` certificate, and so is not term-structural from any of
the `50` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `4` magmas on `Fin 6` whose endomorphism monoid is exactly the order-`28` monoid of
`Magma.endE6T` satisfies any of these `38` equations. -/
theorem end6T_refutes_0 :
    FamilyRefutes Magma.end6T [
      101, 104, 205, 208, 419, 822, 1023, 1025, 1028, 1035, 1055, 1225, 1228, 1248, 1258, 1631,
      1634, 1647, 1654, 1837, 1840, 1847, 1850, 2243, 2246, 2249, 2253, 2443, 2446, 2452, 2466,
      2530, 2649, 3075, 3306, 3458, 3867, 4131
    ] := by nativeDecideFin!
