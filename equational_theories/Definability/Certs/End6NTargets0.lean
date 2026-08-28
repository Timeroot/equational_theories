import equational_theories.Definability.ExactEnd6N

/-!
# Term-structural certificate targets: `Magma.end6N`

Equations with no model among the `22` magmas on `Fin 6` whose endomorphism monoid is exactly the
order-`384` monoid of `Magma.endE6N`. `69` of them are worth listing, of which `69` appear here;
each is a valid *target* `L` of a `Magma.end6N` certificate, and so is not term-structural from any
of the `41` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `22` magmas on `Fin 6` whose endomorphism monoid is exactly the order-`384` monoid
of `Magma.endE6N` satisfies any of these `69` equations. -/
theorem end6N_refutes_0 :
    FamilyRefutes Magma.end6N [
      10, 25, 101, 110, 159, 208, 214, 413, 416, 419, 426, 429, 432, 439, 1031, 1051, 1055, 1059,
      1067, 1234, 1244, 1262, 1266, 1270, 1431, 1434, 1437, 1441, 1444, 1451, 1454, 1630, 1632,
      1633, 1681, 1691, 1833, 1838, 1884, 1921, 1958, 2037, 2040, 2043, 2053, 2060, 2063, 2070,
      2259, 2269, 2273, 2277, 2285, 2452, 2476, 2480, 2484, 2488, 3052, 3055, 3065, 3068, 3071,
      3075, 3078, 3525, 3529, 3931, 3935
    ] := by nativeDecideFin!
