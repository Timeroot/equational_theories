import equational_theories.Definability.ExactEnd6M

/-!
# Term-structural certificate targets: `Magma.end6M`

Equations with no model among the `2` magmas on `Fin 6` whose endomorphism monoid is exactly the
order-`141` monoid of `Magma.endE6M`. `62` of them are worth listing, of which `62` appear here;
each is a valid *target* `L` of a `Magma.end6M` certificate, and so is not term-structural from any
of the `30` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `2` magmas on `Fin 6` whose endomorphism monoid is exactly the order-`141` monoid of
`Magma.endE6M` satisfies any of these `62` equations. -/
theorem end6M_refutes_0 :
    FamilyRefutes Magma.end6M [
      8, 10, 23, 25, 99, 101, 104, 107, 203, 205, 208, 211, 323, 378, 411, 429, 436, 1020, 1022,
      1025, 1028, 1035, 1038, 1045, 1055, 1223, 1225, 1228, 1231, 1238, 1241, 1248, 1258, 2238,
      2240, 2243, 2246, 2249, 2253, 2256, 2263, 2441, 2443, 2446, 2449, 2452, 2456, 2459, 2466,
      3050, 3058, 3068, 3509, 3519, 3522, 3525, 3537, 3915, 3925, 3928, 3935, 3943
    ] := by nativeDecideFin!
