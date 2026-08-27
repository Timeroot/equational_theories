import equational_theories.Definability.ExactEnd6D

/-!
# Term-structural certificate targets: `Magma.end6D`

Equations with no model among the `2` magmas on `Fin 6` whose endomorphism monoid is exactly the
order-`36` monoid of `Magma.endE6D`. `35` of them are worth listing, of which `35` appear here; each
is a valid *target* `L` of a `Magma.end6D` certificate, and so is not term-structural from any of
the `34` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `2` magmas on `Fin 6` whose endomorphism monoid is exactly the order-`36` monoid of
`Magma.endE6D` satisfies any of these `35` equations. -/
theorem end6D_refutes_0 :
    FamilyRefutes Magma.end6D [
      105, 221, 836, 879, 1036, 1249, 1442, 1444, 1451, 1635, 1657, 1860, 1894, 2043, 2053, 2090,
      2303, 2496, 2650, 2736, 3308, 3316, 3322, 3462, 3511, 3519, 3525, 3880, 3925, 3935, 3955,
      4128, 4138, 4158, 4435
    ] := by nativeDecideFin!
