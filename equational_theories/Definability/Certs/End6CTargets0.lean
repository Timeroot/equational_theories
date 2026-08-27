import equational_theories.Definability.ExactEnd6C

/-!
# Term-structural certificate targets: `Magma.end6C`

Equations with no model among the `10` magmas on `Fin 6` whose endomorphism monoid is exactly the
order-`18` monoid of `Magma.endE6C`. `13` of them are worth listing, of which `13` appear here; each
is a valid *target* `L` of a `Magma.end6C` certificate, and so is not term-structural from any of
the `56` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `10` magmas on `Fin 6` whose endomorphism monoid is exactly the order-`18` monoid of
`Magma.endE6C` satisfies any of these `13` equations. -/
theorem end6C_refutes_0 :
    FamilyRefutes Magma.end6C [
      159, 309, 361, 1278, 1431, 2040, 2254, 3315, 3464, 3467, 3870, 3873, 4165
    ] := by nativeDecideFin!
