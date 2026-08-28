import equational_theories.Definability.ExactEnd6Y

/-!
# Term-structural certificate targets: `Magma.end6Y`

Equations with no model among the `2` magmas on `Fin 6` whose endomorphism monoid is exactly the
order-`26` monoid of `Magma.endE6Y`. `8` of them are worth listing, of which `8` appear here; each
is a valid *target* `L` of a `Magma.end6Y` certificate, and so is not term-structural from any of
the `55` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `2` magmas on `Fin 6` whose endomorphism monoid is exactly the order-`26` monoid of
`Magma.endE6Y` satisfies any of these `8` equations. -/
theorem end6Y_refutes_0 :
    FamilyRefutes Magma.end6Y [
      309, 361, 1428, 2050, 3461, 3464, 3864, 3870
    ] := by nativeDecideFin!
