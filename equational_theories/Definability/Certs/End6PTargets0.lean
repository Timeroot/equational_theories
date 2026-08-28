import equational_theories.Definability.ExactEnd6P

/-!
# Term-structural certificate targets: `Magma.end6P`

Equations with no model among the `4` magmas on `Fin 6` whose endomorphism monoid is exactly the
order-`114` monoid of `Magma.endE6P`. `4` of them are worth listing, of which `4` appear here; each
is a valid *target* `L` of a `Magma.end6P` certificate, and so is not term-structural from any of
the `52` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `4` magmas on `Fin 6` whose endomorphism monoid is exactly the order-`114` monoid of
`Magma.endE6P` satisfies any of these `4` equations. -/
theorem end6P_refutes_0 :
    FamilyRefutes Magma.end6P [
      3666, 3671, 3680, 3698
    ] := by nativeDecideFin!
