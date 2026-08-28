import equational_theories.Definability.ExactEnd6AB

/-!
# Term-structural certificate targets: `Magma.end6AB`

Equations with no model among the `1` magmas on `Fin 6` whose endomorphism monoid is exactly the
order-`68` monoid of `Magma.endE6AB`. `14` of them are worth listing, of which `14` appear here;
each is a valid *target* `L` of a `Magma.end6AB` certificate, and so is not term-structural from any
of the `14` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `1` magmas on `Fin 6` whose endomorphism monoid is exactly the order-`68` monoid of
`Magma.endE6AB` satisfies any of these `14` equations. -/
theorem end6AB_refutes_0 :
    FamilyRefutes Magma.end6AB [
      1045, 1231, 2263, 2449, 3261, 3269, 3297, 3459, 3481, 3865, 3887, 4073, 4081, 4109
    ] := by nativeDecideFin!
