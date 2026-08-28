import equational_theories.Definability.ExactEnd6AM

/-!
# Term-structural certificate targets: `Magma.end6AM`

Equations with no model among the `6` magmas on `Fin 6` whose endomorphism monoid is exactly the
order-`20` monoid of `Magma.endE6AM`. `10` of them are worth listing, of which `10` appear here;
each is a valid *target* `L` of a `Magma.end6AM` certificate, and so is not term-structural from any
of the `18` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `6` magmas on `Fin 6` whose endomorphism monoid is exactly the order-`20` monoid of
`Magma.endE6AM` satisfies any of these `10` equations. -/
theorem end6AM_refutes_0 :
    FamilyRefutes Magma.end6AM [
      1631, 1847, 3519, 3525, 3526, 3925, 3935, 4023, 4314, 4606
    ] := by nativeDecideFin!
