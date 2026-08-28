import equational_theories.Definability.ExactEnd6AI

/-!
# Term-structural certificate targets: `Magma.end6AI`

Equations with no model among the `2` magmas on `Fin 6` whose endomorphism monoid is exactly the
order-`420` monoid of `Magma.endE6AI`. `14` of them are worth listing, of which `14` appear here;
each is a valid *target* `L` of a `Magma.end6AI` certificate, and so is not term-structural from any
of the `10` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `2` magmas on `Fin 6` whose endomorphism monoid is exactly the order-`420` monoid of
`Magma.endE6AI` satisfies any of these `14` equations. -/
theorem end6AI_refutes_0 :
    FamilyRefutes Magma.end6AI [
      310, 367, 3259, 3262, 3266, 3459, 3668, 3672, 3687, 3690, 3887, 4083, 4093, 4096
    ] := by nativeDecideFin!
