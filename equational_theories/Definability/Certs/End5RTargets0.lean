import equational_theories.Definability.ExactEnd5R

/-!
# Term-structural certificate targets: `Magma.end5R`

Equations with no model among the `76` magmas on `Fin 5` whose endomorphism monoid is exactly the
order-`17` monoid of `Magma.endE5R`. `2` of them are worth listing, of which `2` appear here; each
is a valid *target* `L` of a `Magma.end5R` certificate, and so is not term-structural from any of
the `13` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `76` magmas on `Fin 5` whose endomorphism monoid is exactly the order-`17` monoid of
`Magma.endE5R` satisfies any of these `2` equations. -/
theorem end5R_refutes_0 :
    FamilyRefutes Magma.end5R [
      1026, 2503
    ] := by nativeDecideFin!
