import equational_theories.Definability.ExactEnd3X

/-!
# Term-structural certificate targets: `Magma.end3X`

Equations with no model among the `15` magmas on `Fin 3` whose endomorphism monoid is exactly the
order-`4` monoid of `Magma.endE3X`. `2` of them are worth listing, of which `2` appear here; each is
a valid *target* `L` of a `Magma.end3X` certificate, and so is not term-structural from any of the
`2` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd3`.
-/

set_option maxHeartbeats 1000000

/-- None of the `15` magmas on `Fin 3` whose endomorphism monoid is exactly the order-`4` monoid of
`Magma.endE3X` satisfies any of these `2` equations. -/
theorem end3X_refutes_0 :
    FamilyRefutes Magma.end3X [
      4284, 4599
    ] := by nativeDecideFin!
