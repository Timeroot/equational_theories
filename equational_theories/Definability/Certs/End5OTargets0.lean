import equational_theories.Definability.ExactEnd5O

/-!
# Term-structural certificate targets: `Magma.end5O`

Equations with no model among the `180` magmas on `Fin 5` whose endomorphism monoid is exactly the
order-`9` monoid of `Magma.endE5O`. `8` of them are worth listing, of which `8` appear here; each is
a valid *target* `L` of a `Magma.end5O` certificate, and so is not term-structural from any of the
`21` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `180` magmas on `Fin 5` whose endomorphism monoid is exactly the order-`9` monoid of
`Magma.endE5O` satisfies any of these `8` equations. -/
theorem end5O_refutes_0 :
    FamilyRefutes Magma.end5O [
      3309, 3529, 3533, 3921, 3931, 4121, 4284, 4599
    ] := by nativeDecideFin!
