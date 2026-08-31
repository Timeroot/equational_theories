import equational_theories.Definability.ExactEnd5V

/-!
# Term-structural certificate targets: `Magma.end5V`

Equations with no model among the `16` magmas on `Fin 5` whose endomorphism monoid is exactly the
order-`29` monoid of `Magma.endE5V`. `22` of them are worth listing, of which `22` appear here; each
is a valid *target* `L` of a `Magma.end5V` certificate, and so is not term-structural from any of
the `25` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `16` magmas on `Fin 5` whose endomorphism monoid is exactly the order-`29` monoid of
`Magma.endE5V` satisfies any of these `22` equations. -/
theorem end5V_refutes_0 :
    FamilyRefutes Magma.end5V [
      326, 375, 3309, 3315, 3319, 3346, 3509, 3521, 3522, 3525, 3546, 3915, 3927, 3928, 3935,
      3952, 4118, 4120, 4121, 4165, 4362, 4673
    ] := by nativeDecideFin!
