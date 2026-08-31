import equational_theories.Definability.ExactEnd5X

/-!
# Term-structural certificate targets: `Magma.end5X`

Equations with no model among the `12` magmas on `Fin 5` whose endomorphism monoid is exactly the
order-`28` monoid of `Magma.endE5X`. `23` of them are worth listing, of which `23` appear here; each
is a valid *target* `L` of a `Magma.end5X` certificate, and so is not term-structural from any of
the `8` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `12` magmas on `Fin 5` whose endomorphism monoid is exactly the order-`28` monoid of
`Magma.endE5X` satisfies any of these `23` equations. -/
theorem end5X_refutes_0 :
    FamilyRefutes Magma.end5X [
      3315, 3319, 3342, 3462, 3509, 3522, 3545, 3880, 3915, 3928, 3964, 4118, 4165, 4167, 4275,
      4307, 4383, 4386, 4409, 4446, 4458, 4585, 4656
    ] := by nativeDecideFin!
