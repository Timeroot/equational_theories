import equational_theories.Definability.ExactEnd5L

/-!
# Term-structural certificate targets: `Magma.end5L`

Equations with no model among the `4` magmas on `Fin 5` whose endomorphism monoid is exactly the
order-`13` monoid of `Magma.endE5L`. `6` of them are worth listing, of which `6` appear here; each
is a valid *target* `L` of a `Magma.end5L` certificate, and so is not term-structural from any of
the `49` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `4` magmas on `Fin 5` whose endomorphism monoid is exactly the order-`13` monoid of
`Magma.endE5L` satisfies any of these `6` equations. -/
theorem end5L_refutes_0 :
    FamilyRefutes Magma.end5L [
      1647, 1850, 3316, 4128, 4362, 4673
    ] := by nativeDecideFin!
