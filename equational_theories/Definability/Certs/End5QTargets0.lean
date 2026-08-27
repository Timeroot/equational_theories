import equational_theories.Definability.ExactEnd5Q

/-!
# Term-structural certificate targets: `Magma.end5Q`

Equations with no model among the `2` magmas on `Fin 5` whose endomorphism monoid is exactly the
order-`17` monoid of `Magma.endE5Q`. `15` of them are worth listing, of which `15` appear here; each
is a valid *target* `L` of a `Magma.end5Q` certificate, and so is not term-structural from any of
the `8` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `2` magmas on `Fin 5` whose endomorphism monoid is exactly the order-`17` monoid of
`Magma.endE5Q` satisfies any of these `15` equations. -/
theorem end5Q_refutes_0 :
    FamilyRefutes Magma.end5Q [
      427, 439, 442, 833, 1240, 2296, 2699, 3078, 3105, 3318, 3724, 3749, 4155, 4362, 4673
    ] := by nativeDecideFin!
