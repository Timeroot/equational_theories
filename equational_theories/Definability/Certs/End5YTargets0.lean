import equational_theories.Definability.ExactEnd5Y

/-!
# Term-structural certificate targets: `Magma.end5Y`

Equations with no model among the `15` magmas on `Fin 5` whose endomorphism monoid is exactly the
order-`10` monoid of `Magma.endE5Y`. `10` of them are worth listing, of which `10` appear here; each
is a valid *target* `L` of a `Magma.end5Y` certificate, and so is not term-structural from any of
the `1` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `15` magmas on `Fin 5` whose endomorphism monoid is exactly the order-`10` monoid of
`Magma.endE5Y` satisfies any of these `10` equations. -/
theorem end5Y_refutes_0 :
    FamilyRefutes Magma.end5Y [
      3353, 3518, 3556, 3714, 3748, 3752, 3761, 3924, 3962, 4127
    ] := by nativeDecideFin!
