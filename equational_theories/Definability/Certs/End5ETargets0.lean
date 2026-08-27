import equational_theories.Definability.ExactEnd5E

/-!
# Term-structural certificate targets: `Magma.end5E`

Equations with no model among the `6` magmas on `Fin 5` whose endomorphism monoid is exactly the
order-`25` monoid of `Magma.endE5E`. `17` of them are worth listing, of which `17` appear here; each
is a valid *target* `L` of a `Magma.end5E` certificate, and so is not term-structural from any of
the `150` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `6` magmas on `Fin 5` whose endomorphism monoid is exactly the order-`25` monoid of
`Magma.endE5E` satisfies any of these `17` equations. -/
theorem end5E_refutes_0 :
    FamilyRefutes Magma.end5E [
      43, 1241, 2256, 3308, 3556, 3667, 3675, 3703, 3924, 4158, 4283, 4358, 4405, 4435, 4531,
      4635, 4677
    ] := by nativeDecideFin!
