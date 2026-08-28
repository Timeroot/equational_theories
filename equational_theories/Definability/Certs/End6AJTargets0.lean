import equational_theories.Definability.ExactEnd6AJ

/-!
# Term-structural certificate targets: `Magma.end6AJ`

Equations with no model among the `14` magmas on `Fin 6` whose endomorphism monoid is exactly the
order-`48` monoid of `Magma.endE6AJ`. `17` of them are worth listing, of which `17` appear here;
each is a valid *target* `L` of a `Magma.end6AJ` certificate, and so is not term-structural from any
of the `2` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `14` magmas on `Fin 6` whose endomorphism monoid is exactly the order-`48` monoid of
`Magma.endE6AJ` satisfies any of these `17` equations. -/
theorem end6AJ_refutes_0 :
    FamilyRefutes Magma.end6AJ [
      325, 385, 3308, 3318, 3518, 3556, 3924, 3962, 4155, 4158, 4320, 4362, 4406, 4435, 4436,
      4598, 4673
    ] := by nativeDecideFin!
