import equational_theories.Definability.ExactEnd6AE

/-!
# Term-structural certificate targets: `Magma.end6AE`

Equations with no model among the `2` magmas on `Fin 6` whose endomorphism monoid is exactly the
order-`58` monoid of `Magma.endE6AE`. `20` of them are worth listing, of which `20` appear here;
each is a valid *target* `L` of a `Magma.end6AE` certificate, and so is not term-structural from any
of the `14` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `2` magmas on `Fin 6` whose endomorphism monoid is exactly the order-`58` monoid of
`Magma.endE6AE` satisfies any of these `20` equations. -/
theorem end6AE_refutes_0 :
    FamilyRefutes Magma.end6AE [
      1060, 1229, 1230, 2300, 2310, 2554, 3255, 3279, 3458, 3482, 3867, 3881, 4070, 4084, 4269,
      4314, 4321, 4584, 4606, 4636
    ] := by nativeDecideFin!
