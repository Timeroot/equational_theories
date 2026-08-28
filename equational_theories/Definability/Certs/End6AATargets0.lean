import equational_theories.Definability.ExactEnd6AA

/-!
# Term-structural certificate targets: `Magma.end6AA`

Equations with no model among the `12` magmas on `Fin 6` whose endomorphism monoid is exactly the
order-`29` monoid of `Magma.endE6AA`. `20` of them are worth listing, of which `20` appear here;
each is a valid *target* `L` of a `Magma.end6AA` certificate, and so is not term-structural from any
of the `38` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000

/-- None of the `12` magmas on `Fin 6` whose endomorphism monoid is exactly the order-`29` monoid of
`Magma.endE6AA` satisfies any of these `20` equations. -/
theorem end6AA_refutes_0 :
    FamilyRefutes Magma.end6AA [
      310, 367, 3258, 3266, 3660, 3661, 3664, 3674, 4067, 4096, 4272, 4318, 4320, 4343, 4351,
      4583, 4597, 4598, 4608, 4611
    ] := by nativeDecideFin!
