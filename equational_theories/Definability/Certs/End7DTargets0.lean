import equational_theories.Definability.ExactEnd7D

/-!
# Term-structural certificate targets: `Magma.end7D`

Equations with no model among the `8` magmas on `Fin 7` whose endomorphism monoid is exactly the
order-`351` monoid of `Magma.endE7D`. `20` of them are worth listing, of which `20` appear here;
each is a valid *target* `L` of a `Magma.end7D` certificate, and so is not term-structural from any
of the `10` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd7`.
-/

set_option maxHeartbeats 1000000

/-- None of the `8` magmas on `Fin 7` whose endomorphism monoid is exactly the order-`351` monoid of
`Magma.endE7D` satisfies any of these `20` equations. -/
theorem end7D_refutes_0 :
    FamilyRefutes Magma.end7D [
      419, 1022, 1231, 1241, 1650, 1853, 2256, 2263, 2456, 3075, 3322, 3461, 3519, 3864, 3925,
      4138, 4269, 4316, 4584, 4631
    ] := by nativeDecideFin!
