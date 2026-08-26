import equational_theories.Definability.ExactEnd4J

/-!
# Term-structural certificate targets: `Magma.end4J`

Equations with no model among the `2` magmas on `Fin 4` whose endomorphism monoid is exactly the
order-`10` monoid of `Magma.endE4J`. `18` of them are worth listing, of which `18` appear here; each
is a valid *target* `L` of a `Magma.end4J` certificate, and so is not term-structural from any of
the `21` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd4`.
-/

set_option maxHeartbeats 1000000

/-- None of the `2` magmas on `Fin 4` whose endomorphism monoid is exactly the order-`10` monoid of
`Magma.endE4J` satisfies any of these `18` equations. -/
theorem end4J_refutes_0 :
    FamilyRefutes Magma.end4J [
      49, 260, 413, 416, 622, 819, 1428, 2050, 2659, 2872, 3055, 3065, 3255, 3322, 3512, 3918,
      4070, 4138
    ] := by nativeDecideFin!
