import equational_theories.Definability.ExactEnd4L

/-!
# Term-structural certificate targets: `Magma.end4L`

Equations with no model among the `2` magmas on `Fin 4` whose endomorphism monoid is exactly the
order-`16` monoid of `Magma.endE4L`. `25` of them are worth listing, of which `25` appear here; each
is a valid *target* `L` of a `Magma.end4L` certificate, and so is not term-structural from any of
the `33` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd4`.
-/

set_option maxHeartbeats 1000000

/-- None of the `2` magmas on `Fin 4` whose endomorphism monoid is exactly the order-`16` monoid of
`Magma.endE4L` satisfies any of these `25` equations. -/
theorem end4L_refutes_0 :
    FamilyRefutes Magma.end4L [
      436, 466, 500, 513, 838, 1075, 1325, 1434, 1455, 2060, 2137, 2267, 2457, 2665, 3053, 3058,
      3066, 3079, 3261, 3518, 3962, 4073, 4275, 4435, 4585
    ] := by nativeDecideFin!
