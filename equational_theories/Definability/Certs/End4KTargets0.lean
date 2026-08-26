import equational_theories.Definability.ExactEnd4K

/-!
# Term-structural certificate targets: `Magma.end4K`

Equations with no model among the `6` magmas on `Fin 4` whose endomorphism monoid is exactly the
order-`8` monoid of `Magma.endE4K`. `32` of them are worth listing, of which `32` appear here; each
is a valid *target* `L` of a `Magma.end4K` certificate, and so is not term-structural from any of
the `15` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactEnd4`.
-/

set_option maxHeartbeats 1000000

/-- None of the `6` magmas on `Fin 4` whose endomorphism monoid is exactly the order-`8` monoid of
`Magma.endE4K` satisfies any of these `32` equations. -/
theorem end4K_refutes_0 :
    FamilyRefutes Magma.end4K [
      466, 500, 513, 1075, 1325, 1455, 1635, 1684, 1691, 1838, 1848, 1894, 2137, 2267, 2457,
      3053, 3066, 3079, 3318, 3353, 3518, 3962, 4127, 4155, 4275, 4283, 4291, 4320, 4585, 4598,
      4629, 4635
    ] := by nativeDecideFin!
