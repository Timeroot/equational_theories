import equational_theories.Definability.ExactAut5D65

/-!
# Structural certificate targets: `Magma.exactD65` (part 1 of 1)

Equations with no model among the `106` magmas on `Fin 5` whose automorphism group is exactly the
order-`12` group of `Magma.permED65`. `21` of them are worth listing, of which `21` appear here;
each is a valid *target* `L` of a `Magma.exactD65` certificate, and so is not structural from any of
the `3` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactAut5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `106` magmas on `Fin 5` whose automorphism group is exactly the order-`12` group of
`Magma.permED65` satisfies any of these `21` equations. -/
theorem exactD65_refutes_0 :
    FamilyRefutes Magma.exactD65 [
      427, 433, 716, 833, 834, 839, 854, 919, 1260, 1528, 2064, 2306, 2673, 2699, 2702, 2712,
      2774, 2876, 3105, 3180, 4401
    ] := by nativeDecideFin!
