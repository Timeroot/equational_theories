import equational_theories.Definability.ExactAut5C45

/-!
# Structural certificate targets: `Magma.exactC45` (part 5 of 60)

Equations with no model among the `15214` magmas on `Fin 5` whose automorphism group is exactly the
order-`4` group of `Magma.permEC45`. `873` of them are worth listing, of which `23` appear here;
each is a valid *target* `L` of a `Magma.exactC45` certificate, and so is not structural from any of
the `137` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactAut5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `15214` magmas on `Fin 5` whose automorphism group is exactly the order-`4` group of
`Magma.permEC45` satisfies any of these `23` equations. -/
theorem exactC45_refutes_4 :
    FamilyRefutes Magma.exactC45 [
      3378, 3379, 3380, 3381, 3382, 3383, 3384, 3385, 3386, 3387, 3389, 3390, 3391, 3392, 3393,
      3394, 3395, 3396, 3397, 3399, 3400, 3401, 3402
    ] := by nativeDecideFin!
