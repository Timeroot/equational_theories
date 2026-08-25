import equational_theories.Definability.ExactAut5C45

/-!
# Structural certificate targets: `Magma.exactC45` (part 4 of 60)

Equations with no model among the `15214` magmas on `Fin 5` whose automorphism group is exactly the
order-`4` group of `Magma.permEC45`. `873` of them are worth listing, of which `27` appear here;
each is a valid *target* `L` of a `Magma.exactC45` certificate, and so is not structural from any of
the `137` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactAut5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `15214` magmas on `Fin 5` whose automorphism group is exactly the order-`4` group of
`Magma.permEC45` satisfies any of these `27` equations. -/
theorem exactC45_refutes_3 :
    FamilyRefutes Magma.exactC45 [
      3304, 3344, 3347, 3348, 3349, 3351, 3354, 3356, 3357, 3358, 3359, 3360, 3361, 3362, 3363,
      3365, 3366, 3367, 3368, 3369, 3371, 3372, 3373, 3374, 3375, 3376, 3377
    ] := by nativeDecideFin!
