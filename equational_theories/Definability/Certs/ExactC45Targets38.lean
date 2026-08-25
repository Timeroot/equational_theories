import equational_theories.Definability.ExactAut5C45

/-!
# Structural certificate targets: `Magma.exactC45` (part 39 of 60)

Equations with no model among the `15214` magmas on `Fin 5` whose automorphism group is exactly the
order-`4` group of `Magma.permEC45`. `873` of them are worth listing, of which `21` appear here;
each is a valid *target* `L` of a `Magma.exactC45` certificate, and so is not structural from any of
the `137` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactAut5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `15214` magmas on `Fin 5` whose automorphism group is exactly the order-`4` group of
`Magma.permEC45` satisfies any of these `21` equations. -/
theorem exactC45_refutes_38 :
    FamilyRefutes Magma.exactC45 [
      4194, 4195, 4197, 4198, 4199, 4201, 4202, 4203, 4205, 4206, 4207, 4208, 4211, 4212, 4214,
      4215, 4218, 4219, 4220, 4222, 4223
    ] := by nativeDecideFin!
