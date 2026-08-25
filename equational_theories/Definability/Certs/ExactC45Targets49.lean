import equational_theories.Definability.ExactAut5C45

/-!
# Structural certificate targets: `Magma.exactC45` (part 50 of 60)

Equations with no model among the `15214` magmas on `Fin 5` whose automorphism group is exactly the
order-`4` group of `Magma.permEC45`. `873` of them are worth listing, of which `21` appear here;
each is a valid *target* `L` of a `Magma.exactC45` certificate, and so is not structural from any of
the `137` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactAut5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `15214` magmas on `Fin 5` whose automorphism group is exactly the order-`4` group of
`Magma.permEC45` satisfies any of these `21` equations. -/
theorem exactC45_refutes_49 :
    FamilyRefutes Magma.exactC45 [
      4468, 4474, 4476, 4478, 4481, 4485, 4488, 4492, 4493, 4496, 4501, 4502, 4505, 4506, 4508,
      4509, 4511, 4513, 4514, 4516, 4517
    ] := by nativeDecideFin!
