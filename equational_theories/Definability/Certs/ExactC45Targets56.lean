import equational_theories.Definability.ExactAut5C45

/-!
# Structural certificate targets: `Magma.exactC45` (part 57 of 60)

Equations with no model among the `15214` magmas on `Fin 5` whose automorphism group is exactly the
order-`4` group of `Magma.permEC45`. `873` of them are worth listing, of which `19` appear here;
each is a valid *target* `L` of a `Magma.exactC45` certificate, and so is not structural from any of
the `137` source equations, not even over finite carriers.

This file is generated; see the module docstring of `Definability.ExactAut5`.
-/

set_option maxHeartbeats 1000000

/-- None of the `15214` magmas on `Fin 5` whose automorphism group is exactly the order-`4` group of
`Magma.permEC45` satisfies any of these `19` equations. -/
theorem exactC45_refutes_56 :
    FamilyRefutes Magma.exactC45 [
      4589, 4596, 4607, 4610, 4613, 4617, 4618, 4621, 4624, 4628, 4637, 4641, 4643, 4644, 4648,
      4650, 4653, 4659, 4660
    ] := by nativeDecideFin!
